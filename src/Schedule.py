import os
import datetime
from pysat.formula import CNF
from pysat.solvers import MinisatGH

loc = os.path.dirname(os.path.realpath(__file__))


def daterange(numdays, start_date=None):
    if not start_date:
        start_date = datetime.datetime.today()
    date_list = [start_date -
                 datetime.timedelta(days=x) for x in range(numdays)]
    return date_list


class Employee():
    def __init__(self, name):
        self.name = name


class Team():
    members = []

    def __init__(self, name, initial_members):
        self.name = name
        for member in initial_members:
            self.members.append(member)

    def add_member(self, new_member):
        self.members.append(new_member)


class WorkDay():
    length_hr = 8
    date = None

    def __init__(self, length_hr, date):
        self.length_hr = length_hr
        self.date = date


class Job():
    length_sec = 0
    date = None
    team = None

    def __init__(self, length_hr, address):
        self.length_sec = length_hr
        self.address = address

    def set_date(self, date):
        self.date = date

    def distance(self, job):
        distance_mi = 8
        time_min = 30
        return distance_mi, time_min


class Schedule():
    """
        TODO:Model Schedule as a graph, for simple SAT translation
        pay_period = [] list of workdays
        jobs = []   list of jobs
        teams = []  teams assigned in this pay period
        assignments = {} dict mapping jobs to teams and days
        var_dict= {} map of cnf object to its corresponding digit in the formula
        SAT_fomula = CNF()


    Variables:
     Teams: T_i {true: if team is working, false: otherwise }
     Jobs: J_ij {true if team is assigned to job j, false: otherwise}
     Days: D_ijk {true: if team is assigned a job j on day k, false: otherwise}
    Constraints:
    Jobs must be assigned to exactly 1 team, Jobs take at most one full workday:
    Jobs in the same day must be completed in the duration of the including travel time workday.
    REACH -Teams cannot be assigned more than 2 jobs more than the rest at any point in the pay period.
    """
    class CNF_Var:
        """
            cnf_ix is the index used by the schedule cnf formula
            category is the type of variable [T, J, D]
            mapping contains indexes from each list to the item of the variable
        """

        def __init__(self, cnf_ix, category, mapping):
            self.cnf_ix = cnf_ix
            self.category = category
            self.mapping = mapping
            self.sublist = []

    pay_period = []
    jobs = []
    teams = []
    cnf_map = []
    cnf_vars = []
    SAT_formula = []

    def __init__(self, period_start=None, period_length=5, workday_len=8, **kwargs):
        if "pay_period" in kwargs:
            self.pay_period = kwargs["pay_period"]
        else:
            if not period_start:
                period_start = datetime.datetime.today()
            std_pay_period = [WorkDay(workday_len, date)
                              for date in daterange(period_length, period_start)]
            self.pay_period = std_pay_period

    def unmap_team(self, team_ix):
        return self.cnf_vars[self.cnf_map[team_ix]-1]

    def unmap_job(self, team_ix, job_ix):
        return self.cnf_vars[self.unmap_team(team_ix).sublist[job_ix]-1]

    def unmap_day(self, team_ix, job_ix, day_ix):
        return self.cnf_vars[self.unmap_job(team_ix, job_ix).sublist[day_ix]-1]

    def curr_cnf_num(self):
        return len(self.cnf_vars) + 1

    def add_var(self, category, mapping):
        cnf_num = self.curr_cnf_num()
        var = self.CNF_Var(cnf_num, category, mapping)
        self.cnf_vars.append(var)
        return cnf_num

    def make_inner_vars(self, i, j):
        J_ij = self.add_var("J", {"job": j, "team": i})
        self.unmap_team(i).sublist.append(J_ij)
        for k, day in enumerate(self.pay_period):
            D_ijk = self.add_var("D", {"day": k, "job": j, "team": i})
            self.unmap_job(i, j).sublist.append(D_ijk)

    def add_job(self, job):
        j = len(self.jobs)
        self.jobs.append(job)
        # add avrs for this job
        for i, team in enumerate(self.teams):
            self.make_inner_vars(i, j)

    def add_team(self, team):
        i = len(self.teams)
        self.teams.append(team)
        T_i = self.add_var("T", {"team": i})
        self.cnf_map.append(T_i)
        # add vars for this team
        for j, job in enumerate(self.jobs):
            self.make_inner_vars(i, j)

    def encode_full_cnf(self):
        # assumes mapping is correct and complete
        # this assumes one job per day
        clauses = []
        for team in self.cnf_map:
            # having this team implies variables containing these teams
            T_i = self.cnf_vars[team-1]
            i = T_i.cnf_ix
            team_per_job = [-i]
            for job in T_i.sublist:
                # print(job)
                J_ij = self.cnf_vars[job-1]
                j = J_ij.cnf_ix
                job_per_team = [-j, i]
                clauses.append(job_per_team)
                day_per_job = [-j]
                team_per_job.append(j)
                for day in J_ij.sublist:
                    # do [-D_ij, J_ij][-D_ij,J_ij] one clause per job
                    # having this day implies no other job has this day
                    # TODO: make this account for multiple jobs in a day
                    D_ijk = self.cnf_vars[day-1]
                    k = D_ijk.cnf_ix
                    job_per_day = [-k, j]
                    clauses.append(job_per_day)
                    # also
                    # do [-JT_ij,DJT_ij,DJT_ij] one item in clause per job
                    # having this job implies no other day has this job
                    day_per_job.append(k)
                clauses.append(day_per_job)
            clauses.append(team_per_job)

        self.SAT_formula = clauses

    def resolve(self):
        self.encode_full_cnf()
        print(self.SAT_formula)
        print([var.cnf_ix for var in self.cnf_vars])
        g = MinisatGH(bootstrap_with=self.SAT_formula)
        print(g.solve())
        res = g.get_model()
        print(res)
        return self.humanize(res)

    def humanize(self, result):
        if None:
            return "Unsatisfiable"
        res_obj = {}
        for ix in result:
            val = ix > 0
            var = self.cnf_vars[abs(ix)-1]
            # if var.category == "T":
            #     key = self.teams[var.mapping["team"]].name
            #     res_obj[key] = var.mapping
            # elif var.category == "J":
            #     key = self.jobs[var.mapping["team"]].address
            #     res_obj[key] = var.mapping
            # else:
            if var.category == "D":
                key = ix
                job = self.jobs[var.mapping["job"]].address
                team = self.teams[var.mapping["team"]].name
                day = var.mapping["day"]
                res_obj[key] = {
                    "job": job,
                    "team": team,
                    "day": day,
                }

        return res_obj


if __name__ == "__main__":
    print("SAT Schedule")
    formula = CNF()
    formula.append([-1, 2])

    test = Schedule(period_length=1)
    team1 = Team("A", [Employee("Luis"), Employee("Leo")])
    team2 = Team("B", [Employee("Eva"), Employee("Mar")])
    test.add_team(team1)
    # test.add_team(team2)
    test.add_job(Job(3, "1 LMU Drive"))
    test.add_job(Job(3, "1062 Durness"))

    print(test.resolve())
