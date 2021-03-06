import os
import datetime
import pprint
import itertools
from pysat.formula import CNF
from pysat.solvers import MinisatGH
from pprint import pprint

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
    length_hr = 0
    date = None
    team = None

    def __init__(self, length_hr, address):
        self.length_hr = length_hr
        self.address = address

    def set_date(self, date):
        self.date = date

    def distance(self, job):
        distance_mi = 8
        time_hr = 0.25
        return distance_mi, time_hr

    def total_time(self, job):
        return self.length_hr + job.length_hr + self.distance(job)[1]


class Schedule():
    """
    Variables:
     Teams: T_i {true: if team is working, false: otherwise }
     Jobs: J_ij {true if team is assigned to job j, false: otherwise}
     Days: D_ijk {true: if team is assigned a job j on day k, false: otherwise}
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

    def jobs_overlap(self, d1_ix, d2_ix):
        d1 = self.cnf_vars[d1_ix-1].mapping
        d2 = self.cnf_vars[d2_ix-1].mapping
        if d1["team"] != d2["team"]:
            return True
        if d1["job"] == d2["job"]:
            return True
        if d1["day"] != d2["day"]:
            return True
        if self.jobs[d1["job"]].total_time(self.jobs[d2["job"]]) <= self.pay_period[d1["day"]].length_hr:
            return False
        return True

    def encode_full_cnf(self):
        # TODO: clean up this monster
        # TODO: add [-J_ijk, -J_ijk] if the combination of i's has the same employees.
        # Assumes teams can have overlapping members
        # assumes mapping is correct and complete
        # this assumes one job per day
        clauses = []
        i_vars = []
        j_vars = [[] for i in range(len(self.jobs))]
        team_jobs = [[] for _ in range(len(self.jobs))]
        for i_ix, team in enumerate(self.cnf_map):
            team_days = []
            # having this team implies variables containing these teams
            T_i = self.cnf_vars[team-1]
            i = T_i.cnf_ix
            # this team implies certain jobs are satisfiable
            team_per_job = [-i]
            jobs = T_i.sublist
            for j_ix, j in enumerate(jobs):
                team_jobs[j_ix].append(j)
                J_ij = self.cnf_vars[j-1]
                job_per_team = [-j, i]
                # this job assignment implies certain team is working
                clauses.append(job_per_team)
                # this job implies certain assignments are satisfiable
                day_per_job = [-j]
                team_per_job.append(j)
                day_assn = []
                days = J_ij.sublist
                team_days.append(days)
                j_vars[j_ix].append(days)
                for k in days:
                    # this job assignment implies certain job_team pairing is met
                    job_per_day = [-k, j]
                    clauses.append(job_per_day)
                    day_per_job.append(k)
                clauses.append(day_per_job)

            clauses.append(team_per_job)
            i_vars.append(team_days)
        # print(team_jobs)
        clauses.extend(team_jobs)
        # print("byTeam")
        # print(i_vars)
        # print("byJob")
        # print(j_vars)
        for ix, team_group in enumerate(i_vars):
            flat_grp = sum(team_group, [])  # same team
            for rem_team in i_vars[ix+1:]:
                # multiple teams do not do the same job on the same day
                rem = sum(rem_team, [])
                c = [[-job, -rem[job_ix]]
                     for job_ix, job in enumerate(flat_grp)]
                # print("c", c)
                # remove constraint if jobs can be in the same day

                clauses.extend(c)

        for ix, job_group in enumerate(j_vars):
            # jobs cannot happen on the same day
            flat_grp = sum(job_group, [])  # same address
            c = [[-x, -y] for ix, x in enumerate(flat_grp)
                 for y in flat_grp[ix+1:]]
            # print("c", c)
            clauses.extend(c)
            for rem_job in j_vars[ix+1:]:
                # jobs is done after one team works on it for one day
                # same team does not do multiple jobs on the same day
                rem = sum(rem_job, [])
                c = [[-team, -rem[team_ix]]
                     for team_ix, team in enumerate(flat_grp) if self.jobs_overlap(team, rem[team_ix])]
                # print("c", c)
                clauses.extend(c)

        self.SAT_formula = clauses

    def resolve(self):
        if(len(self.teams) == 0 or len(self.jobs) == 0):
            print("not enough variables to decide")
            return False, None
        self.encode_full_cnf()
        g = MinisatGH(bootstrap_with=self.SAT_formula)
        print(g.solve())
        res = g.get_model()
        print(res)
        return self.humanize(res)

    def humanize(self, result):
        if not result:
            return "Unsatisfiable", None
        res_obj = {}
        assignments = {}
        for ix in result:
            val = ix > 0
            var = self.cnf_vars[abs(ix)-1]

            if var.category == "D":
                job = self.jobs[var.mapping["job"]].address
                team = self.teams[var.mapping["team"]].name
                day = var.mapping["day"]
                res_obj[ix] = {
                    "job": job,
                    "team": team,
                    "day": day,
                }
                if val:
                    assignments[ix] = res_obj[ix]
            elif var.category == "T":
                res_obj[ix] = self.teams[var.mapping["team"]].name
            elif var.category == "J":
                job = self.jobs[var.mapping["job"]].address
                team = self.teams[var.mapping["team"]].name
                res_obj[ix] = {"job": job, "team": team}

        return res_obj, assignments


if __name__ == "__main__":
    print("SAT Schedule")
    # formula = CNF()
    # formula.append([-1, 2])

    # test = Schedule(period_length=1)
    # test.add_team(Team("A", [Employee("Luis"), Employee("Leo")]))
    # test.add_team(Team("B", [Employee("Eva"), Employee("Mar")]))
    # # test.add_team(Team("C", [Employee("Teca")]))
    # test.add_job(Job(3, "1 LMU Drive"))
    # test.add_job(Job(5, "1062 Durness"))
    # # test.add_job(Job(2, "Hello"))
    # # test.add_job(Job(2, "Hello"))
    # # test.add_job(Job(2, "Hello"))
    # # test.add_job(Job(2, "Hello"))
    # res = test.resolve()

    # pprint(test.humanize([x.cnf_ix for x in test.cnf_vars])[0])
    # print(test.SAT_formula)
    # # pprint(res[0])
    # pprint(res[1])

    proceed = True

    length = int(input("How many days are in your schedule?\t"))
    sched = Schedule(period_length=length)

    def cmd_add_team():
        team = None
        team_name = str(input("What is the team name?\t"))
        employee_names = str(
            input("Input comma separated names of employees in the team. \t"))
        employees = [Employee(name) for name in employee_names.split(',')]
        team = Team(team_name, employees)
        return team

    def cmd_add_job():
        job = None
        print("For testing purposes the jobs will default to travel length of one quarter of an hour.\n")
        job_name = str(input("What is the job address?\t"))
        job_length = int(
            input("How long will it take to complete this job?\t"))
        job = Job(job_length, job_name)
        return job
    resolve = False
    while proceed:
        choice = int(
            input("pick one: 1) add team 2) add job 3) resolve 4) quit \t"))
        if choice == 1:
            team = cmd_add_team()
            if not team:
                continue
            sched.add_team(team)
            resolve = True
        if choice == 2:
            job = cmd_add_job()
            if not job:
                continue
            sched.add_job(job)
            resolve = True
        if choice == 3:
            if resolve:
                print(sched.resolve()[1])
            else:
                print("No schedule was made")
        if choice == 4:
            proceed = False
        else:
            continue
