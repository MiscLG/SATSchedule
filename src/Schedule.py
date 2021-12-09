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
    name = ""
    members = []

    def __init__(self, name, initial_members):
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
    address = None
    team = Team

    def __init__(self, length_hr, address):
        self.length_sec = length
        self.location = address

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
    """
    pay_period = []
    jobs = []
    teams = []
    assignments = {}
    var_dict = []
    SAT_fomula = CNF()

    def __init__(self, period_start=None, period_length=15, workday_len=8, **kwargs):
        if kwargs["pay_period"]:
            self.pay_period = kwargs["pay_period"]
        else:
            if not period_start:
                period_start = datetime.datetime.today()
            std_pay_period = [WorkDay(workday_len, date)
                              for date in daterange(period_length, period_start)]

    def curr_cnf_num(self):
        return len(var_dict) + 1

    def job_cnf_clauses(self, job):
        # TODO: model as a graph

        pass

    def add_job(self, job):
        job_index = len(self.jobs)
        job_cnf = curr_cnf_num()
        self.jobs.append({"obj": job, "cnf_ix": job_cnf})
        self.var_dict.append({"category": "job", "index": job_index})

    def add_team(self, team):
        team_index = len(self.teams)
        team_cnf = curr_cnf_num()
        self.teams.append({"obj": team, "cnf_ix": team_cnf})
        self.var_dict.append({"category": "team", "index": team_index})
        # we would reassign here if we were accounting for fair, weighted, distribution of work

    def humanize_result(self, result):
        if None:
            return "Unsatisfiable"
        res_obj = {}
        for var in result:
            val = var > 0
            data = var_dict[Math.abs(var)]
            if data["category"] == "team":
                key = self.teams[data["index"]]["obj"].name
                res_obj[key] = val
            elif data["category"] == "job":
                key = self.jobs[data["index"]]["obj"].address
                res_obj[key] = val

        return res_obj


if __name__ == "__main__":
    print("SAT Schedule")
    formula = CNF()
    formula.append([-1, 2])

    g = MinisatGH(bootstrap_with=formula)
    print(g.solve())
    res = g.get_model()
    print(g.get_model())
