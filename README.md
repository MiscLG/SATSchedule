# SATSchedule

I use a sat solver to solve scheduling problems, analyzing the complexity of the problem along the way.

## Proposal

I will apply an open-source SAT solver (minisat) to scheduling construction jobs. I have come across this problem while designing an automation system for my father's rain gutter company. The problem is explicitly, we need to assign teams of workers to the jobs that come in, and we need to know which jobs can be assigned to different teams of people such that we can complete as many as possible, and workers get a fair amount of work so that their pay is consistent. Since this is a construction business, traveling salesman is also a part of this problem. To solve this problem completely we would require that we can do some amount of optimization because we need to maximize the use of time and take advantage of the location of workers at any given time, however, I believe that the problem of scheduling the teams to some location is NP complete the optimization should be NP hard. Nevertheless, since we are working with a small business and a similarly small set of variables per working day, solving this as a reduction of SAT should be quick and optimization should be manageable to do without approximation. For this project I will create the code to make this computation and will attempt to make a formal reduction from SAT to the given problem so that I can demonstrate the complexity I am hypothesizing. As a reach goal, I will attempt to find some optimization solution, but it is unlikely due to the schedule I am working with.

## Final Product:

I have created a program that allows me to schedule teams of workers to different jobs across a pay-period. This program is flexible enough to account for workdays of varying length, as well as how jobs of varying difficulties (estimated lengths of times) fit into these workdays. To implement this scheduling problem, I encode the different parts of the problem into CNF clauses (more on this below), thus reducing the problem to a Boolean Satisfiability problem.

### Encoding the problem

The schedule involves three different types of variables: Teams, Jobs, and WorkDays.
To encode the possible states of the schedule do the following:

> create T_i where i is the identifier of a Team associated with the schedule. If E_i is true, it means The team is working, otherwise it is false.
> create J_ij where i is the identifier of a team working the job identified with j. If J_ij is true, Team i is assigned to work on Job j.
> create D_ijk where i is the identifier of a team, j is the identifier of a job and k is the identifier of a workday. If D_ijk is true, it means team i is assigned to work on job j on workday k.

With the boolean variables established, we can encode schedule constraints into CNF clauses using these variables.

Constraints:

- Each job must be completed by only one team
  > Ex. If J_11, for all j != 1 produce [-J_12, -J_1(j)]. In plain English, a true job-team assignment variable J_ij implies all other assignments with different teams i and same job j are false.
- Jobs can be assigned only one team and workday.
  > Ex. If D_111, for all k !=1 and j==1 and all i, [-D_111,-D_ijk]. In plain English, an assignment variable D_ijk implies all other assignments involving the same job j, different workdays k and any team i are false.
- Jobs can be assigned to the same workday only if the length of completion and travel are less than the alotted time for the workday.
  > Ex. If D_111, for all k==1 and for all j, for all i!=1 [-D_111, -D_ijk]. In plain English, an assignment variable D_ijk implies all other assignements with different teams and the same day are false. To allow jobs that can be done back to back, we condition adding clauses like this based on the distance between the jobs of the variables in the clause.
- Teams cannot do multiple jobs at the same time
  > Ex. If D_111, for all k==1 and for all j!=1, for all i==1, [-D_111, -D_ijk]. In plain English, an assignment variable D_ijk implies all other assignements with the same team and day are false. To allow jobs that can be done back to back, we condition adding clauses like this based on the distance between the jobs of the variables in the clause.

Supporting Constraints:

- Assignment of D_ijk means [-D_ijk, j_ij] for each J_ij. Making a full day assignment implies the Job Variable that indicates that the Job and team are assigned to each other.
- Assignment of J_ik means [-J_ij, d_ijk for each D_ijk]. If a Job is assigned to a team, then one of the day assignments that has the same pairing of job and team must be true.
- Assignment of T_i means [-J_ij, j_ij for each J_ij]. Saying that a Team is working implies that one of the variables that contains that team is true.
- Assignment of J_ik means [-J_ij, t_i] for each T_i. If a Job is a assigned a team, then the variable that contains that team must be true.

Each of these constraints is encoded into corresponding cnf_clauses and then that clause is processed by Minisat using the pysat library. This library gives me a solution as a list of variables that are set to either true or false. Since this is not a human readable answer, I take the workday variables D_ijk that are true and show the relevant data for the team, job and day that the jobs are assigned. Displaying this data I can obtain the assignment I need for the pay_period, although finer details about specific times, order of execution within a day and how much workers are getting payed in each job is left out to be calculated at a later time. Although those items may be doable with SAT, covering those bases may be useful for optimization, but for now, this project deals solely with obtaining assignments that work within business requirements.

### Formally

We can prove this scheduling problem is NP complete:

- The problem is in NP.
  > An assignment can be checked in polynomial time. Checking will mean making sure assignments are not overlapping by day, team, and job. We can make this comparison by hashing the assignments by their identifiers and checking for collisions when adding to a hashmap.
- The problem is NP-Hard.

  > We can Reduce this problem to SAT in polynomial time. Using the above CNF encoding rules. With t being the number of teams, j being the number of jobs and d being the number of workdays. The number of variables v = t+tj + tjd. The number of clauses created is a function of t, j, and d. If we consider n to be the maximum between t,j and d then the overall complexity of this step end up being some O(n^2). This encoding can then be solved as a Boolean Satisfiability problem.

  Therefore this scheduling problem is NP complete.

  If we wanted to create an optimization algorithm for this process, it would be NP-Hard because checking the optimal solution would require us to calculate the optimal solution. And to solve the problem we would have to solve SAT some number of times.
