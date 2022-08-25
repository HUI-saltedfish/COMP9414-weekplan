import copy
import sys
import re
from cspProblem import Constraint, CSP
from cspConsistency import Search_with_AC_from_CSP
from searchGeneric import AStarSearcher
from itertools import accumulate
import operator
from sys import stdin

week_dict = {'sun': 100, 'mon': 200, 'tue': 300, 'wed': 400, 'thu': 500, 'fri': 600, 'sat': 700}

time_dict = {'7am': 7, '8am': 8, '9am': 9, '10am': 10, '11am': 11, '12pm': 12, '1pm': 13, '2pm': 14, '3pm': 15,
             '4pm': 16, '5pm': 17, '6pm': 18, '7pm': 19}

# all the working time slot
timeslot_mapping = dict()
for t in time_dict.keys():
    for d in week_dict.keys():
        timeslot_mapping[week_dict[d] + time_dict[t]] = d + " " + t

reversed_timeslot = dict()
for t in time_dict.keys():
    for d in week_dict.keys():
        reversed_timeslot[d + ' ' + t] = week_dict[d] + time_dict[t]


# binary constraints

# A1 ends when or before A2 starts
def before(a1: tuple, a2: tuple):
    if a1[1] <= a2[0]:
        return True
    else:
        return False


# A1 starts after or when A2 ends
def after(a1: tuple, a2: tuple):
    if a1[0] >= a2[1]:
        return True
    else:
        return False


# A1 and A2 start and end on the same day
def same_day(a1: tuple, a2: tuple):
    a1_day = a1[0] // 100
    a2_day = a2[0] // 100
    if a1_day == a2_day:
        return True
    else:
        return False


# A1 and A2 start at the same day and time
def starts(a1: tuple, a2: tuple):
    if a1[0] == a2[0]:
        return True
    else:
        return False


# A1 and A2 end at the same day and time
def ends(a1: tuple, a2: tuple):
    if a1[1] == a2[1]:
        return True
    else:
        return False


# A2 starts after A1 starts and not after A1 ends, and ends after A1 ends
def overlaps(a1: tuple, a2: tuple):
    a2s_after_a1s = a2[0] >= a1[0]
    a2s_before_a1e = a2[0] <= a1[1]
    a2e_after_a1e = a2[1] >= a1[1]
    return a2s_after_a1s and a2s_before_a1e and a2e_after_a1e


# A1 starts after A2 starts and ends before A2 ends
def during(a1: tuple, a2: tuple):
    return (a1[0] >= a2[0]) and (a1[1] <= a2[1])


# A1 and A2 start and end at the same day and time
def equals(a1: tuple, a2: tuple):
    return (a1[0] == a2[0]) and (a1[1] == a2[1])


# compute single step of cost
def compute_single_cost(deadline, actual_time, cost):
    actual_time = actual_time % 100

    time_gap = abs(actual_time - deadline)
    if time_gap == 0:
        return 0
    else:
        return time_gap * cost


# compute all cost
def compute_total_cost(schedule, deadlines, costs):
    cost = list()
    for k in schedule:
        cost.append(compute_single_cost(deadlines[k], schedule[k], costs[k]))
    return sum(cost)


# domains process
def read_domain(domain, possible_value, duration):
    sz_domain = domain
    cost = 0
    deadline = 0
    if 'ends-before' in sz_domain:
        sz_domain = sz_domain.split(' ')[1]
        possible_value = [
            v for v in possible_value
            if v % 100 + duration <= time_dict[sz_domain]
        ]
    elif 'starts-before' in sz_domain:
        sz_domain = sz_domain.split(' ')[1]
        possible_value = [
            v for v in possible_value
            if v % 100 <= time_dict[sz_domain]
        ]
    elif 'starts-after' in sz_domain:
        sz_domain = sz_domain.split(' ')[1]
        possible_value = [
            v for v in possible_value
            if v % 100 >= time_dict[sz_domain]
        ]
    elif 'ends-after' in sz_domain:
        sz_domain = sz_domain.split(' ')[1]
        possible_value = [
            v for v in possible_value
            if v % 100 + duration >= time_dict[sz_domain]
        ]
    elif 'on' in sz_domain:
        sz_domain = sz_domain.split(' ')[1]
        possible_value = [
            v for v in possible_value
            if (v // 100) == (week_dict[sz_domain] // 100)
        ]
    elif 'before' in sz_domain:
        sz_domain = sz_domain.split(' ')[1]
        possible_value = [
            v for v in possible_value
            if (v // 100) <= (week_dict[sz_domain] // 100)
        ]
    elif 'after' in sz_domain:
        sz_domain = sz_domain.split(' ')[1]
        possible_value = [
            v for v in possible_value
            if (v // 100) >= (week_dict[sz_domain] // 100)
        ]
    elif 'around' in sz_domain:
        temp_ls = sz_domain.split(' ')
        cost = int(temp_ls[-1])
        deadline = time_dict[temp_ls[-2]]

    return possible_value, cost, deadline


def remove_comment_and_spaces(content):
    temp_str = r'\s*#.*\n'
    content = re.sub(temp_str, '\n', content)
    temp_str = r'[ ]+'
    content = re.sub(temp_str, ' ', content)
    temp_str = r'\s*\n\s*'
    content = re.sub(temp_str, '\n', content)
    return content


# read input.txt
def read_task(content):
    all_constraints = list()
    all_domains = dict()

    content = content + '\n'

    content = remove_comment_and_spaces(content)

    result = dict(re.findall(
        r'activity\s(.*?)\s(.*?)\n', content, re.S
    ))

    all_tasks = dict()
    for k in result:
        all_tasks[k] = {'duration': int(result[k])}

    for t in all_tasks:
        temp_str = r'domain\s{}\s(.*?)\n'
        result = tuple(re.findall(
            temp_str.format(t), content, re.S
        ))

        possible_value = set()
        for v in set(timeslot_mapping.keys()):
            possible_value.add(v)

        task_cost = 0
        soft_deadline = 0
        for r in result:
            possible_value, cost, deadline = read_domain(r, possible_value, all_tasks[t]['duration'])
            if cost != 0:
                task_cost = copy.deepcopy(cost)
                soft_deadline = copy.deepcopy(deadline)

        all_tasks[t]['meta-info'] = copy.deepcopy(result)

        # cul soft deadline cost and deadline
        all_domains[t] = {(i, i + all_tasks[t]['duration']) for i in possible_value}
        all_tasks[t]['cost'] = copy.deepcopy(task_cost)
        all_tasks[t]['deadline'] = copy.deepcopy(soft_deadline)

    # cul total constraints
    temp_str = r'constraint\s(.*?)\s(.*?)\s(.*?)\n'
    result = tuple(re.findall(temp_str, content, re.S))

    # construct constraints
    for a1, condition, a2 in result:
        cons = None
        if condition == "ends":
            cons = Constraint((a1, a2), ends)
        elif condition == "overlaps":
            cons = Constraint((a1, a2), overlaps)
        elif condition == "during":
            cons = Constraint((a1, a2), during)
        elif condition == "equals":
            cons = Constraint((a1, a2), equals)
        elif condition == "same-day":
            cons = Constraint((a1, a2), same_day)
        elif condition == 'before':
            cons = Constraint((a1, a2), before)
        elif condition == 'after':
            cons = Constraint((a1, a2), after)
        elif condition == "starts":
            cons = Constraint((a1, a2), starts)
        all_constraints.append(cons)

    return all_tasks, all_constraints, all_domains


class Search_with_AC_from_Cost_CSP(Search_with_AC_from_CSP):
    def __init__(self, my_csp_var):
        super().__init__(my_csp_var)
        self.csp = copy.deepcopy(my_csp_var)
        self.variables = set(sorted(my_csp_var.domains, key=lambda t: my_csp_var.domains[t]))

    def heuristic(self, node):
        result = list()
        result.append(0)
        ls = list()
        for var in node:
            if self.csp.costs[var] != 0 and len(node[var]) > 0:
                temp_ls = list(node[var])
                temp = sorted(temp_ls, key=lambda x: abs(x[0] % 100 - self.csp.deadlines[var]))
                ls.append(abs(temp[0][0] % 100 - self.csp.deadlines[var]) * self.csp.costs[var])
        result.extend(list(accumulate(ls)))
        return result[-1]


def get_one_schedule(filename):
    all_tasks, all_constraints, all_domains = read_task(filename)
    deadlines = dict()
    for k in all_tasks:
        deadlines[k] = all_tasks[k]['deadline']
    costs = dict()
    for k in all_tasks:
        costs[k] = all_tasks[k]['cost']

    schedule_csp = MyCSP(all_domains=all_domains, all_constraints=all_constraints, all_tasks=all_tasks)
    temp_var_csp = Search_with_AC_from_Cost_CSP(schedule_csp)
    searcher = AStarSearcher(temp_var_csp)
    searcher.max_display_level = 0
    path = searcher.search()

    if path is None:
        print('No solution')
    else:
        assignments = dict()
        for k, v in path.end().items():
            assignments[k] = v.pop()[0]
        for k, v in assignments.items():
            print('{}:{}'.format(k, timeslot_mapping[v]))

        for k, v in assignments.items():
            assignments[k] = v
        total_cost = compute_total_cost(assignments, deadlines, costs)
        print('cost:{}'.format(total_cost))


class MyCSP(CSP):
    def __init__(self, all_domains, all_constraints, all_tasks):
        super().__init__(all_domains, all_constraints)
        self.costs = dict()
        for k in all_tasks:
            self.costs[k] = all_tasks[k]['cost']
        self.deadlines = dict()
        for k in all_tasks:
            self.deadlines[k] = all_tasks[k]['deadline']


# input_files = sys.argv[1:]
# for i in input_files:
#     get_one_schedule(i)
f = stdin.readlines()
content = "".join(f)
get_one_schedule(content)
