from cspProblem import Constraint, CSP
from cspConsistency import Search_with_AC_from_CSP
from searchGeneric import AStarSearcher

from sys import stdin

base = 100
week_list = ['sun', 'mon', 'tue', 'wed', 'thu', 'fri', 'sat']
week2num = dict()
for i, week in enumerate(week_list):
    week2num[week] = i * base

start_time = 7
time_list = ['7am', '8am', '9am', '10am', '11am', '12pm', '1pm', '2pm', '3pm', '4pm', '5pm', '6pm', '7pm']
time2num = dict()
for i, time in enumerate(time_list):
    time2num[time] = start_time + i

num2date = dict()
for d in week_list:
    for t in time_list:
        date = d + " " + t
        k = week2num[d] + time2num[t]
        num2date[k] = date

import copy
import sys
import re


def before(activity1, activity2):
    return activity1[1] <= activity2[0]


def after(activity1, activity2):
    return activity1[0] >= activity2[1]


def same_day(activity1, activity2):
    return activity1[0] // base == activity2[0] // base


def starts(activity1, activity2):
    return activity1[0] == activity2[0]


def ends(activity1, activity2):
    return activity1[1] == activity2[1]


def overlaps(activity1, activity2):
    return (activity2[0] >= activity1[0]) and (activity2[0] <= activity2[1]) and (activity2[1] > activity1[1])


def during(activity1, activity2):
    return (activity1[0] >= activity2[0]) and (activity1[1] <= activity2[1])


def equals(activity1, activity2):
    return activity1 == activity2


def cul_sin_cost(end_time, realtime, cost):
    hour = realtime % 100
    gap_hours = abs(end_time - hour)
    return cost * gap_hours


def cul_all_cost(path, end_time, costs):
    final_costs = 0
    for node in path:
        final_costs += cul_sin_cost(end_time[node], path[node], costs[node])
    return final_costs


def domain_process(sz_domain, poss_val, dur):
    ret_poss_val = list()
    cost = 0
    end_time = 0
    if "end-before" in sz_domain:
        t = sz_domain.split(" ")[-1]
        for v in poss_val:
            if v % base + dur <= time2num[t]:
                ret_poss_val.append(v)
    elif 'starts-before' in sz_domain:
        t = sz_domain.split(" ")[-1]
        for v in poss_val:
            if v % base <= time2num[t]:
                ret_poss_val.append(v)
    elif 'starts-after' in sz_domain:
        t = sz_domain.split(" ")[-1]
        for v in poss_val:
            if v % base >= time2num[t]:
                ret_poss_val.append(v)
    elif 'ends-after' in sz_domain:
        t = sz_domain.split(' ')[-1]
        for v in poss_val:
            if v % base + dur >= time2num[t]:
                ret_poss_val.append(v)
    elif 'on' in sz_domain:
        d = sz_domain.split(' ')[-1]
        for v in poss_val:
            if v // base == (week2num[d] // base):
                ret_poss_val.append(v)
    elif 'before' in sz_domain:
        d = sz_domain.split(' ')[-1]
        for v in poss_val:
            if (v // base) <= (week2num[d] // base):
                ret_poss_val.append(v)
    elif 'after' in sz_domain:
        d = sz_domain.split(' ')[-1]
        for v in poss_val:
            if (v // base) >= (week2num[d] // base):
                ret_poss_val.append(v)
    elif 'around' in sz_domain:
        ls = sz_domain.split(" ")
        cost = int(ls[-1])
        t = ls[-2]
        end_time = time2num[t]
        ret_poss_val = poss_val

    return ret_poss_val, cost, end_time


def remove(info):
    re_str1 = r'\s*'
    re_str2 = r'\n\s*'
    info = re.sub(re_str1 + re_str2, '\n', info)
    re_str1 = r'['
    re_str2 = ' ]+'
    info = re.sub(re_str1 + re_str2, ' ', info)
    re_str1 = r'\s*'
    re_str2 = r'#.*\n'
    info = re.sub(re_str1 + re_str2, '\n', info)
    return info


def constraints_fun(activity1, activity2, condition):
    if condition == "same-day":
        cons = Constraint((activity1, activity2), same_day)
    else:
        cons = Constraint((activity1, activity2), eval(condition))
    return cons


def read_input(info):
    domains = dict()
    constraints = list()
    tasks = dict()

    info = info + "\n"
    info = remove(info)

    temp_str1 = r'activit'
    temp_str2 = r'y\s(.*?)\s'
    temp_str3 = r'(.*?)\n'
    tasks_result = dict(re.findall(temp_str1 + temp_str2 + temp_str3, info, re.S))
    for activity in tasks_result:
        tasks[activity] = {"duration": int(tasks_result[activity])}

    key_list = list(tasks.keys())
    for activity in key_list:
        re_str = r'domain\s{}\s(.*?)\n'
        temp = re.findall(re_str.format(activity), info, re.S)
        domain_result = tuple(temp)
        poss_val = set(num2date.keys())

        end_time = 0
        task_cost = 0
        for sin in domain_result:
            dur = copy.deepcopy(tasks[activity]["duration"])
            poss_val, cost, end_time = domain_process(sin, poss_val, dur)
            if cost != 0:
                task_cost = copy.deepcopy(cost)
                end_time = copy.deepcopy(end_time)
        tasks[activity]["meta-info"] = copy.deepcopy(domain_result)

        domains[activity] = set()
        for start in poss_val:
            domains[activity].add((start, start + tasks[activity]["duration"],))
        tasks[activity]["cost"] = copy.copy(task_cost)
        tasks[activity]["deadline"] = copy.copy(end_time)

    temp_str1 = r'constraint\s'
    temp_str2 = r'(.*?)\s(.'
    temp_str3 = r'*?)\s(.*?)\n'
    constraints_result = tuple(re.findall(temp_str1 + temp_str2 + temp_str3, info, re.S))
    for activity1, con, activity2 in constraints_result:
        constraints.append(constraints_fun(activity1, activity2, con))
    x = copy.deepcopy(tasks)
    y = copy.deepcopy(constraints)
    z = copy.deepcopy(domains)
    return x, y, z


class My_Search_CSP(Search_with_AC_from_CSP):
    def __init__(self, csp_var):
        super(My_Search_CSP, self).__init__(csp_var)
        temp_csp = copy.copy(csp_var)
        x = base
        if x % 10 == 0:
            self.csp = copy.deepcopy(temp_csp)
            self.x = x
            self.variables = set(sorted(csp_var.domains, key=lambda t: csp_var.domains[t]))

    def heuristic(self, node):
        if self.x // 10 == 10:
            ret = list()
            ret.append(0)
        temp_data = 0
        for activity in node:
            if self.csp.costs[activity] != 0:
                if len(node[activity]) > 0:
                    min_data = float('inf')
                    for x, y in node[activity]:
                        temp_cost = abs(x % 100 - self.csp.deadlines[activity]) * self.csp.costs[activity]
                        min_data = min(temp_cost, min_data)
                    temp_data += min_data
        ret.append(temp_data)

        return ret[-1]


class MyCSP(CSP):
    def __init__(self, tol_dom, tol_cons, tol_tak):
        super().__init__(tol_dom, tol_cons)
        self.costs = {i: tol_tak[i]["cost"] for i in tol_tak}
        self.deadlines = {i: tol_tak[i]["deadline"] for i in tol_tak}


def main(data):
    res = read_input(data)
    activities, constraints, domains = res[0], res[1], res[2]
    end_time = {k: activities[k]["deadline"] for k in activities}
    costs = {k: activities[k]["cost"] for k in activities}
    ser = AStarSearcher(My_Search_CSP(MyCSP(domains, constraints, activities)))
    ser.max_display_level = 0
    route = ser.search()

    if not route:
        print("No solution")
    else:
        if base == 100:
            temp_dict = dict()
            for x, y in route.end().items():
                temp_dict[x] = y.pop()[0]
        if temp_dict is not None:
            for k, v in temp_dict.items():
                print(f'{k}:{num2date[v]}')

        total_cost = cul_all_cost(temp_dict, end_time, costs)
        print(f'cost:{total_cost}')


f = stdin.readlines()
content = "".join(f)
main(content)
