#!/usr/bin/env python2.7

from __future__ import print_function

import argparse

import pddlstream.algorithms.scheduling.diverse
pddlstream.algorithms.scheduling.diverse.DEFAULT_K = 1

import pddlstream.algorithms.downward
pddlstream.algorithms.downward.USE_FORBID = True

from pddlstream.algorithms.focused import solve_focused
from pddlstream.language.generator import from_test
from pddlstream.language.stream import StreamInfo, DEBUG
from pddlstream.utils import read, get_file_path
from pddlstream.language.constants import print_solution, PDDLProblem, And, dump_pddlstream, is_plan
from examples.fault_tolerant.logistics.run import test_from_bernoulli_fn, CachedFn
from examples.fault_tolerant.data_network.run import fact_from_str

P_SUCCESS = 1

INIT = """
(CONNECTED A B)
(CONNECTED A C)
(CONNECTED B D)
(CONNECTED C D)
(CONNECTED C E)
(CONNECTED D F)
(CONNECTED D G)
(CONNECTED E G)
(CONNECTED F H)
(CONNECTED G H)
(CONNECTED G I)
(SOURCE A)
(SOURCE D)
(TARGET H)
(TARGET I)
(POI E)
(POI F)

(considered dummy)
(DISCARD_AFTER E dummy)
(DISCARD_AFTER F E)
"""

GOAL = """
(__goal-achieved)
(considered E)
(considered F)
"""

def get_problem(*kwargs):
    domain_pddl = read(get_file_path(__file__, 'domain.pddl'))
    constant_map = {}
    #stream_pddl = read(get_file_path(__file__, 'stream.pddl'))
    stream_pddl = None

    # TODO: compare statistical success and the actual success
    bernoulli_fns = {
        #'test-open': fn_from_constant(P_SUCCESS),
    }

    # universe_test | empty_test
    stream_map = {
        #'test-less_equal': from_test(lambda x, y: int_from_str(x) <= int_from_str(y)),
        #'test-sum': from_test(lambda x, y, z: int_from_str(x) + int_from_str(y) == int_from_str(z)),
    }
    stream_map.update({name: from_test(CachedFn(test_from_bernoulli_fn(fn)))
                       for name, fn in bernoulli_fns.items()})

    init = [fact_from_str(s) for s in INIT.split('\n') if s]
    goal_literals = [fact_from_str(s) for s in GOAL.split('\n') if s]

    goal = And(*goal_literals)

    return PDDLProblem(domain_pddl, constant_map, stream_pddl, stream_map, init, goal)

def solve_pddlstream(num=1, **kwargs):
    stream_info = {
        'test-less_equal': StreamInfo(eager=True, p_success=0),
        'test-sum': StreamInfo(eager=True, p_success=0), # TODO: p_success=lambda x: 0.5
        #'test-open': StreamInfo(p_success=P_SUCCESS),
    }

    problem = get_problem(**kwargs)
    dump_pddlstream(problem)

    successes = 0.
    for _ in range(num):
        print('\n'+'-'*5+'\n')
        #problem = get_problem(**kwargs)
        #solution = solve_incremental(problem, unit_costs=True, debug=True)
        solution = solve_focused(problem, stream_info=stream_info,
                                 unit_costs=True, unit_efforts=False, debug=True,
                                 #initial_complexity=1, max_iterations=1, max_skeletons=1
                                 )
        plan, cost, certificate = solution
        print_solution(solution)
        successes += is_plan(plan)
    print('Fraction {:.3f}'.format(successes / num))

##################################################

def main():
    parser = argparse.ArgumentParser()
    #parser.add_argument('-v', '--visualize', action='store_true')
    args = parser.parse_args()
    solve_pddlstream()

if __name__ == '__main__':
    main()

# https://github.com/IBM/risk-pddl
