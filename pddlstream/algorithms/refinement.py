from __future__ import print_function

from itertools import product
from copy import deepcopy, copy
from collections import namedtuple
from pddlstream.algorithms.instantiation import Instantiator
from pddlstream.algorithms.scheduling.recover_streams import evaluations_from_stream_plan, get_achieving_streams
from pddlstream.algorithms.constraints import add_plan_constraints, PlanConstraints, WILD
from pddlstream.language.constants import FAILED, INFEASIBLE, is_plan, str_from_plan, get_length
from pddlstream.language.conversion import evaluation_from_fact, substitute_expression, fact2eval, eval2fact
from pddlstream.language.function import FunctionResult, Function
from pddlstream.language.stream import StreamResult, Result
from pddlstream.language.statistics import check_effort, compute_plan_effort
from pddlstream.language.object import Object, OptimisticObject
from pddlstream.utils import INF, safe_zip, get_mapping, implies

CONSTRAIN_STREAMS = False
CONSTRAIN_PLANS = False  # TODO: might cause some strange effects on continuous_tamp
MAX_DEPTH = INF  # 1 | INF

ResultNode = namedtuple('ResultNode', ['effort', 'level', 'result'])


def is_refined(stream_plan):
    # TODO: lazily expand the shared objects in some cases to prevent increase in size
    if not is_plan(stream_plan):
        return True
    # TODO: some of these opt_index equal None
    return all((result.opt_index is None) or (result.opt_index == 0)
               for result in stream_plan)


##################################################

def optimistic_process_instance(instantiator, instance):
    results = []
    for result in instance.next_optimistic():
        new_facts = False
        complexity = instantiator.compute_complexity(instance)
        for fact in result.get_certified():
            new_facts |= instantiator.add_atom(evaluation_from_fact(fact), complexity)
        if isinstance(result, FunctionResult) or new_facts:
            # yield result
            results.append(result)
    return results


def prune_high_effort_streams(streams, max_effort=INF, **effort_args):
    # TODO: convert streams to test streams with extremely high effort
    low_effort_streams = []
    for stream in streams:
        effort = stream.get_effort(**effort_args)
        if isinstance(stream, Function) or check_effort(effort, max_effort):
            low_effort_streams.append(stream)
    return low_effort_streams


def optimistic_evaluate_streams(evaluations, streams, complexity_limit, **effort_args):
    optimistic_streams = prune_high_effort_streams(streams, **effort_args)
    instantiator = Instantiator(optimistic_streams)
    for evaluation, node in evaluations.items():
        if node.complexity <= complexity_limit:
            instantiator.add_atom(evaluation, node.complexity)
    results = []
    while instantiator and (instantiator.min_complexity() <= complexity_limit):
        instance = instantiator.pop_stream()
        optms_resuls = instance.next_optimistic()
        if optms_resuls:
            [result] = optms_resuls
            new_facts = False
            complexity = instantiator.compute_complexity(instance)
            for fact in result.get_certified():
                new_facts |= instantiator.add_atom(evaluation_from_fact(fact), complexity)
            if isinstance(result, FunctionResult) or new_facts:
                # assert not isinstance(result, FunctionResult)
                results.extend(optms_resuls)

        # TODO: instantiate and solve to avoid repeated work
    exhausted = not instantiator
    return results, exhausted


##################################################

def optimistic_stream_instantiation(instance, bindings, evaluations, opt_evaluations,
                                    only_immediate=False):
    # TODO: combination for domain predicates
    new_instances = []
    for input_combo in product(*[bindings.get(i, [i]) for i in instance.input_objects]):
        mapping = get_mapping(instance.input_objects, input_combo)
        domain_evaluations = set(map(evaluation_from_fact, substitute_expression(
            instance.get_domain(), mapping)))  # TODO: could just instantiate first
        if domain_evaluations <= opt_evaluations:
            new_instance = instance.external.get_instance(input_combo)
            if (new_instance.opt_index != 0) and implies(only_immediate, domain_evaluations <= evaluations):
                new_instance.opt_index -= 1
            new_instances.append(new_instance)
    return new_instances


def optimistic_stream_evaluation(evaluations, stream_plan, use_bindings=True):
    # TODO: can also use the instantiator and operate directly on the outputs
    # TODO: could bind by just using new_evaluations
    evaluations = set(evaluations)  # For subset testing
    opt_evaluations = set(evaluations)
    new_results = []
    bindings = {}
    for opt_result in stream_plan:  # TODO: just refine the first step of the plan
        for new_instance in optimistic_stream_instantiation(
                opt_result.instance, (bindings if use_bindings else {}), evaluations, opt_evaluations):
            for new_result in new_instance.next_optimistic():
                opt_evaluations.update(map(evaluation_from_fact, new_result.get_certified()))
                new_results.append(new_result)
                if isinstance(new_result, StreamResult):  # Could not add if same value
                    for opt, obj in safe_zip(opt_result.output_objects, new_result.output_objects):
                        bindings.setdefault(opt, []).append(obj)
    return new_results, bindings


##################################################

def compute_stream_results(evaluations, opt_results, externals, complexity_limit, **effort_args):
    # TODO: start from the original evaluations or use the stream plan preimage
    # TODO: only use streams in the states between the two actions
    # TODO: apply hierarchical planning to restrict the set of streams that considered on each subproblem
    # TODO: plan up to first action that only has one
    # TODO: revisit considering double bound streams
    functions = list(filter(lambda s: type(s) is Function, externals))
    opt_evaluations = evaluations_from_stream_plan(evaluations, opt_results)
    new_results, _ = optimistic_evaluate_streams(opt_evaluations, functions, complexity_limit, **effort_args)
    return opt_results + new_results


def compute_skeleton_constraints(action_plan, bindings):
    skeleton = []
    groups = {arg: values for arg, values in bindings.items() if len(values) != 1}
    for name, args in action_plan:
        new_args = []
        for arg in args:
            if isinstance(arg, Object):
                new_args.append(arg)
            elif isinstance(arg, OptimisticObject):
                assert bindings.get(arg, [])
                if len(bindings[arg]) == 1:
                    new_args.append(bindings[arg][0])
                else:
                    # new_args.append(WILD)
                    new_args.append(arg)
            else:
                raise ValueError(arg)
        skeleton.append((name, new_args))
    # exact=False because we might need new actions
    return PlanConstraints(skeletons=[skeleton], groups=groups, exact=False, max_cost=INF)


##################################################


def is_plan_successful(plan):
    """Return True
       if the plan is neither FAILED nor INFEASIBLE"""
    return not (plan in [None, False])


def is_plan_certified(stream_plan):
    if stream_plan is None:
        return None

    # if all results in the stream plan is verified (optms_index=None or 0), then the plan is certified
    r = all((result.opt_index is None) or (result.opt_index == 0)
            for result in stream_plan)
    return r


def unique_instances(init_evals, stream_plan):
    """
    Update the stream_plan-related instances by reducing their optms_index, make them more unique
    the resultant instances will be saved in their own streams, and available for next Stream.get_instance()
    """

    # Initialize accumulated optimistic evaluations. The init_evals will not be changed here.
    accm_evals = set(init_evals)

    for result in stream_plan:
        instance = result.instance  # instance relevant to stream plan will be marked more unique
        domain_evals = set(map(fact2eval, instance.domain))

        if domain_evals <= accm_evals:
            # new_instance may be identical to instance
            r_instance = instance.external.get_instance(instance.input_objects)
            if r_instance.opt_index != 0:
                # if this instance is not unique, then make it unique
                r_instance.opt_index -= 1

            for new_result in r_instance.next_optimistic():
                accm_evals.update(map(fact2eval, new_result.get_certified()))


def plan_action_plan_stream(optms_plan_solver, evaluations, externals, level_limit, **effort_args):
    # externals = (streams + functions + optimizers)
    # Previously didn't have unique optimistic objects that could be constructed at arbitrary depths
    limited_evals = {e: n for e, n in evaluations.items() if n.complexity <= level_limit}
    num_iterations = 0
    while True:
        num_iterations += 1

        optms_results, exhausted = optimistic_evaluate_streams(limited_evals, externals, level_limit, **effort_args)

        stream_plan, action_plan, cost = optms_plan_solver.planner_core(limited_evals, optms_results)

        print('  Attempt: {} | Results: {} | Success: {} | Certified: {}'.format(
            num_iterations, len(optms_results), is_plan_successful(action_plan), is_plan_certified(stream_plan)))

        if not is_plan_successful(action_plan):
            # if the plan is not successful, then break and start a new session with increased level_limit
            status = INFEASIBLE if exhausted else FAILED
            return status, status, cost
        elif is_plan_certified(stream_plan):
            # If the plan is all unique and successful, then return the plans
            return stream_plan, action_plan, cost
        else:
            unique_instances(limited_evals, stream_plan)
            # continue the while loop
