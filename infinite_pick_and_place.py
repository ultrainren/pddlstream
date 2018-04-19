#!/usr/bin/env python
from pddlstream.conversion import convert_head, AND
from pddlstream.incremental import solve_exhaustive, solve_finite
from pddlstream.problem import Object
# TODO: each action would be associated with a control primitive anyways
from pddlstream.stream import from_gen_fn, from_fn, Stream

DOMAIN_PDDL = """
(define (domain pick-and-place)
  (:requirements :strips :equality)
  (:predicates 
    (Conf ?q)
    (Block ?b)
    (Pose ?p)
    (Kin ?q ?p)
    (AtPose ?p ?q)
    (AtConf ?q)
    (Holding ?b)
    (HandEmpty)
  )
  (:action move
    :parameters (?q1 ?q2)
    :precondition (and (Conf ?q1) (Conf ?q2) 
                       (AtConf ?q1))
    :effect (and (AtConf ?q2)
                 (not (AtConf ?q1)))
  )
  (:action pick
    :parameters (?q ?b ?p)
    :precondition (and (Block ?b) (Kin ?q ?p)
                       (AtConf ?q) (AtPose ?b ?p) (HandEmpty))
    :effect (and (Holding ?b)
                 (not (AtPose ?b ?p)) (not (HandEmpty)))
  )
  (:action place
    :parameters (?q ?b ?p)
    :precondition (and (Block ?b) (Kin ?q ?p) 
                       (AtConf ?q) (Holding ?b))
    :effect (and (AtPose ?b ?p) (HandEmpty)
                 (not (Holding ?b)))
  )
)
"""

STREAM_PDDL = """
(define (stream pick-and-place)
  (:stream sample-pose
    :inputs ()
    :domain ()
    :outputs (?p)
    :certified (and (Pose ?p))
  )
  (:stream inverse-kinematics
    :inputs (?p)
    :domain (Pose ?p)
    :outputs (?q)
    :certified (and (Conf ?q) (Kin ?q ?p))
  )
)
"""


def get_problem1(n_blocks=1, n_poses=5):
    assert(n_blocks + 1 <= n_poses)
    blocks = ['block{}'.format(i) for i in range(n_blocks)]
    #poses = [(x, 0) for x in range(n_blocks)]
    poses = [(x, 0) for x in range(n_blocks+1)]
    #poses = [(x, 0) for x in range(n_poses)]
    conf = (0, 5)
    goal_conf = (5, 5)

    #objects = []
    init = [
        ('Conf', conf),
        ('Conf', goal_conf),
        ('AtConf', conf),
        ('HandEmpty',),
        #(NOT, ('Holding', blocks[0])),  # Confirms that not
        #(EQ, (TOTAL_COST,), 0),
    ]

    init += [('Block', b) for b in blocks]
    init += [('Pose', p) for p in poses]
    init += [('AtPose', b, p) for b, p in zip(blocks, poses)]

    #goal = ('AtConf', conf)
    goal = ('AtConf', goal_conf)
    #goal = (AND,
    #        ('Holding', blocks[0]),
    #        (NOT, ('HandEmpty',)))
    goal = ('AtPose', blocks[0], poses[1])

    domain_pddl = DOMAIN_PDDL
    stream_pddl = STREAM_PDDL
    streams = {
        #'sample-pose': (lambda: (((x, 0),) for x in range(n_blocks, n_poses))),
        'sample-pose': from_gen_fn(lambda: (((x, 0),) for x in range(len(poses), n_poses))),
        #'inverse-kinematics': (lambda p: iter([((p[0], p[1]+1),)])),
        'inverse-kinematics':  from_fn(lambda p: ((p[0], p[1] + 1),)),

    }
    constants = {}

    return init, goal, domain_pddl, stream_pddl, streams, constants

def main():
    problem = get_problem1()
    plan, init = solve_finite(problem)
    #plan, init = solve_exhaustive(problem)
    print(plan)
    print(init)

def brainstorm():
    #Block = 'Block'
    #Block = Predicate('Block')

    block0 = 'block0'
    p0 = (0, 0)

    def ik(p):
        return p,

    gen_fns = { # TODO: return
        'inverse-kinematics': ik, # TODO: include various options as well
    }

    # TODO: the more I can separate representation language from parsing, the better

    #objects = []
    init = [
        ('Block', block0),
        ('Pose', p0),
        ('AtPose', block0, p0),
        ('HandEmpty',),
    ]
    #goal = [
    #    ('Holding', block0),
    #    ('not', ('Holding', block0)),
    #    (NOT, ('Holding', block0)),
    #]
    goal = (AND,
            ('Holding', block0),
            ('HandEmpty',),
            )

    # TODO: no string constants that aren't associated with a value


    for atom in init:
        args = atom[1:]
        for arg in args:
            obj = Object.from_value(arg)
            print(obj)
        print(convert_head(atom))



    # TODO: can make rule streams that automatically infer object (types in general)
    # TODO: apply the constant mapping here as well
    streams = [
        Stream(inp='?p', domain='(Pose ?p)',
               fn=lambda p: (p,),
               out='?q', certifed='(Kin ?q ?p)'),

        RuleStream(inp='?q ?p', domain='(Kin ?q ?p)', # TODO: infer these from types
               certifed='(and (Pose ?p) (Conf ?q))'),

        Stream(inp='?q1 ?q2', domain='(and (Conf ?q1) (Conf ?q2))',
               fn=lambda q1, q2: (abs(q2 - q1),),
               out='?d', certifed='(= (Distance ?q1 ?q2) ?d)'),
    ]
    # TODO: the difference between predicates and functions is that functions must be evaluated
    # While predicates are always assumed to be false

    # Initial state conditional effects
    streams = [
        Stream(inp='?b', domain='(and ())',
               fn=lambda b: ([((i, 0),)] for i in range(5)),
               out='?p', certifed='( )'),
    ]
    # TODO: maybe I take an even more basic view where certified are just the statements to write down completing the values
    # TODO: then I could have functions and streams do equivalent things
    # TODO: name whatever the output of the stream is but don't require that it be an object.
    # TODO: can make a wrapper around the stream fn to simplify what its behavior is

    # (Predicate ?inp1 ?inp2 ?out1 ?out2)
    # (= (Function) ?out) # Number, True, False

    # TODO: parse streams like a pddl thing
    # TODO: can map stream name to function and any parameters

if __name__ == '__main__':
    main()