from collections import namedtuple

import numpy as np
import string

GROUND_NAME = 'grey'
BLOCK_WIDTH = 2
BLOCK_HEIGHT = BLOCK_WIDTH

SUCTION_HEIGHT = 1.
GRASP = -np.array([0, BLOCK_HEIGHT + SUCTION_HEIGHT/2]) # TODO: side grasps
CARRY_Y = 2*BLOCK_WIDTH+SUCTION_HEIGHT
APPROACH = -np.array([0, CARRY_Y]) - GRASP

MOVE_COST = 10.
COST_PER_DIST = 1.


def interval_contains(i1, i2):
    """
    :param i1: The container interval
    :param i2: The possibly contained interval
    :return:
    """
    return (i1[0] <= i2[0]) and (i2[1] <= i1[1])


def interval_overlap(i1, i2):
    return (i2[0] <= i1[1]) and (i1[0] <= i2[1])


def get_block_interval(b, p):
    return p[0]*np.ones(2) + np.array([-BLOCK_WIDTH, +BLOCK_WIDTH]) / 2.

##################################################

def collision_test(b1, p1, b2, p2):
    return interval_overlap(get_block_interval(b1, p1), get_block_interval(b2, p2))


def distance_fn(q1, q2):
    ord = 1  # 1 | 2
    return MOVE_COST + COST_PER_DIST*np.linalg.norm(q2 - q1, ord=ord)


def inverse_kin_fn(b, p, g):
    q = p - g
    #return (q,)
    a = q - APPROACH
    return (a,)


def unreliable_ik_fn(b, p):
    # For testing the algorithms
    while 1e-2 < np.random.random():
        yield None
    yield inverse_kin_fn(b, p)


def get_region_test(regions):
    def test(b, p, r):
        return interval_contains(regions[r], get_block_interval(b, p))
    return test


def sample_region(b, region):
    x1, x2 = np.array(region, dtype=float) - get_block_interval(b, np.zeros(2))
    if x2 < x1:
        return None
    x = np.random.uniform(x1, x2)
    return np.array([x, 0])


def rejection_sample_region(b, region, placed={}, max_attempts=10):
    for _ in range(max_attempts):
        p = sample_region(b, region)
        if p is None:
            break
        if not any(collision_test(b, p, b2, p2) for b2, p2 in placed.items()):
            return p
    return None


def rejection_sample_placed(block_poses={}, block_regions={}, regions={}, max_attempts=10):
    assert(not set(block_poses.keys()) & set(block_regions.keys()))
    for _ in range(max_attempts):
        placed = block_poses.copy()
        remaining = block_regions.items()
        np.random.shuffle(remaining)
        for b, r in remaining:
            p = rejection_sample_region(b, regions[r], placed)
            if p is None:
                break
            placed[b] = p
        else:
            return placed
    return None


def get_pose_gen(regions):
    def gen_fn(b, r):
        while True:
            p = sample_region(b, regions[r])
            if p is None:
                break
            yield (p,)
    return gen_fn


def plan_motion(q1, q2):
    x1, y1 = q1
    x2, y2 = q2
    t = [q1,
         np.array([x1, CARRY_Y]),
         np.array([x2, CARRY_Y]),
         q2]
    return (t,)

##################################################

TAMPState = namedtuple('TAMPState', ['robot_confs', 'holding', 'block_poses'])
TAMPProblem = namedtuple('TAMPProblem', ['initial', 'regions', 'goal_conf', 'goal_regions'])

REGION_NAME = 'red'
INITIAL_CONF = np.array([-5, CARRY_Y + 1])
#GOAL_CONF = None
GOAL_CONF = INITIAL_CONF

REGIONS = {
    GROUND_NAME: (-10, 10),
    REGION_NAME: (5, 10),
    #REGION_NAME: (7.5, 10),
}

def make_blocks(num):
    #return ['b{}'.format(i) for i in range(num)]
    return [string.ascii_uppercase[i] for i in range(num)]

def mirror(n_blocks=1, n_robots=2):
    confs = [INITIAL_CONF, np.array([-1, 1])*INITIAL_CONF]
    robots = ['r{}'.format(x) for x in range(n_robots)]
    initial_confs = dict(zip(robots, confs))

    n_goals = n_blocks
    poses = [np.array([-(BLOCK_WIDTH + 1) * x - BLOCK_WIDTH, 0]) for x in range(n_blocks)]
    blocks = make_blocks(len(poses))
    goal_poses = [-pose for pose in poses[:n_goals]]

    initial = TAMPState(initial_confs, {}, dict(zip(blocks, poses)))
    goal_regions = {block: pose for block, pose in zip(blocks, goal_poses)}

    return TAMPProblem(initial, REGIONS, GOAL_CONF, goal_regions)

def tight(n_blocks=2, n_goals=2, n_robots=1):
    confs = [INITIAL_CONF, np.array([-1, 1])*INITIAL_CONF]
    robots = ['r{}'.format(x) for x in range(n_robots)]
    initial_confs = dict(zip(robots, confs))

    #poses = [np.array([(BLOCK_WIDTH + 1)*x, 0]) for x in range(n_blocks)]
    poses = [np.array([-(BLOCK_WIDTH + 1) * x, 0]) for x in range(n_blocks)]
    #poses = [sample_region(b, regions[GROUND]) for b in blocks]
    blocks = make_blocks(len(poses))

    initial = TAMPState(initial_confs, {}, dict(zip(blocks, poses)))
    goal_regions = {block: REGION_NAME for block in blocks[:n_goals]}

    return TAMPProblem(initial, REGIONS, GOAL_CONF, goal_regions)

def blocked(n_blocks=3, n_robots=1, deterministic=True):
    confs = [INITIAL_CONF, np.array([-1, 1])*INITIAL_CONF]
    robots = ['r{}'.format(x) for x in range(n_robots)]
    initial_confs = dict(zip(robots, confs))

    blocks = make_blocks(n_blocks)
    if deterministic:
        lower, upper = REGIONS[GROUND_NAME]
        poses = [np.zeros(2), np.array([7.5, 0])]
        poses.extend(np.array([lower + BLOCK_WIDTH/2 + (BLOCK_WIDTH + 1) * x, 0])
                     for x in range(n_blocks-len(poses)))
        block_poses = dict(zip(blocks, poses))
    else:
        block_regions = {blocks[0]: GROUND_NAME}
        block_regions.update({b: REGION_NAME for b in blocks[1:2]})
        block_regions.update({b: GROUND_NAME for b in blocks[2:]})
        block_poses = rejection_sample_placed(block_regions=block_regions, regions=REGIONS)

    initial = TAMPState(initial_confs, {}, block_poses)
    goal_regions = {blocks[0]: 'red'}

    return TAMPProblem(initial, REGIONS, GOAL_CONF, goal_regions)


#def blocked2(n_blocks=0, **kwargs):
#    lower, upper = REGIONS[GROUND_NAME]
#    poses = [np.zeros(2), np.array([6.5, 0]), np.array([8.5, 0])]
#    poses.extend(np.array([lower + BLOCK_WIDTH/2 + (BLOCK_WIDTH + 1) * x, 0])
#                 for x in range(n_blocks-len(poses)))
#    blocks = make_blocks(len(poses))
#    block_poses = dict(zip(blocks, poses))
#    initial = TAMPState(INITIAL_CONF, None, block_poses)
#    goal_regions = {blocks[0]: 'red'}
#
#    return TAMPProblem(initial, REGIONS, GOAL_CONF, goal_regions)

PROBLEMS = [
    mirror,
    tight,
    blocked,
    #blocked2,
]

##################################################

def draw_state(viewer, state, colors):
    # TODO: could draw the current time
    viewer.clear_state()
    #viewer.draw_environment()
    for robot, conf in state.robot_confs.items():
        viewer.draw_robot(*conf, name=robot)
    for block, pose in state.block_poses.items():
        x, y = pose
        viewer.draw_block(x, y, BLOCK_WIDTH, BLOCK_HEIGHT,
                          name=block, color=colors[block])
    for robot, holding in state.holding.items():
        block, grasp = holding
        x, y = state.robot_confs[robot] + grasp
        viewer.draw_block(x, y, BLOCK_WIDTH, BLOCK_HEIGHT,
                          name=block, color=colors[block])
    viewer.tk.update()

def get_random_seed():
    return np.random.get_state()[1][0]

##################################################

def apply_action(state, action):
    robot_confs, holding, block_poses = state
    # TODO: don't mutate block_poses?
    name, args = action[:2]
    if name == 'move':
        robot, _, traj, _ = args
        #traj = plan_motion(*args)[0] if len(args) == 2 else args[1]
        for conf in traj[1:]:
            robot_confs[robot] = conf
            yield TAMPState(robot_confs, holding, block_poses)
    elif name == 'pick':
        # TODO: approach and retreat trajectory
        robot, block, _, grasp, _ = args
        holding[robot] = (block, grasp)
        del block_poses[block]
        yield TAMPState(robot_confs, holding, block_poses)
    elif name == 'place':
        robot, block, pose, _, _ = args
        del holding[robot]
        block_poses[block] = pose
        yield TAMPState(robot_confs, holding, block_poses)
    else:
        raise ValueError(name)

def prune_duplicates(traj):
    # TODO: could use the more general sparcify function
    new_traj = [traj[0]]
    for conf in traj[1:]:
        if 0 < np.linalg.norm(np.array(conf) - np.array(new_traj[-1])):
            new_traj.append(conf)
    return new_traj

def get_value_at_time(traj, fraction):
    waypoints = prune_duplicates(traj)
    if len(waypoints) == 1:
        return waypoints[0]
    distances = [0.] + [np.linalg.norm(np.array(q2) - np.array(q1))
                        for q1, q2 in zip(waypoints, waypoints[1:])]
    cum_distances = np.cumsum(distances)
    cum_fractions = np.minimum(cum_distances / cum_distances[-1], np.ones(cum_distances.shape))
    index = np.digitize(fraction, cum_fractions, right=False)
    if index == len(waypoints):
        index -= 1
    waypoint_fraction = (fraction - cum_fractions[index - 1]) / (cum_fractions[index] - cum_fractions[index - 1])
    waypoint1, waypoint2 = np.array(waypoints[index - 1]), np.array(waypoints[index])
    conf = (1 - waypoint_fraction) * waypoint1 + waypoint_fraction * waypoint2
    #if np.isnan(conf).any():
    #    print(distances, fraction)
    #    raw_input()
    return conf

def update_state(state, action, t):
    robot_confs, holding, block_poses = state
    name, args, start, duration = action
    fraction = float(t) / duration
    fraction = max(0, min(fraction, 1))
    assert 0 <= fraction <= 1
    threshold = 0.5
    if name == 'move':
        robot, _, traj, _ = args
        robot_confs[robot] = get_value_at_time(traj, fraction)
    elif name == 'pick':
        robot, block, pose, grasp, conf = args
        traj = [conf, pose - grasp]
        if fraction < threshold:
            robot_confs[robot] = get_value_at_time(traj, fraction / threshold)
        else:
            holding[robot] = (block, grasp)
            block_poses.pop(block, None)
            robot_confs[robot] = get_value_at_time(traj[::-1], (fraction - threshold) / (1 - threshold))
    elif name == 'place':
        robot, block, pose, grasp, conf = args
        traj = [conf, pose - grasp]
        if fraction < threshold:
            robot_confs[robot] = get_value_at_time(traj, fraction / threshold)
        else:
            holding.pop(robot, None)
            block_poses[block] = pose
            robot_confs[robot] = get_value_at_time(traj[::-1], (fraction - threshold) / (1 - threshold))
    elif name == 'cook':
        pass
    else:
        raise ValueError(name)
    return TAMPState(robot_confs, holding, block_poses)
