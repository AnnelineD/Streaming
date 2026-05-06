from random import random

from src.expr import Var


def random_set_env(variables, universe=None, rng=None):
    rng = rng or random
    universe = universe or tuple("123456789ABCDEF")

    return {
        v: set(rng.sample(universe, rng.randint(0, len(universe))))
        for v in variables
    }


def rand_expr(rng, names, depth, stop_prob=0.3):
    if depth == 0 or rng.random() < stop_prob:
        return Var(rng.choice(names))

    op = rng.choices(
        ["&", "|", "-"],
        weights=[3, 3, 4],   # bias toward difference
    )[0]

    left = rand_expr(rng, names, depth - 1, stop_prob)
    right = rand_expr(rng, names, depth - 1, stop_prob)

    if op == "&":
        return left & right
    elif op == "|":
        return left | right
    else:
        return left - right