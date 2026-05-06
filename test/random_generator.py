import string
from random import random

from src.clause import Clause, DNF
from src.expr import Var
from src.trie.trie import bittrieset


def generate_var_names(n):
    assert n <= 26  # limited letters in the alphabet
    letters = list(string.ascii_lowercase)
    return letters[:n]

def random_set_env(variables, universe=None, rng=None):
    rng = rng or random
    universe = universe or tuple("123456789ABCDEF")

    return {
        v: set(rng.sample(universe, rng.randint(0, len(universe))))
        for v in variables
    }


def random_trie_path(rng):
    return "".join(rng.choice("01") for _ in range(rng.randint(1, 6)))

def random_trie_set(rng, size=50):
    pool = set()
    while len(pool) < size:
        pool.add(random_trie_path(rng))
    return list(pool)

def random_trie_env_for_clauses(clauses, variables, rng):
    pool = random_trie_set(rng)
    env = {v: set() for v in variables}

    # inject overlap per clause
    for clause in clauses:
        shared = rng.sample(pool, rng.randint(1, 3))
        for v in clause.P:
            env[v].update(shared)

    # add noise
    for v in variables:
        env[v].update(rng.sample(pool, rng.randint(0, 5)))

    # convert plain sets -> bittrieset
    return {v: bittrieset(*paths) for v, paths in env.items()}

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


def random_clause(rng, variables, min_pos=1, max_pos=3, min_neg=0, max_neg=2):
    vars_list = list(variables)

    p_size = rng.randint(min_pos, min(max_pos, len(vars_list)))
    P = set(rng.sample(vars_list, p_size))

    remaining = [v for v in vars_list if v not in P]
    max_neg_allowed = min(max_neg, len(remaining))
    min_neg_allowed = min(min_neg, max_neg_allowed)
    n_size = rng.randint(min_neg_allowed, max_neg_allowed) if remaining else 0
    N = set(rng.sample(remaining, n_size))

    return Clause.make(P, N)


def random_dnf(rng, *, variable_count=5, clause_count=3, min_pos=1, max_pos=3, min_neg=0, max_neg=2,):
    variables = generate_var_names(variable_count)
    clauses = [
        random_clause(rng, variables, min_pos=min_pos, max_pos=max_pos, min_neg=min_neg, max_neg=max_neg,)
        for _ in range(clause_count)
    ]
    return DNF(clauses), variables