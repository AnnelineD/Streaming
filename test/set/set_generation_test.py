import random
import unittest
from abc import ABC, abstractmethod
from collections import defaultdict
from contextlib import redirect_stdout
from io import StringIO

from src.clause import DNF, Clause
from src.set.set_generation import graph_generation #, naive
from src.set.synth import Sink, Source, Graph

from test.random_generator import random_set_env


CASES = [
    {
        "name": "clause",
        "clauses": [
            Clause.make({"a", "b", "c", "d"}, {"e", "f"}),
        ],
        "env": {
            "a": {"1", "3", "A", "B", "C"},
            "b": {"2", "3", "A", "B"},
            "c": {"1", "3", "4", "A", "B"},
            "d": {"1", "3", "A", "B"},
            "e": {"1", "A"},
            "f": {"3"},
        },
        "dependency_names": {
            "a": ("b", "c", "d", "e", "f"),
            "b": ("a", "c", "d", "e", "f"),
            "c": ("a", "b", "d", "e", "f"),
            "d": ("a", "b", "c", "e", "f"),
            "e": ("a", "b", "c", "d", "f"),
            "f": ("a", "b", "c", "d", "e"),
        },
        "variables": ["a", "b", "c", "d", "e", "f"],
        "trials": 100,
        "seed": 10,
    },
    {
        "name": "two_results_non_overlapping",
        "clauses": [
            Clause.make({"a", "b"}, {"c"}),
            Clause.make({"d"}, {"e"}),
        ],
        "env": {
            "a": {"1", "3", "A", "B", "C"},
            "b": {"2", "3", "A", "B"},
            "c": {"1", "3", "4", "A", "B"},
            "d": {"1", "3", "A", "B"},
            "e": {"1", "A"},
        },
        "variables": ["a", "b", "c", "d", "e"],
        "trials": 100,
        "seed": 11,
    },
    {
        "name": "overlapping_intersections",
        "clauses": [
            Clause.make({"a", "c"}, {"d"}),
            Clause.make({"b", "c"}, {"e"}),
        ],
        "env": {
            "a": {"1", "3", "A", "B", "C"},
            "b": {"2", "3", "A", "B"},
            "c": {"1", "3", "4", "A", "B"},
            "d": {"1", "3", "B"},
            "e": {"1", "A"},
        },
        "dependency_names": {
            "c": ("a", "b"),
        },
        "variables": ["a", "b", "c", "d", "e"],
        "trials": 100,
        "seed": 12,
    },
    {
        "name": "first_formula",
        "clauses": [
            Clause.make({"a", "c"}, {"d"}),
            Clause.make({"b", "c"}, {"d"}),
        ],
        "env": {
            "a": {"1", "B", "C"},
            "b": {"2", "3", "A"},
            "c": {"3", "4", "A", "B"},
            "d": {"1", "A"},
        },
        "dependency_names": {
            "c": ("a", "b"),
        },
        "variables": ["a", "b", "c", "d"],
        "trials": 100,
        "seed": 13,
    },
    {
        "name": "random_original",
        "clauses": [
            Clause.make({"a", "b"}, {"c"}),
            Clause.make({"b"}, {"c"}),
        ],
        "env": {
            "a": {"1"},
            "b": {"3", "4", "F"},
            "c": {"2", "C"},
            "d": {"1", "2", "7", "B", "C"},
            "e": {"4"},
        },
        "dependency_names": {
            "a": ("b",),
            "b": ("a",),
            "c": ("a", "b"),
        },
        "singleton_names": ("b",),
        "variables": ["a", "b", "c", "d", "e"],
        "trials": 100,
        "seed": 14,
    },
    {
        "name": "singleton",
        "clauses": [
            Clause.make({"a", "b"}, {"c"}),
            Clause.make({"b"}, {"d"}),
        ],
        "env": {
            "a": {"1", "4", "5", "6"},
            "b": {"2", "4", "5", "6", "7"},
            "c": {"3", "5"},
            "d": {"5", "6"},
        },
        "dependency_names": {
            "a": ("b",),
            "b": ("a",),
            "c": ("a", "b"),
            "d": ("b",),
        },
        "singleton_names": ("b",),
        "variables": ["a", "b", "c", "d"],
        "trials": 100,
        "seed": 15,
    },
]


class FormulaTestBase(unittest.TestCase, ABC):
    maxDiff = None
    CASES = CASES

    # -------------------------
    # Pretty printing helpers
    # -------------------------

    def format_env(self, env: dict[str, set]) -> str:
        return ", ".join(
            f"{k}={{{', '.join(sorted(v))}}}"
            for k, v in sorted(env.items())
        )

    def repr_env(self, env: dict[str, set]) -> str:
        lines = ["{"]
        for name in sorted(env):
            elems = ", ".join(repr(x) for x in sorted(env[name]))
            lines.append(f'    "{name}": {{{elems}}},')
        lines.append("}")
        return "\n".join(lines)

    def expected_result(self, clauses, env):
        wanted = set()
        for clause in clauses:
            wanted |= clause.eval(env)
        return wanted

    def assert_formula_result(
        self,
        *,
        wanted,
        actual,
        clauses,
        env,
        seed=None,
        trial=None,
        case_name=None,
        extra="",
    ):
        self.assertSetEqual(
            wanted,
            actual,
            msg=(
                f"\ncase={case_name}"
                f"\nseed={seed}"
                f"\ntrial={trial}"
                f"\nclauses={clauses}"
                f"\nenv={self.repr_env(env)}"
                f"\nwanted={sorted(wanted)}"
                f"\nactual={sorted(actual)}"
                f"{extra}"
            ),
        )


    # -------------------------
    # Random clause helpers
    # -------------------------

    def random_clause(self, rng, variables, min_pos=1, max_pos=3, min_neg=0, max_neg=2):
        vars_list = list(variables)

        p_size = rng.randint(min_pos, min(max_pos, len(vars_list)))
        P = set(rng.sample(vars_list, p_size))

        remaining = [v for v in vars_list if v not in P]
        max_neg_allowed = min(max_neg, len(remaining))
        min_neg_allowed = min(min_neg, max_neg_allowed)
        n_size = rng.randint(min_neg_allowed, max_neg_allowed) if remaining else 0
        N = set(rng.sample(remaining, n_size))

        return Clause.make(P, N)

    def random_clauses(
        self,
        rng,
        *,
        variable_count=5,
        clause_count=3,
        min_pos=1,
        max_pos=3,
        min_neg=0,
        max_neg=2,
    ):
        variables = [chr(ord("a") + i) for i in range(variable_count)]
        clauses = [
            self.random_clause(
                rng,
                variables,
                min_pos=min_pos,
                max_pos=max_pos,
                min_neg=min_neg,
                max_neg=max_neg,
            )
            for _ in range(clause_count)
        ]
        return clauses, variables

    # -------------------------
    # Shared runners
    # -------------------------

    @abstractmethod
    def run_formula_case(
        self,
        clauses,
        env,
        *,
        dependency_names=None,
        singleton_names=None,
        debug_py=False,
        debug_dot=False,
        seed=None,
        trial=None,
        case_name=None,
    ):
        raise NotImplementedError

    def run_random_envs(
        self,
        clauses,
        *,
        dependency_names=None,
        singleton_names=None,
        variables=None,
        trials=50,
        seed=0,
        case_name=None,
    ):
        if variables is None:
            variables = sorted(set().union(*(c.P | c.N for c in clauses)))

        rng = random.Random(seed)

        for i in range(trials):
            env = random_set_env(variables, rng=rng)

            with self.subTest(case=case_name, i=i, seed=seed, env=self.format_env(env)):
                self.run_formula_case(
                    clauses,
                    env,
                    dependency_names=dependency_names,
                    singleton_names=singleton_names,
                    seed=seed,
                    trial=i,
                    case_name=case_name,
                )

    def run_random_formulas(
        self,
        *,
        formula_trials=50,
        env_trials=10,
        seed=0,
        variable_count=6,
        clause_count=4,
        min_pos=1,
        max_pos=3,
        min_neg=0,
        max_neg=2,
        case_name="random_formulas",
    ):
        rng = random.Random(seed)

        for i in range(formula_trials):
            clauses, variables = self.random_clauses(
                rng,
                variable_count=variable_count,
                clause_count=clause_count,
                min_pos=min_pos,
                max_pos=max_pos,
                min_neg=min_neg,
                max_neg=max_neg,
            )

            for j in range(env_trials):
                env = random_set_env(variables, rng=rng)

                with self.subTest(case=case_name, formula_trial=i, env_trial=j, seed=seed):
                    self.run_formula_case(
                        clauses,
                        env,
                        seed=seed,
                        trial=(i, j),
                        case_name=case_name,
                    )

    def run_case_with_original_and_random(self, case):
        name = case["name"]
        clauses = case["clauses"]
        env = case["env"]
        dependency_names = case.get("dependency_names", {})
        singleton_names = case.get("singleton_names", ())
        variables = case.get("variables")
        trials = case.get("trials", 50)
        seed = case.get("seed", 0)

        with self.subTest(case=name, kind="original"):
            self.run_formula_case(
                clauses,
                env,
                dependency_names=dependency_names,
                singleton_names=singleton_names,
                case_name=name,
            )

        self.run_random_envs(
            clauses,
            dependency_names=dependency_names,
            singleton_names=singleton_names,
            variables=variables,
            trials=trials,
            seed=seed,
            case_name=name,
        )

"""
class TestGraphGeneration(FormulaTestBase):
    def run_formula_case(
        self,
        clauses,
        env,
        *,
        dependency_names=None,
        singleton_names=None,
        debug_py=False,
        debug_dot=False,
        seed=None,
        trial=None,
        case_name=None,
    ):
        dependency_names = dependency_names or {}
        singleton_names = singleton_names or ()

        wanted = self.expected_result(clauses, env)

        f = Formula(clauses)
        g = Graph()
        s0, s1, s2 = g.states("s0", "s1", "s2")
        g.init = s0

        names = sorted(env.keys())
        pulled = g.sources(*names)
        source_map = dict(zip(names, pulled))

        s0.to(s1, pull=tuple(pulled))

        dependencies = defaultdict(tuple)
        for name, deps in dependency_names.items():
            dependencies[name] = tuple(source_map[d] for d in deps)

        singletons = tuple(source_map[name] for name in singleton_names)
        _ = singletons

        g = f.make_graph2(g, s1, s2, dependencies)

        if debug_dot:
            g.dot()

        exec_env = {n: Source(n, env[n]) for n in names}
        exec_env["r"] = Sink()

        s = StringIO()
        with redirect_stdout(s):
            g.py()

        generated_code = s.getvalue()

        if debug_py:
            print(generated_code)

        try:
            exec(generated_code, exec_env, exec_env)
        except IndexError:
            print("stopped by exhaustion")

        actual = set(exec_env["r"].data)

        self.assert_formula_result(
            wanted=wanted,
            actual=actual,
            clauses=clauses,
            env=env,
            seed=seed,
            trial=trial,
            case_name=case_name,
            extra=f"\ngenerated_code=\n{generated_code}",
        )

    def test_clause(self):
        self.run_case_with_original_and_random(self.CASES[0])

    def test_two_results_non_overlapping(self):
        self.run_case_with_original_and_random(self.CASES[1])

    def test_overlapping_intersections(self):
        self.run_case_with_original_and_random(self.CASES[2])

    def test_first_formula(self):
        self.run_case_with_original_and_random(self.CASES[3])

    def test_random_original(self):
        self.run_case_with_original_and_random(self.CASES[4])

    def test_singleton(self):
        self.run_case_with_original_and_random(self.CASES[5])

    def test_random_formulas(self):
        self.run_random_formulas(
            formula_trials=50,
            env_trials=10,
            seed=123,
            variable_count=6,
            clause_count=4,
        )


class TestNaiveGeneration(FormulaTestBase):
    def run_formula_case(
        self,
        clauses,
        env,
        *,
        dependency_names=None,
        singleton_names=None,
        debug_py=False,
        debug_dot=False,
        seed=None,
        trial=None,
        case_name=None,
    ):
        wanted = self.expected_result(clauses, env)
        actual = set(naive(Formula(clauses), env).data)

        self.assert_formula_result(
            wanted=wanted,
            actual=actual,
            clauses=clauses,
            env=env,
            seed=seed,
            trial=trial,
            case_name=case_name,
        )

    def test_clause(self):
        self.run_case_with_original_and_random(self.CASES[0])

    def test_two_results_non_overlapping(self):
        self.run_case_with_original_and_random(self.CASES[1])

    def test_overlapping_intersections(self):
        self.run_case_with_original_and_random(self.CASES[2])

    def test_first_formula(self):
        self.run_case_with_original_and_random(self.CASES[3])

    def test_random_original(self):
        self.run_case_with_original_and_random(self.CASES[4])

    def test_singleton(self):
        self.run_case_with_original_and_random(self.CASES[5])

    def test_random_formulas(self):
        self.run_random_formulas(
            formula_trials=50,
            env_trials=10,
            seed=123,
            variable_count=6,
            clause_count=4,
        )
"""

class TestGraphGeneration2(FormulaTestBase):
    def run_formula_case(
        self,
        clauses,
        env,
        *,
        dependency_names=None,
        singleton_names=None,
        debug_py=False,
        debug_dot=False,
        seed=None,
        trial=None,
        case_name=None,
    ):
        dependency_names = dependency_names or {}
        singleton_names = singleton_names or ()

        wanted = self.expected_result(clauses, env)

        f = DNF(clauses)
        g = graph_generation(f)

        names = sorted(f.vars())
        srcs = g.sources(*names)
        source_map = dict(zip(names, srcs))

        dependencies = defaultdict(tuple)
        for name, deps in dependency_names.items():
            dependencies[name] = tuple(source_map[d] for d in deps)

        singletons = tuple(source_map[name] for name in singleton_names)
        _ = dependencies
        _ = singletons

        if debug_dot:
            g.dot()

        exec_env = {n: Source(n, env[n]) for n in names}
        exec_env["r"] = Sink()

        s = StringIO()
        with redirect_stdout(s):
            g.py()

        generated_code = s.getvalue()

        if debug_py:
            print(generated_code)

        try:
            exec(generated_code, exec_env, exec_env)
        except IndexError:
            print("stopped by exhaustion")

        actual = set(exec_env["r"].data)

        self.assert_formula_result(
            wanted=wanted,
            actual=actual,
            clauses=clauses,
            env=env,
            seed=seed,
            trial=trial,
            case_name=case_name,
            extra=f"\ngenerated_code=\n{generated_code}",
        )

    def test_clause(self):
        self.run_case_with_original_and_random(self.CASES[0])

    def test_two_results_non_overlapping(self):
        self.run_case_with_original_and_random(self.CASES[1])

    def test_overlapping_intersections(self):
        self.run_case_with_original_and_random(self.CASES[2])

    def test_first_formula(self):
        self.run_case_with_original_and_random(self.CASES[3])

    def test_random_original(self):
        self.run_case_with_original_and_random(self.CASES[4])

    def test_singleton(self):
        self.run_case_with_original_and_random(self.CASES[5])

    def test_random_formulas(self):
        self.run_random_formulas(
            formula_trials=100,
            env_trials=20,
            seed=851,
            variable_count=6,
            clause_count=4,
        )

if __name__ == "__main__":
    unittest.main()