import random
import unittest
from abc import ABC, abstractmethod
from contextlib import redirect_stdout
from io import StringIO

from src.clause import Clause, DNF
from src.trie.trie import bittrieset
from src.trie.trie_generation import TrieExecution
from src.trie.trie_synth import Source, Sink
from test.random_generator import random_dnf

CASES = [
    {
        "name": "clause",
        "clauses": [
            Clause.make({"a", "b", "c", "d"}, {"e", "f"}),
        ],
        "env": {
            "a": {"0", "001", "011", "1011", "11000"},
            "b": {"001", "011", "111", "11000"},
            "c": {"0", "001", "011", "100", "11000"},
            "d": {"0", "001", "011", "11000"},
            "e": {"0", "001"},
            "f": {"011"},
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
            "a": {"0", "011", "1011", "11000", "11111"},
            "b": {"001", "011", "1011", "11000"},
            "c": {"0", "011", "100", "1011", "11000"},
            "d": {"0", "011", "1011", "11000"},
            "e": {"0", "1011"},
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
            "a": {"0", "011", "1011", "11000", "11111"},
            "b": {"001", "011", "1011", "11000"},
            "c": {"0", "011", "100", "1011", "11000"},
            "d": {"0", "011", "11000"},
            "e": {"0", "1011"},
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
            "a": {"0", "1011", "11111"},
            "b": {"001", "011", "11000"},
            "c": {"011", "100", "1011", "11000"},
            "d": {"0", "1011"},
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
            "a": {"0"},
            "b": {"011", "100", "11111"},
            "c": {"001", "1011"},
            "d": {"0", "001", "111", "11000", "1011"},
            "e": {"100"},
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
            "a": {"0", "100", "101", "110"},
            "b": {"001", "100", "101", "110", "111"},
            "c": {"011", "101"},
            "d": {"101", "110"},
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

    def format_env(self, env):
        return ", ".join(
            f"{k}={{{', '.join(sorted(v))}}}"
            for k, v in sorted(env.items())
        )

    def repr_env(self, env):
        lines = ["{"]
        for name in sorted(env):
            elems = ", ".join(repr(x) for x in sorted(env[name]))
            lines.append(f'    "{name}": {{{elems}}},')
        lines.append("}")
        return "\n".join(lines)


    def assert_formula_result(self, *, wanted, actual, clauses, env, **meta):
        print(f"\nclauses={clauses}", f"\nenv={self.repr_env(env)}")

        self.assertEqual(
            wanted,
            actual,
            msg=(
                f"\ncase={meta.get('case_name')}"
                f"\nseed={meta.get('seed')}"
                f"\ntrial={meta.get('trial')}"
                f"\nclauses={clauses}"
                f"\nenv={self.repr_env(env)}"
                f"\nwanted={sorted(wanted)}"
                f"\nactual={sorted(actual)}"
            ),
        )

    # -------- random path generation --------

    def random_path(self, rng):
        return "".join(rng.choice("01") for _ in range(rng.randint(1, 6)))

    def random_pool(self, rng, size=50):
        pool = set()
        while len(pool) < size:
            pool.add(self.random_path(rng))
        return list(pool)

    def random_env_for_clauses(self, clauses, variables, rng):
        pool = self.random_pool(rng)
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

    # -------- runners --------

    @abstractmethod
    def run_formula_case(self, clauses, env, **kwargs):
        pass

    def run_random_envs(self, clauses, *, variables, trials, seed, case_name, **kwargs):
        rng = random.Random(seed)

        for i in range(trials):
            env = self.random_env_for_clauses(clauses, variables, rng)

            with self.subTest(case=case_name, i=i):
                self.run_formula_case(
                    clauses,
                    env,
                    trial=i,
                    seed=seed,
                    case_name=case_name,
                )

    def run_case_with_original_and_random(self, case):
        name = case["name"]

        # original
        # with self.subTest(case=name, kind="original"):
        #     self.run_formula_case(
        #         case["clauses"],
        #         case["env"],
        #         case_name=name,
        #     )

        # random
        self.run_random_envs(
            case["clauses"],
            variables=case.get("variables"),
            trials=case.get("trials", 50),
            seed=case.get("seed", 0),
            case_name=name,
        )

    def run_random_formulas(
            self,
            *,
            formula_trials=50,
            env_trials=20,
            seed=0,
            variable_count=5,
            clause_count=3,
            min_pos=1,
            max_pos=3,
            min_neg=0,
            max_neg=2,
            case_name="random_formula",
    ):
        rng = random.Random(seed)

        for i in range(formula_trials):
            dnf, variables = random_dnf(
                rng,
                variable_count=variable_count,
                clause_count=clause_count,
                min_pos=min_pos,
                max_pos=max_pos,
                min_neg=min_neg,
                max_neg=max_neg,
            )

            print(clauses)

            for j in range(env_trials):
                env = self.random_env_for_clauses(clauses, variables, rng)

                with self.subTest(case=case_name, formula_trial=i, env_trial=j):
                    self.run_formula_case(
                        clauses,
                        env,
                        trial=(i, j),
                        seed=seed,
                        case_name=case_name,
                    )


class TestNaiveGeneration(FormulaTestBase):
    def run_formula_case(self, clauses, env, **meta):
        formula = DNF(clauses)
        wanted = set(formula.eval(env).keys_iterator())
        print(wanted)
        actual = set(TrieExecution.naive(DNF(clauses), env).data)

        self.assert_formula_result(
            wanted=wanted,
            actual=actual,
            clauses=clauses,
            env=env,
            **meta,
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
            seed=456,
            variable_count=6,
            clause_count=4,
        )

class TestStateMachineGeneration(FormulaTestBase):
    def run_formula_case(self, clauses, env, **meta):
        formula = DNF(clauses)
        wanted = list(formula.eval(env).keys_iterator())
        print(wanted)

        g = TrieExecution.create_state_machine(formula)

        names = sorted(formula.vars())
        srcs = g.sources(*names)
        source_map = dict(zip(names, srcs))

        exec_env = {n: Source(n, env[n]) for n in names}
        exec_env["r"] = Sink()

        print(g.dot())

        s = StringIO()
        with redirect_stdout(s):
            g.py()

        generated_code = s.getvalue()

        try:
            exec(generated_code, exec_env, exec_env)
        except IndexError:
            print("stopped by exhaustion")

        actual = exec_env["r"].data

        # actual = set(TrieExecution.naive(DNF(clauses), env).data)

        self.assert_formula_result(
            wanted=wanted,
            actual=actual,
            clauses=clauses,
            env=env,
            **meta,
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
            seed=154,
            variable_count=10,
            clause_count=6,
        )

class TestStateMachineMultipleGeneration(FormulaTestBase):
    def run_formula_case(self, clauses, env, **meta):
        self.run_multiple_formula_case(
            [DNF(clauses)],
            env,
            **meta,
        )
    def random_formulas(
        self,
        rng,
        *,
        formula_count=4,
        variable_count=6,
        clause_count=4,
        min_pos=1,
        max_pos=3,
        min_neg=0,
        max_neg=2,
    ):
        variables = [chr(ord("a") + i) for i in range(variable_count)]

        formulas = []
        all_clauses = []

        for _ in range(formula_count):
            dnf, _ = random_dnf(
                rng,
                variable_count=variable_count,
                clause_count=clause_count,
                min_pos=min_pos,
                max_pos=max_pos,
                min_neg=min_neg,
                max_neg=max_neg,
            )
            formulas.append(dnf)
            all_clauses.extend(dnf.clauses)

        return formulas, all_clauses, variables

    def run_multiple_formula_case(self, formulas, env, **meta):
        wanted = [
            list(formula.eval(env).keys_iterator())
            for formula in formulas
        ]

        graph = TrieExecution.create_state_machine_multiple(formulas)

        names = sorted(set().union(*(formula.vars() for formula in formulas)))

        exec_env = {
            name: Source(name, env[name])
            for name in names
        }

        for i in range(len(formulas)):
            exec_env[f"r{i}"] = Sink()

        print(graph.dot())

        s = StringIO()
        with redirect_stdout(s):
            graph.py()

        generated_code = s.getvalue()

        try:
            exec(generated_code, exec_env, exec_env)
        except IndexError:
            print("stopped by exhaustion")

        actual = [
            exec_env[f"r{i}"].data
            for i in range(len(formulas))
        ]

        self.assertEqual(
            wanted,
            actual,
            msg=(
                f"\ncase={meta.get('case_name')}"
                f"\nseed={meta.get('seed')}"
                f"\ntrial={meta.get('trial')}"
                f"\nformulas={[formula.show() for formula in formulas]}"
                f"\nenv={self.repr_env(env)}"
                f"\nwanted={wanted}"
                f"\nactual={actual}"
            ),
        )

    def run_random_multiple_formulas(
        self,
        *,
        formula_set_trials=100,
        env_trials=20,
        seed=0,
        formula_count=4,
        variable_count=6,
        clause_count=4,
        min_pos=1,
        max_pos=3,
        min_neg=0,
        max_neg=2,
        case_name="random_multiple_formulas",
    ):
        rng = random.Random(seed)

        for i in range(formula_set_trials):
            formulas, all_clauses, variables = self.random_formulas(
                rng,
                formula_count=formula_count,
                variable_count=variable_count,
                clause_count=clause_count,
                min_pos=min_pos,
                max_pos=max_pos,
                min_neg=min_neg,
                max_neg=max_neg,
            )

            print([formula.show() for formula in formulas])

            for j in range(env_trials):
                env = self.random_env_for_clauses(
                    all_clauses,
                    variables,
                    rng,
                )

                with self.subTest(case=case_name, formula_trial=i, env_trial=j):
                    self.run_multiple_formula_case(
                        formulas,
                        env,
                        trial=(i, j),
                        seed=seed,
                        case_name=case_name,
                    )

    def test_random_multiple_formulas(self):
        self.run_random_multiple_formulas(
            formula_set_trials=100,
            env_trials=20,
            seed=987,
            formula_count=3,
            variable_count=6,
            clause_count=4,
        )


if __name__ == "__main__":
    unittest.main()