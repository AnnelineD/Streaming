import random
import unittest
from abc import ABC, abstractmethod
from contextlib import redirect_stdout
from io import StringIO

from src.clause import Clause, DNF
from src.normalize import normalize
from src.trie.trie import bittrieset
from src.trie.trie_generation import TrieExecution
from src.trie.trie_synth import Source, Sink
from test.random_generator import rand_expr, generate_var_names, random_trie_env_for_clauses


class FormulaTestBase(unittest.TestCase, ABC):
    maxDiff = None

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


    # -------- runners --------

    @abstractmethod
    def run_formula_case(self, clauses, env, **kwargs):
        pass

    def run_random_envs(self, clauses, *, variables, trials, seed, case_name, **kwargs):
        rng = random.Random(seed)

        for i in range(trials):
            env = random_trie_env_for_clauses(clauses, variables, rng)

            with self.subTest(case=case_name, i=i):
                self.run_formula_case(
                    clauses,
                    env,
                    trial=i,
                    seed=seed,
                    case_name=case_name,
                )

    def run_random_formulas(
            self,
            *,
            formula_trials=50,
            env_trials=20,
            seed=0,
            variable_count=5,
            depth=3,
            case_name="random_formula",
    ):
        rng = random.Random(seed)
        alphabet = "abcdefghijklmnopqrstuvwxyz"

        names = alphabet[:variable_count]

        for i in range(formula_trials):
            expr = rand_expr(
                rng,
                names=names,
                depth=depth
            )

            dnf = normalize(expr)
            variables = names

            print(dnf.clauses)

            for j in range(env_trials):
                env = random_trie_env_for_clauses(dnf.clauses, variables, rng)

                with self.subTest(case=case_name, formula_trial=i, env_trial=j):
                    self.run_formula_case(
                        dnf.clauses,
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

    def test_random_formulas(self):
        self.run_random_formulas(
            formula_trials=50,
            env_trials=10,
            seed=456,
            variable_count=6,
            depth=4,
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

    def test_random_formulas(self):
        self.run_random_formulas(
            formula_trials=100,
            env_trials=20,
            seed=154,
            variable_count=10,
            depth=6,
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
        depth=4
    ):
        variables = [chr(ord("a") + i) for i in range(variable_count)]

        formulas = []
        all_clauses = []

        for _ in range(formula_count):
            expr = rand_expr(rng, variables, depth=depth)
            dnf = normalize(expr)
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
        depth=4,
        case_name="random_multiple_formulas",
    ):
        rng = random.Random(seed)
        names = generate_var_names(variable_count)

        for i in range(formula_set_trials):
            exprs = [rand_expr(rng, names=names, depth=depth) for _ in range(formula_count)]
            dnfs = [normalize(expr) for expr in exprs]

            # print([formula.show() for formula in dnfs])

            all_clauses = [clause for dnf in dnfs for clause in dnf.clauses]

            for j in range(env_trials):
                env = random_trie_env_for_clauses(
                    all_clauses,
                    names,
                    rng,
                )

                with self.subTest(case=case_name, formula_trial=i, env_trial=j):
                    self.run_multiple_formula_case(
                        dnfs,
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
            depth=4,
        )


if __name__ == "__main__":
    unittest.main()