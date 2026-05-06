import random
import unittest
from contextlib import redirect_stdout
from io import StringIO

from src.normalize import normalize
from src.set.set_generation import graph_generation
from src.set.synth import Source, Sink
from test.random_generator import rand_expr, random_set_env


class MyTestCase(unittest.TestCase):
    def run_formula_case(
            self,
            formula,
            env,
            *,
            seed=None,
            trial=None,
            case_name=None,
    ):
        # wanted = self.expected_result(clauses, env)

        g = graph_generation(formula)

        names = sorted(formula.vars())
        srcs = g.sources(*names)
        source_map = dict(zip(names, srcs))

        exec_env = {n: Source(n, env[n]) for n in names}
        exec_env["r"] = Sink()

        s = StringIO()
        with redirect_stdout(s):
            g.py()

        generated_code = s.getvalue()

        try:
            exec(generated_code, exec_env, exec_env)
        except IndexError:
            print("stopped by exhaustion")

        actual = set(exec_env["r"].data)

        return actual

    def run_random_formulas(
        self,
        *,
        formula_trials=50,
        env_trials=10,
        seed=0,
        variable_count=6,
        depth = 3,
        case_name="random_formulas",
    ):
        rng = random.Random(seed)
        alphabet = "abcdefghijklmnopqrstuvwxyz"

        names = alphabet[:variable_count]

        for i in range(formula_trials):
            expr = rand_expr(
                rng,
                names=names,
                depth = depth
            )

            formula = normalize(expr)
            for j in range(env_trials):
                env = random_set_env(names, rng=rng)
                wanted = expr.eval(env)

                with self.subTest(case=case_name, formula_trial=i, env_trial=j, seed=seed):
                    result = self.run_formula_case(
                        formula,
                        env,
                        seed=seed,
                        trial=(i, j),
                        case_name=case_name,
                    )
                print(expr.show())
                print(formula.show())
                print(wanted)
                print(result)
                self.assertSetEqual(wanted, result)


    def test_random_formulas(self):
        self.run_random_formulas(
            formula_trials=100,
            env_trials=20,
            seed=256,
            variable_count=6,
            depth=3,
        )


if __name__ == '__main__':
    unittest.main()
