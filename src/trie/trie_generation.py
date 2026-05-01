from src.clause import Clause, DNF
from src.trie.trie import bittrieset, bittriemap
from src.trie.trie_synth import *

class TrieExecution:
    @staticmethod
    def naive(formula, env):
        print(formula.dependencies())
        srcs = {k: Source(k, v) for (k, v) in env.items() if k in formula.vars()}
        r = Sink()
        values = {k: s.descend_or_next() for (k, s) in srcs.items()}

        for i in range(500):
            print("ITER", i)
            matched = False

            # check whether there are paths to add to the results
            for c in formula.clauses:
                ps = list(c.P)
                if all(values[p] is not None for p in ps):
                    if (
                            all(values[ps[0]].path() == values[p].path() for p in ps)
                            and all(values[p].is_value() for p in ps)
                            and all(values[n].path() > values[ps[0]].path() or (values[n].path() == values[ps[0]].path() and not values[n].is_value()) for n in c.N if values[n] is not None)
                    ):
                        r.push(values[ps[0]].path())
                        p = ps[0]
                        values[p] = srcs[p].descend_or_next()   #TODO see how much we can skip!
                        matched = True
                        break

            if matched:
                continue

            if all(v is None for v in values.values()):
                break

            # compute minimum path value
            min_path = min(
                (v.path() for v in values.values() if v is not None),
            )

            # get all keys with that minimum
            mins = [
                k for k, v in values.items()
                if v is not None and v.path() == min_path
            ]

            # update all of them
            print("next iter")

            print("all mins", mins)
            for k in mins:
                if k in formula.singletons():
                    values[k] = srcs[k].descend_or_next()
                    continue


                print("for minimum", k)
                dependencies = formula.dependencies()

                maxima = [
                    max(
                        (p for p in pg if values[p] is not None),
                        key=lambda p: values[p].path(),
                        default=None
                    )
                    for pg in dependencies[k]
                    if pg and any(values[p] is not None for p in pg)
                ]
                # print("pos candidates: ", [{p: values[p].path() for p in pg} for pg in pgs])

                # temp_pos = min(pos_candidates, key=lambda p: values[p].path()) if pos_candidates else None
                temp = min(maxima, key=lambda p: values[p].path()) if maxima else None

                # neg_candidates = [
                #     max(
                #         (n for n in ng if values[n] is not None),
                #         key=lambda n: values[n].path(),
                #         default=None
                #     )
                #     for ng in ngs[k]
                #     if ng and any(values[n] is not None for n in ng)
                # ]
                # temp_neg = min(neg_candidates, key=lambda p: values[p].path()) if neg_candidates else None
                #
                # candidates = [x for x in (temp_pos, temp_neg) if x is not None]
                # temp = min(candidates, key=lambda c: values[c].path()) if candidates else None
                print("approach", temp, values[temp].path() if temp else '/')

                if temp is None:
                    values[k] = srcs[k].descend_or_next() # TODO what to do?
                    continue

                if values[temp].path() == values[k].path():
                    values[k] = srcs[k].descend_or_next()
                else:
                    if srcs[k].prefix_of(srcs[temp]):
                        values[k] = srcs[k].descend_or_next()

                    else:
                        i = srcs[k].difference_level(srcs[temp])
                        values[k] = srcs[k].next(i)

                # print("min", k, temp)

        return r

    @staticmethod
    def create_state_machine_version1(formula: DNF):
        # !!! CURRENT VERSION BELOW
        # premature version - we still go over every branch of the trie
        # to add: if all positives are None, we are done, we don't have to pull the negatives
        g = Graph()
        s0, s1, s2 = g.states('s0', 's1', 's2')
        var_states = {v: g.states(f"s{v}")[0] for v in formula.vars()}
        clause_states = {e: g.states(f"sc{e}")[0] for e, c in enumerate(formula.clauses)}
        srcs = {v: g.sources(v)[0] for v in formula.vars()}

        stateidx = 0

        pos_vars = {v for c in formula.clauses for v in c.P}

        g.init = s0

        s0.to(s1, descend=(srcs.values()))

        r, = g.sinks('r')

        for e, clause in enumerate(formula.clauses):
            ps = list(clause.P)
            s1.to(clause_states[e],
                  *(IsValue(srcs[p]) for p in ps),
                  *(srcs[ps[0]] == srcs[q] for q in ps),
                  *(Finished(srcs[v]) | Inequality(">=", srcs[v], srcs[ps[0]]) for v in pos_vars.difference(ps)),
                  *(Or(Finished(srcs[n]), Or(Inequality("!=", srcs[n], srcs[ps[0]]), Not(IsValue(srcs[n])))) for n in clause.N), active=tuple(srcs[p] for p in ps))
            # possible optimization: create new state for every clause in which we know that the vars in that clause are part of the minima
            clause_states[e].to(var_states[ps[0]], *(Or(Or(Finished(srcs[n]), Inequality(">", srcs[n], srcs[ps[0]])), And(Inequality("==", srcs[n], srcs[ps[0]]), Not(IsValue(srcs[n])))) for n in clause.N), push=((r, srcs[ps[0]]),))

            for n in clause.N:
                new_state = g.states(f"n{stateidx}")[0]
                clause_states[e].to(new_state, srcs[n] < srcs[ps[0]], active=(srcs[n],))
                new_state.to(clause_states[e], PrefixOf(srcs[n], srcs[ps[0]]), active=(srcs[n],), descend=(srcs[n],))
                new_state.to(clause_states[e], Not(PrefixOf(srcs[n], srcs[ps[0]])), active=(srcs[n],), next_i=((srcs[n], (srcs[ps[0]], )),))
                stateidx += 1
                clause_states[e].to(s1, IsValue(srcs[n]), srcs[n] == srcs[ps[0]], active=(srcs[n],))

        s1.to(s2)

        for v in pos_vars:
            s2.to(var_states[v], *(Or(Finished(srcs[v]), Inequality(">=", srcs[v2], srcs[v])) for v2 in pos_vars.difference(v)),
                  active=(srcs[v],))
            for v2 in pos_vars.difference(v):
                var_states[v].to(var_states[v], srcs[v] == srcs[v2], active=(srcs[v2], ), descend=(srcs[v2],))
            var_states[v].to(s1, descend=(srcs[v],))

        return g

    @staticmethod
    def create_state_machine(formula: DNF):
        g = Graph()
        s0, s1, s2 = g.states('s0', 's1', 's2')
        pos_vars = {v for c in formula.clauses for v in c.P}

        var_states = {v: g.states(f"s{v}")[0] for v in pos_vars}
        clause_states = {e: g.states(f"sc{e}")[0] for e, c in enumerate(formula.clauses)}
        srcs = {v: g.sources(v)[0] for v in formula.vars()}

        stateidx = 0

        dependencies = formula.dependencies()

        g.init = s0

        s0.to(s1, descend=(srcs.values()))

        r, = g.sinks('r')

        for e, clause in enumerate(formula.clauses):
            ps = list(clause.P)
            # all positives of a clause are equal, minima, and not equal to any of the negatives -> potential push
            s1.to(clause_states[e],
                  *(IsValue(srcs[p]) for p in ps),
                  *(srcs[ps[0]] == srcs[q] for q in ps),
                  *(Finished(srcs[v]) | (srcs[v] >= srcs[ps[0]]) for v in pos_vars.difference(ps)),
                  *(Finished(srcs[n]) | (srcs[n] != srcs[ps[0]]) | Not(IsValue(srcs[n])) for n in clause.N), active=tuple(srcs[p] for p in ps))
            # all negatives of the clause are bigger than the equal positives -> push
            # possible optimization: create new state for every clause in which we know that the vars in that clause are part of the minima
            clause_states[e].to(var_states[ps[0]], *(Finished(srcs[n]) | (srcs[n] > srcs[ps[0]]) | ((srcs[n] == srcs[ps[0]]) & Not(IsValue(srcs[n]))) for n in clause.N), push=((r, srcs[ps[0]]),))

            for n in clause.N:
                new_state = g.states(f"n{stateidx}")[0]
                # a negative n is smaller than the positives -> increase it
                clause_states[e].to(new_state, srcs[n] < srcs[ps[0]], active=(srcs[n],))
                new_state.to(clause_states[e], PrefixOf(srcs[n], srcs[ps[0]]), active=(srcs[n],), descend=(srcs[n],))
                new_state.to(clause_states[e], Not(PrefixOf(srcs[n], srcs[ps[0]])), active=(srcs[n],), next_i=((srcs[n], (srcs[ps[0]], )),))
                stateidx += 1
                # a negative n is equal to the positives -> no push
                clause_states[e].to(s1, IsValue(srcs[n]), srcs[n] == srcs[ps[0]], active=(srcs[n],))

        s1.to(s2)

        for v in pos_vars:
            # find one of the minimum elements
            s2.to(var_states[v], *(Finished(srcs[v2]) | (srcs[v2] >= srcs[v]) for v2 in pos_vars.difference(v)),
                  active=(srcs[v],))
            for v2 in pos_vars.difference(v):
                # pull all other minima
                if v2 in formula.singletons():
                    var_states[v].to(var_states[v], srcs[v] == srcs[v2], active=(srcs[v2],), descend=(srcs[v2],))
                    continue
                depv2 =  dependencies[v2]
                if len(depv2) == 0:
                    var_states[v].to(var_states[v], srcs[v] == srcs[v2], active=(srcs[v2], ), descend=(srcs[v2],))
                else:
                    var_states[v].to(var_states[v], srcs[v] == srcs[v2], active=(srcs[v2], ), approach=((srcs[v2], [[srcs[p] for p in s] for s in depv2]), ))

            # else branch
            if v in formula.singletons():
                var_states[v].to(s1, descend=(srcs[v],))

            else:
                var_states[v].to(s1, approach=((srcs[v], [[srcs[p] for p in s] for s in dependencies[v]]), ))

        return g



if __name__ == '__main__':
    """
    c1 = Clause.make({"a", "c"}, {"d"})
    c2 = Clause.make({"b", "c"}, {"d"})
    formula = DNF([c1, c2])

    x, y, z, w, _1, _2, _3 = ('000', '001', '010', '011', '100', '101', '110')

    # a = Source('a', bittrieset(x, _2, _3))
    a = Source('a', bittrieset(y, _1, _2, _3))
    b = Source('b', bittrieset(y, z, _1, _2))
    c = Source('c', bittrieset(z, w, _1, _2))
    d = Source('d', bittrieset(x, _1))

    env = {
        "a": bittrieset(y, _1, _2, _3),
        "b": bittrieset(y, z, _1, _2),
        "c": bittrieset(z, w, _1, _2),
        "d": bittrieset(x, _1),
    }
    """


    clauses=[Clause(P=frozenset({'a'}), N=frozenset({'b'})), Clause(P=frozenset({'b'}), N=frozenset({'c'})), Clause(P=frozenset({'c'}), N=frozenset({'d'})), Clause(P=frozenset({'d'}), N=frozenset({'e'}))]
    env={
        "a": {},
        "b": {('001111', None), ('010', None), ('1000', None), ('10100', None), ('11', None), ('1101', None)},
        "c": {('0', None), ('00000', None), ('001111', None), ('010', None), ('01001', None), ('110001', None), ('1101', None)},
        "d": {('000111', None), ('01000', None), ('10010', None), ('1110', None)},
        "e": {('001111', None), ('01001', None), ('0101', None), ('1010', None), ('10100', None), ('110001', None), ('1101', None)},
        "f": {('000101', None), ('101', None), ('1010', None), ('11', None), ('110001', None), ('110011', None)},
    }
    # wanted=['000101', '001111', '101', '1010', '11', '110001', '110011', '1101']
    # actual=['001111', '101', '1010', '11', '110001', '1101']


    env_ = {k: bittrieset(*{s[0] for s in v}) for k, v in env.items()}
    a = Source('a', env_["a"])
    b = Source('b', env_["b"])
    c = Source('c', env_["c"])
    d = Source('d', env_["d"])
    e = Source('e', env_["e"])
    f = Source('f', env_["f"])


    r = Sink()

    formula = DNF(clauses)
    # f = DNF([Clause({"a", "b", "c", "d"}, {"e", "f"})])

    g = TrieExecution.create_state_machine(formula)
    g.dot(title=formula.show())
    g.py()



    env = {k: bittrieset(*[e[0] for e in v]) for k, v in env.items()}

    wanted: BitTrieMap = formula.eval(env)

    # r = TrieExecution.naive(f, env)
    s = StringIO()
    with redirect_stdout(s):
        g.py()
    try:
        exec(s.getvalue())
    except IndexError:
        print("stopped by exhaustion")


    print(formula.show())
    print("wanted", list(wanted.keys_iterator()))
    print("found", r.data)


