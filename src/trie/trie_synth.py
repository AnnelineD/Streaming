from contextlib import redirect_stdout
from io import StringIO
from typing import Self, Literal
from src.trie.trie import bittrieset, BitTrieMap, TrieRef


class Graph:
    def __init__(self): self.srcs = []; self.snks = []; self.vtcs = []; self.transitions = []; self.init = None
    def sources(self, *names): new = Src.named(self, *names); self.srcs += new; return new
    def sinks(self, *names): new = Snk.named(self, *names); self.snks += new; return new
    def states(self, *names): new = Vtx.named(self, *names); self.vtcs += new; return new
    def py(self):
        print(f"from src.trie.utils import *")
        for src in self.srcs:
            print(f"tmp_{src.name} = None")
        print(f"state = '{self.init.name}'")
        print("for i in range(500):")
        print('\tprint("state", state)')
        for state in self.vtcs:
            print(f"\tif state == '{state.name}':")
            for t in self.transitions:
                if t.s_from != state: continue
                if t.active: print(f"\t\tif {' and '.join(f'tmp_{c.name}' for c in t.active)}:")
                else: print(f"\t\tif True:")
                if t.when:
                    temp = []
                    for c in t.when:
                        def print_condition(c):
                            match c:
                                case Inequality(kind=kind, lhs=lhs, rhs=rhs): return (f'tmp_{lhs.name}.path() {kind} tmp_{rhs.name}.path()')
                                case IsValue(lhs=lhs): return (f'tmp_{lhs.name}.is_value()')
                                case PrefixOf(lhs=lhs, rhs=rhs, is_var=is_var):  return (f'tmp_{lhs.name}.prefix_of({rhs if is_var else f'tmp_{rhs.name}'})')
                                case Finished(lhs=lhs): return (f'tmp_{lhs.name} is None')
                                case NotFinished(lhs=lhs): return (f'tmp_{lhs.name}')
                                case Not(lhs=lhs): return f'not ({print_condition(lhs)})'
                                case Or(lhs=lhs, rhs=rhs): return f'({print_condition(lhs)} or {print_condition(rhs)})'
                                case And(lhs=lhs, rhs=rhs): return f'({print_condition(lhs)} and {print_condition(rhs)})'
                        temp.append(print_condition(c))
                    print(f"\t\t\tif {' and '.join(temp)}:")
                else: print(f"\t\t\tif True:")
                for dst, src in t.push: print(f"\t\t\t\t{dst.name}.push(tmp_{src.name}.path())")
                for src in t.descend: print(f"\t\t\t\ttmp_{src.name} = {src.name}.descend_or_next()")
                for src, ds in t.next_i:
                    if len(ds) > 1:
                        lvls = [f"{src.name}.difference_level({rhs.name})" for rhs in ds]
                        print(f"\t\t\t\ttmp_{src.name} = {src.name}.next(max({', '.join(lvls)}))")
                    else: print(f"\t\t\t\ttmp_{src.name} = {src.name}.next({src.name}.difference_level({ds[0].name}))")
                for src, ds in t.approach:
                    if len(ds) == 1:
                        print(
                            f"\t\t\t\ttarget = {f'argmax([{", ".join('tmp_' + e.name for e in ds[0])}])' if len(ds[0]) > 1 else 'tmp_' + ds[0][0].name}"
                        )
                    else:
                        print(
                            f"\t\t\t\ttarget = argmin([{", ".join(f'argmax([{", ".join('tmp_' + e.name for e in s)}])' if len(s) > 1 else 'tmp_' + s[0].name for s in ds)}])"
                        )
                    print(f"\t\t\t\ttmp_{src.name} = {src.name}.approach(target)")
                for src in t.end: print(f"\t\t\t\ttmp_{src.name} = None")
                print(f"\t\t\t\tstate = '{t.s_to.name}'")
                print(f"\t\t\t\tcontinue")
            # print("\t\tprint(state, 'not continued!')")
            print("\t\tbreak")
    def dot(self, title=None):
        if title:
            title = title.replace("\\", "\\\\")
            print(f"title [shape=\"rect\", label=\"{title}\"]")
        label_index = 0
        for state in self.vtcs:
            print(state.name, ";")
        for t in self.transitions:
            cond = []
            todo = []
            for src in t.active: cond.append(f"active {src.name}")
            # for src in t.finished: cond.append(f"finished {src.name}")
            if t.when:
                for c in t.when:
                    def print_condition(c):
                        match c:
                            case Inequality(kind=kind, lhs=lhs, rhs=rhs): return (f'{lhs.name} {kind} {rhs.name}')
                            case IsValue(lhs=lhs): return (f'{lhs.name}.is_value()')
                            case PrefixOf(lhs=lhs, rhs=rhs, is_var=is_var): return (f'{lhs.name}.prefix_of({rhs if is_var else rhs.name})')
                            case Finished(lhs=lhs): return (f'{lhs.name} is None')
                            case NotFinished(lhs=lhs): return (f'active {lhs.name}')
                            case Not(lhs=lhs): return f'not {print_condition(lhs)}'
                            case And(lhs=lhs, rhs=rhs): return f'({print_condition(lhs)}) and ({print_condition(rhs)})'
                            case Or(lhs=lhs, rhs=rhs): return f'({print_condition(lhs)}) or ({print_condition(rhs)})'
                    cond.append(print_condition(c))
            for dst, src in t.push: todo.append(f"{dst.name}!{src.name}")
            for src in t.descend: todo.append(f"{src.name}.descend_or_next()")
            for src, ds in t.next_i: todo.append(f"{src.name}.next({[d.name for d in ds]})")
            for src, ds in t.approach:
                if len(ds) == 1:
                    todo.append(
                        f"target = {f'argmax([{", ".join(e.name for e in ds[0])}])' if len(ds[0]) > 1 else ds[0][0].name}"
                    )
                else:
                    todo.append(
                        f"target = argmin([{", ".join(f'argmax([{", ".join(e.name for e in s)}])' if len(s) > 1 else s[0].name for s in ds)}])"
                    )
                todo.append(f"{src.name}.approach(target)")
            for src in t.end: todo.append(f"end {src.name}")
            if len(cond) == 0:
                cond = ["else"]
            temp = [f"{' \\n '.join(cond)}", f"{' \\n '.join(todo)}"]
            label = f"{{{' | '.join(temp)}}}"
            label = label.replace('>', '\\>')
            label = label.replace('<', '\\<')
            print(f"l{label_index} [shape=\"record\", label=\"{label}\"];")
            print(f"{t.s_from.name} -> l{label_index} [arrowhead=\"none\"];")
            print(f"l{label_index} -> {t.s_to.name};")
            label_index += 1
class Node:
    def __init__(self, graph, name): self.graph = graph; self.name = name
    @classmethod
    def named(cls, g, *args) -> list[Self]: return [cls(g, a) for a in args]
class Src(Node):
    def __lt__(self, other: 'Src'): return Inequality('<', self, other)
    def __le__(self, other: 'Src'): return Inequality('<=', self, other)
    def __gt__(self, other: 'Src'): return Inequality('>', self, other)
    def __ge__(self, other: 'Src'): return Inequality('>=', self, other)
    def __eq__(self, other: 'Src'): return Inequality('==', self, other)
    def __ne__(self, other: 'Src'): return Inequality('!=', self, other)

class Snk(Node): pass

class Cond:
    def __or__(self, other: 'Cond'): return Or(self, other)
    def __and__(self, other: 'Cond'): return And(self, other)
    def __neg__(self): return Not(self)

class Inequality(Cond):
    def __init__(self, kind: Literal["=="] | Literal["<"] | Literal[">"] | Literal["!="], lhs: Src, rhs: Src):
        self.kind = kind; self.lhs = lhs; self.rhs = rhs

class IsValue(Cond):
    def __init__(self, lhs: Src):
        self.lhs = lhs

class PrefixOf(Cond):
    def __init__(self, lhs: Src, rhs:Src, is_var=False):
        self.lhs = lhs; self.rhs = rhs; self.is_var = is_var

class Finished(Cond):
    def __init__(self, lhs: Src):
        self.lhs = lhs

class NotFinished(Cond):
    def __init__(self, lhs: Src):
        self.lhs = lhs

class Or(Cond):
    def __init__(self, lhs: Cond, rhs: Cond):
        self.lhs = lhs; self.rhs = rhs

class And(Cond):
    def __init__(self, lhs: Cond, rhs: Cond):
        self.lhs = lhs; self.rhs = rhs

class Not(Cond):
    def __init__(self, lhs: Cond):
        self.lhs = lhs

class Transition:
    def __init__(self, s_from, s_to, when, push, descend, next_i, active, approach, end):
        self.s_from = s_from; self.s_to = s_to; self.when = when; self.push = push; self.descend = descend; self.next_i = next_i; self.active=active; self.approach=approach; self.end=end;
class Vtx(Node):
    def to(self, other, *when, push=(), descend=(), next_i=(), active=(), approach=(), end=()):
        self.graph.transitions.append(Transition(self, other, when, push, descend, next_i, active, approach, end))

def ctx():
    # (a /\ c)\/(b /\ c) \ d
    g = Graph()
    a, b, c, d = g.sources('a', 'b', 'c', 'd')
    r, = g.sinks('r')
    s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s15 = g.states('s0', 's1', 's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11', 's12', "s15")
    g.init = s0

    s0.to(s1, descend=(a, b, c, d))
    s1.to(s2, NotFinished(a), NotFinished(c), a < c)
    s1.to(s3, NotFinished(b), NotFinished(c), b < c)
    s1.to(s4, NotFinished(a), NotFinished(c), a == c)
    s1.to(s5, NotFinished(b), NotFinished(c), b == c)
    s1.to(s6, NotFinished(a), NotFinished(b), NotFinished(c), a > c, b > c)
    s1.to(s11, Finished(a), NotFinished(b), NotFinished(c), b > c)
    s1.to(s12, Finished(b), NotFinished(a), NotFinished(c), a > c)

    s2.to(s1, PrefixOf(a, c), descend=(a,)) # we already know that a and c are not finished
    s2.to(s1, Not(PrefixOf(a, c)), next_i=((a, (c, )),))

    s3.to(s1, PrefixOf(b, c), descend=(b,)) # we already know that b and c are not finished
    s3.to(s1, Not(PrefixOf(b, c)), next_i=((b, (c,)),))

    s4.to(s7, IsValue(a), IsValue(c))   # we already know that a and c are not finished
    s4.to(s1, Not(IsValue(a)), descend=(a,))
    s4.to(s1, Not(IsValue(c)), descend=(a,))

    s5.to(s9, IsValue(b), IsValue(c))
    s5.to(s1, Not(IsValue(b)), descend=(b,))
    s5.to(s1, Not(IsValue(c)), descend=(b,))

    s6.to(s1, PrefixOf(c, a), descend=(c,))
    s6.to(s1, PrefixOf(c, b), descend=(c,))
    s6.to(s1, Not(PrefixOf(c, a)), Not(PrefixOf(c, b)), next_i=((c, (a, b)),))

    s7.to(s8, NotFinished(d), a > d)
    s7.to(s1, NotFinished(d), a < d, push=((r, a),), descend=(a,))
    s7.to(s1, NotFinished(d), a == d, IsValue(d), descend=(a,))
    s7.to(s1, NotFinished(d), a == d, Not(IsValue(d)), push=((r, a),), descend=(a,))
    s7.to(s1, Finished(d), push=((r, a),), descend=(a,))

    s8.to(s7, NotFinished(d), PrefixOf(d, a), descend=(d,))
    s8.to(s7, NotFinished(d), Not(PrefixOf(d, a)), next_i=((d, (a,)),))

    s9.to(s10, NotFinished(d), b > d)
    s9.to(s1, NotFinished(d), b < d, push=((r, b),), descend=(b,))
    s9.to(s1, NotFinished(d), b == d, IsValue(d), descend=(b,))
    s9.to(s1, NotFinished(d), b == d, Not(IsValue(d)), push=((r, b),), descend=(b,))
    s9.to(s1, Finished(d), push=((r, b),), descend=(b,))

    s10.to(s9, NotFinished(d), PrefixOf(d, b), descend=(d, ))
    s10.to(s9, NotFinished(d), Not(PrefixOf(d, b)), next_i=((d, (b, )), ))

    s11.to(s1, PrefixOf(c, b), descend=(c,))
    s11.to(s1, Not(PrefixOf(c, b)), next_i=((c, (b,)),))

    s12.to(s1, PrefixOf(c, a), descend=(c, ))
    s12.to(s1, Not(PrefixOf(c, a)), next_i=((c, (a, )), ))

    return g

def intersection_graph():
    # a /\ b /\ c
    g = Graph()
    a, b, c = g.sources('a', 'b', 'c')
    r, = g.sinks('r')
    s0, s1, s2, s3, s4, s5 = g.states('s0', 's1', 's2', 's3', 's4', 's5')
    g.init = s0

    s0.to(s1, descend=(a, b, c))

    s1.to(s2, NotFinished(a), NotFinished(b), NotFinished(c), a == b, b == c)

    s1.to(s3, NotFinished(a), NotFinished(b), NotFinished(c), a < b)
    s1.to(s3, NotFinished(a), NotFinished(b), NotFinished(c), a < c)
    s1.to(s4, NotFinished(a), NotFinished(b), NotFinished(c), b < a)
    s1.to(s4, NotFinished(a), NotFinished(b), NotFinished(c), b < c)
    s1.to(s5, NotFinished(a), NotFinished(b), NotFinished(c), c < a)
    s1.to(s5, NotFinished(a), NotFinished(b), NotFinished(c), c < b)

    s2.to(s1, IsValue(a), IsValue(b), IsValue(c), push = ((r, a), ), descend=(a, )) # or descend b or descend c
    s2.to(s1, Not(IsValue(a)), descend=(a, )) # or descend b or descend c
    s2.to(s1, Not(IsValue(b)), descend=(a, )) # or descend b or descend c
    s2.to(s1, Not(IsValue(c)), descend=(a, )) # or descend b or descend c


    s3.to(s1, b > c, PrefixOf(a, b), descend=(a,))
    s3.to(s1, b == c, PrefixOf(a, b), descend=(a,))
    s3.to(s1, b < c, PrefixOf(a, c), descend=(a,))
    s3.to(s1, b == c, PrefixOf(a, c), descend=(a,))
    s3.to(s1, b > c, Not(PrefixOf(a, b)), next_i=((a, (b, )),))
    s3.to(s1, b < c, Not(PrefixOf(a, c)), next_i=((a, (c, )),))
    s3.to(s1, b == c, Not(PrefixOf(a, c)), next_i=((a, (c, )),))

    s4.to(s1, a > c, PrefixOf(b, a), descend=(b,))
    s4.to(s1, a == c, PrefixOf(b, a), descend=(b,))
    s4.to(s1, a < c, PrefixOf(b, c), descend=(b,))
    s4.to(s1, a == c, PrefixOf(b, c), descend=(b,))
    s4.to(s1, a > c, Not(PrefixOf(b, a)), next_i=((b, (a, )),))
    s4.to(s1, a < c, Not(PrefixOf(b, c)), next_i=((b, (c, )),))
    s4.to(s1, a == c, Not(PrefixOf(b, c)), next_i=((b, (c, )),))

    s5.to(s1, a > b, PrefixOf(c, a), descend=(c,))
    s5.to(s1, a == b, PrefixOf(c, a), descend=(c,))
    s5.to(s1, a < b, PrefixOf(c, b), descend=(c,))
    s5.to(s1, a == b, PrefixOf(c, b), descend=(c,))
    s5.to(s1, a > b, Not(PrefixOf(c, a)), next_i=((c, (a,)),))
    s5.to(s1, a < b, Not(PrefixOf(c, b)), next_i=((c, (b,)),))
    s5.to(s1, a == b, Not(PrefixOf(c, b)), next_i=((c, (b,)),))

    return g

def tree(ds):
  v, r = set(), dict()
  for d in ds:
    if len(d) == 1:
      v.add(d[0])
    else:
      x, y = tree(d[1:])
      z, w = r.get(d[0], tree([]))
      r[d[0]] = (x | z, y | w)
  return (v, r)

class Source:
    def __init__(self, n, s):
        self.name = n
        self.data: BitTrieMap = s
        self.current: TrieRef = self.data.ref()
        self.finished = False
    def path(self):
        return self.current.path
    # def descend(self):
    #     if self.current.descend_first() is not None:
    #         self.current = self.current.descend_first()
    #         return self.current
    #     return None
    def descend_or_next(self):
        # descend one, and if you can't descend anymore, find the next possible value
        if self.current.descend_first() is not None:
            self.current = self.current.descend_first()
        else:
            while self.current is not None and not self.has_sibling():
                self.current = self.ascend()
            if self.current is None:
                print(f"descend None from {self.name}")
                return None
            self.current = self.next_sibling()
            if self.current is None:
                return None
        print(f"descend {self.current.path} from {self.name}")
        return self
    def ascend(self):
        self.current = self.current.ascend_bit()
        return self.current
    def has_sibling(self):
        return self.current.next_sibling() is not None
    def next_sibling(self):
        self.current = self.current.next_sibling()
        return self.current
    def next(self, i):
        current_lvl = len(self.path())
        for _ in range(current_lvl - i - 1):
            self.current = self.ascend()
        while self.current is not None and not self.has_sibling():
            self.current = self.ascend()

        if self.current is None:
            return None
        self.current = self.next_sibling()
        if self.current is None:
            return None
        print(f"next_{i} {self.current.path} from {self.name}")
        return self
    def prefix_of(self, other):
        res = other.path().startswith(self.path())
        print("prefix", self.path(), other.path(), res)
        return other.path().startswith(self.path())
    def val_prefix_of(self, other):
        res = other.path().startswith(self.path())
        print(self.path(), other.path(), res)
        return other.path().startswith(self.path())
    def difference_level(self, other):
        return next((e for e, (c1, c2) in enumerate(zip(self.path(), other.path())) if c1 != c2), None)
    def val_difference_level(self, value):
        return next((e for e, (c1, c2) in enumerate(zip(self.path(), value)) if c1 != c2), None)
    def is_value(self):
        return self.current.is_value()
    def approach(self, other):
        if other is None:
            return None
        if self.prefix_of(other):
            return self.descend_or_next()
        else:
            return self.next(self.difference_level(other))
    def approach_val(self, value):
        if value is None:
            return None
        if self.val_prefix_of(value):
            return self.descend_or_next()
        else:
            return self.next(self.val_difference_level(value))



class Sink:
    def __init__(self):
        self.data = []
    def push(self, inp):
        print("push", inp)
        self.data.append(inp)

if __name__ == '__main__':
    g = ctx()
    # g = intersection_graph()
    g.py()


    x, y, z, w, _1, _2, _3 = ('000', '001', '010', '011', '100', '101', '110')

    a = Source('a', bittrieset(x, _2, _3))
    # a = Source('a', bittrieset(y, _1, _2, _3))
    b = Source('b', bittrieset(y, z, _1, _2))
    c = Source('c', bittrieset(z, w, _1, _2))
    d = Source('d', bittrieset(x, _1))

    r = Sink()
    #wanted: 010, 101

    r_wanted = ((a.data | b.data) & c.data) - d.data
    # r_wanted = ((a.data & b.data) & c.data)

    s = StringIO()
    with redirect_stdout(s): g.py()
    try: exec(s.getvalue())
    except IndexError: print("stopped by exhaustion")


    print(r_wanted)
    print("result", r.data)

    g.dot()
