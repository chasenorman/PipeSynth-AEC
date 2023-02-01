# Functions for creating synthesis functions of various templates.

from litmus import *


def baseline_reads2(nodes, microop_t, name=None):
    def third(i: microop_t, j: microop_t, k: microop_t) -> bool:
        def non_terminals(b: bool, n: Node, m: microop_t):
            return {b: [False, program_order(m, m), same_padd(m, m), same_core(m, m), is_write(m),
                        same_mop(m, m), same_data(m, m), is_read(m), add_edge(n, n),
                        access_type_rmw(m), consecutive(m, m), data_from_init_at_pa(m), True,
                        b & b, ~b, b | b, b >> b, b == b],
                    n: [node(m) for node in nodes],
                    m: [i, j, k]}
        return non_terminals
    def second(i: microop_t, j: microop_t) -> bool:
        def non_terminals(b: bool, n: Node, m: microop_t):
            return {b: [False, program_order(m, m), same_padd(m, m), same_core(m, m), is_write(m),
                        same_mop(m, m), same_data(m, m), is_read(m), add_edge(n, n),
                        access_type_rmw(m), consecutive(m, m), data_from_init_at_pa(m), True,
                        b & b, ~b, b | b, b >> b, b == b],
                    n: [node(m) for node in nodes],
                    m: [i, j]}

        return non_terminals
    def first(i: microop_t) -> bool:
        def non_terminals(b: bool, n: Node, m: microop_t):
            return {b: [False, is_write(m), is_read(m), add_edge(n, n),
                        access_type_rmw(m), data_from_init_at_pa(m), True,
                        b & b, ~b, b | b, b >> b, b == b],
                    n: [node(m) for node in nodes],
                    m: [i]}
        return non_terminals
    synth1 = synthesize(first, 'synth1')
    synth2 = synthesize(second, 'synth2')
    synth3 = synthesize(third, 'synth3')
    synth4 = synthesize(first, 'synth4')
    synth5 = synthesize(second, 'synth5')

    def result(microops):
        return forall(microops, lambda a: synth1(a) >> exists(microops, lambda b:
        synth2(a, b) & ~exists(microops, lambda c:
        synth3(a, b, c)
        )) | (synth4(a) & forall(microops, lambda b:
            synth5(a, b)
        )))

    return result


def baseline_predicate(nodes, microop_t, name=None):
    def baseline_mono(i: microop_t) -> bool:
        def non_terminals(b: bool, n: Node):
            return {b: [False, is_write(i), is_read(i), access_type_rmw(i),
                        data_from_init_at_pa(i), add_edge(n, n), True, is_fence(i),
                        data_from_final_at_pa(i),
                        b & b, ~b, b >> b, b | b, b == b],
                    n: [node(i) for node in nodes]}
        return non_terminals
    return synthesize(baseline_mono, name)

def baseline_path(nodes, microop_t, name=None):
    s = baseline_predicate(nodes, microop_t, name)
    return lambda test: forall(test, lambda i: s(i))


def baseline_bi_predicate(nodes, microop_t, name=None):
    def baseline_bi(i: microop_t, j: microop_t) -> bool:
        def non_terminals(b: bool, n1: Node, n2: Node):
            return {b: [False, program_order(i, j), same_padd(i, j), same_core(i, j), is_write(i), is_write(j),
                        same_mop(i, j), same_data(i, j), is_read(i), is_read(j), add_edge(n1, n2), add_edge(n2, n1),
                        access_type_rmw(i), consecutive(i, j), data_from_init_at_pa(i), data_from_init_at_pa(j),
                        access_type_rmw(j), True, is_fence(i), is_fence(j),
                        data_from_final_at_pa(i), data_from_final_at_pa(j), same_vadd(i, j),
                        b & b, ~b, b | b, b >> b, b == b],
                    n1: [node(i) for node in nodes],
                    n2: [node(j) for node in nodes]}

        return non_terminals
    return synthesize(baseline_bi, name)


def baseline_fifo(nodes, microop_t, name=None):
    s = baseline_bi_predicate(nodes, microop_t, name)
    return lambda test: forall(test, lambda i: forall(test, lambda j: s(i, j)))


count = 0
def conjunct(f, microop_t, arity, name):
    global count
    count += 1
    if not isinstance(f, set):
        f = set(f)
    if arity == 1:
        def grammar(i: microop_t) -> bool:
            def non_terminals(b: bool):
                return {b: [True] + [ff(i) for ff in f]}
            return non_terminals
    if arity == 2:
        def grammar(i: microop_t, j: microop_t) -> bool:
            def non_terminals(b: bool):
                return {b: [True] + [ff(i, j) for ff in f]}
            return non_terminals
    if arity == 3:
        def grammar(i: microop_t, j: microop_t, k: microop_t) -> bool:
            def non_terminals(b: bool):
                return {b: [True] + [ff(i, j, k) for ff in f]}
            return non_terminals
    return synthesize(grammar, f'{name}{count}')


def negation(f, arity):
    if arity == 1:
        return lambda i: ~f(i)
    if arity == 2:
        return lambda i, j: ~f(i, j)

def reverse(f):
    return lambda i, j: f(j, i)


def edge_conjuncts(microop_t, allowed_edges, name, negated=False, unary=False):
    if negated:
        conjuncts = [conjunct(f, microop_t, 2, name) for f in
                     [{(lambda n, m: lambda i, j: ~add_edge(n(i), m(j)))(n, m), (lambda n, m: lambda i, j: add_edge(n(i), m(j)))(n, m)} if unary else
                      {(lambda n, m: lambda i, j: ~add_edge(n(i), m(j)))(n, m), (lambda n, m: lambda i, j: ~add_edge(n(j), m(i)))(n, m), (lambda n, m: lambda i, j: add_edge(n(i), m(j)))(n, m), (lambda n, m: lambda i, j: add_edge(n(j), m(i)))(n, m)}for n, m in allowed_edges]]
    else:
        conjuncts = [conjunct(f, microop_t, 2, name) for f in
                 [{(lambda n, m: lambda i, j: add_edge(n(i), m(j)))(n, m)}
                  if unary else {(lambda n, m: lambda i, j: add_edge(n(i), m(j)))(n, m), (lambda n, m: lambda i, j: add_edge(n(j), m(i)))(n, m)} for n, m in allowed_edges]]
    return lambda a, b: forall(conjuncts, lambda i: i(a, b))


def unary_conjuncts(microop_t, name):
    first_conjuncts = [conjunct(f, microop_t, 1, name) for f in
                       [{is_write, is_read, },  # is_fence},
                        {data_from_init_at_pa, negation(data_from_init_at_pa, 1)},
                        {access_type_rmw, negation(access_type_rmw, 1)}
                        ]]
    return lambda a: forall(first_conjuncts, lambda i: i(a))


def binary_conjuncts(microop_t, name):
    second_conjuncts = [conjunct(f, microop_t, 2, name) for f in
                        [{program_order, same_core, negation(same_core, 2), reverse(program_order),
                           negation(program_order, 2), consecutive},
                          {same_padd, negation(same_padd, 2)},
                          {lambda i, j: is_write(j), lambda i, j: is_read(j), },  # lambda i, j: is_fence(j)},
                          {same_data, negation(same_data, 2)},
                          {lambda i, j: data_from_init_at_pa(j), lambda i, j: ~data_from_init_at_pa(j)},
                          {lambda i, j: access_type_rmw(j), lambda i, j: ~access_type_rmw(j)},
                          ]]
    return lambda a, b: forall(second_conjuncts, lambda i: i(a, b))


def ternary_conjuncts(microop_t, name):
    third_conjuncts = [conjunct(f, microop_t, 3, name) for f in
                       [{lambda i, j, k: is_write(k), lambda i, j, k: is_read(k), lambda i, j, k: is_fence(k)},
                         {lambda i, j, k: data_from_init_at_pa(k), lambda i, j, k: ~data_from_init_at_pa(k)},
                         {lambda i, j, k: access_type_rmw(j), lambda i, j, k: ~access_type_rmw(j)},
                         {lambda i, j, k: same_padd(i, k), lambda i, j, k: same_padd(j, k),
                          lambda i, j, k: ~same_padd(i, k), lambda i, j, k: ~same_padd(j, k),
                          lambda i, j, k: ~same_padd(i, k) & ~same_padd(j, k)},
                         {lambda i, j, k: same_data(i, k), lambda i, j, k: same_data(j, k),
                          lambda i, j, k: ~same_data(i, k), lambda i, j, k: ~same_data(j, k),
                          lambda i, j, k: ~same_data(i, k) & ~same_data(j, k)},
                         {lambda i, j, k: same_core(i, k), lambda i, j, k: same_core(j, k),
                          lambda i, j, k: ~same_core(i, k), lambda i, j, k: ~same_core(j, k),
                          lambda i, j, k: ~same_core(i, k) & ~same_core(j, k)},
                         {lambda i, j, k: program_order(i, k), lambda i, j, k: program_order(k, i),
                          lambda i, j, k: consecutive(i, k), lambda i, j, k: consecutive(k, i)},
                         {lambda i, j, k: program_order(j, k), lambda i, j, k: program_order(k, j),
                          lambda i, j, k: consecutive(k, j), lambda i, j, k: consecutive(j, k)},
                         ]]
    return lambda a, b, c: forall(third_conjuncts, lambda i: i(a, b, c))

axiom_count = 0
def sourcing_axiom(microop_t, allowed_edges, with_final_quantifier=True):
    global axiom_count
    axiom_count += 1
    first = unary_conjuncts(microop_t, f"sourcing{axiom_count}-unary-")
    second = binary_conjuncts(microop_t, f"sourcing{axiom_count}-binary-")
    third = ternary_conjuncts(microop_t, f"sourcing{axiom_count}-ternary-")

    edge1 = edge_conjuncts(microop_t, allowed_edges, f"sourcing{axiom_count}-edge1-")
    edge2 = edge_conjuncts(microop_t, allowed_edges, f"sourcing{axiom_count}-edge2-")
    edge3 = edge_conjuncts(microop_t, allowed_edges, f"sourcing{axiom_count}-edge3-")

    if with_final_quantifier:
        def result(microops):
            return  forall(microops, lambda a: first(a) >> exists(microops, lambda b:
                    ~same_mop(a, b) & second(a, b) & edge1(a, b) & ~exists(microops, lambda c:
                        ~same_mop(a, c) & ~same_mop(b, c) & third(a, b, c) & edge2(a, c) & edge3(b, c)
                    )
                ))
    else:
        def result(microops, a):
            return  first(a) >> exists(microops, lambda b:
                    ~same_mop(a, b) & second(a, b) & edge1(a, b) & ~exists(microops, lambda c:
                        ~same_mop(a, c) & ~same_mop(b, c) & third(a, b, c) & edge2(a, c) & edge3(b, c)
                    )
                )
    return result


def path_axiom(microop_t, allowed_edges):
    global axiom_count
    axiom_count += 1
    first = unary_conjuncts(microop_t, f"path{axiom_count}-unary-")
    edge = edge_conjuncts(microop_t, allowed_edges, f"path{axiom_count}-edge-", unary=True)

    def result(microops):
        return forall(microops, lambda a:
            first(a) >> edge(a, a)
        )

    return result


def fifo_axiom(microop_t, allowed_edges, with_final_quantifier=True):
    global axiom_count
    axiom_count += 1
    first = unary_conjuncts(microop_t, f"fifo{axiom_count}-unary-")
    second = binary_conjuncts(microop_t, f"fifo{axiom_count}-binary-")
    edge1 = edge_conjuncts(microop_t, allowed_edges, f"fifo{axiom_count}-edge1-", negated=True)
    edge2 = edge_conjuncts(microop_t, allowed_edges, f"fifo{axiom_count}-edge2-")

    if with_final_quantifier:
        def result(microops):
            return forall(microops, lambda a:
                forall(microops, lambda b:
                    (~same_mop(a, b) & first(a) & second(a, b) & edge1(a, b)) >> edge2(a, b)
                )
            )
    else:
        def result(microops, a):
            return forall(microops, lambda b:
                    (~same_mop(a, b) & first(a) & second(a, b) & edge1(a, b)) >> edge2(a, b)
                )
    return result


def empty(microop_t):
    c = conjunct([], microop_t, 1, 'empty-empty')
    return lambda microops: c(microops[0])


class Microarchitecture:
    def __init__(self, suite, axioms, Microop, nodes, co_node, execution_dictionary,
                 structure, name, allowed_unary, allowed_binary, axiom_names):
        self.suite = suite
        self.axioms = axioms
        self.Microop = Microop
        self.nodes = nodes
        self.co_node = co_node
        self.execution_dictionary = execution_dictionary
        self.structure = structure
        self.name = name
        self.allowed_unary = allowed_unary
        self.allowed_binary = allowed_binary
        self.axiom_names = axiom_names