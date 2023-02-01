# Implementation of the uspec language embedded in LIA

from cvc import *

TRACKED = None
ASSIGNED_VARIABLES = dict()

class UOPType(CVCEnum):
    Read: None
    Write: None
    Fence: None


class Node(CVCObject):
    node_exists: bool
    time: int

defined = dict()

def forall(l, f, id=0, first_operands=None):
    global defined
    if len(l) == 0:
        return CVCBool(value=True)
    if len(l) == 1:
        return f(l[0])
    if id:
        if id not in defined:
            defined[id] = define_fun(f, name=f'quantified{id}')
        f = defined[id]
    return CVCObject(kind=pycvc5.kinds.And, operands=tuple(map(f, l)))


def exists(l, f, id=0, first_operands=()):
    global defined
    if len(l) == 0:
        return True
    if len(l) == 1:
        return f(l[0])
    if id:
        if id not in defined:
            defined[id] = define_fun(f, name=f'quantified{id}')
        f = defined[id]
    l = [first_operands + (li, ) for li in l]
    return CVCObject(kind=pycvc5.kinds.Or, operands=tuple(f(*li) for li in l))

@define_fun
def is_read(i):
    # if repr(i.type) in ASSIGNED_VARIABLES:
    #     return ASSIGNED_VARIABLES[repr(i.type)] == 'R'
    return i.type == UOPType.Read


@define_fun
def is_write(i):
    #if repr(i.type) in ASSIGNED_VARIABLES:
    #    return ASSIGNED_VARIABLES[repr(i.type)] == 'W'
    return i.type == UOPType.Write


def access_type_rmw(i):
    #if repr(i.rmw_access) in ASSIGNED_VARIABLES:
    #    return ASSIGNED_VARIABLES[repr(i.rmw_access)]
    return i.rmw_access


def node_exists(n):
    return n.node_exists


@define_fun
def consecutive(i, j):
    #if repr(i.core) in ASSIGNED_VARIABLES and repr(j.core) in ASSIGNED_VARIABLES:
    #    return (ASSIGNED_VARIABLES[repr(i.core)] == ASSIGNED[repr(j.core)]) and (ASSIGNED_VARIABLES[repr(i.id)] + 1 == ASSIGNED_VARIABLES[repr(j.id)])
    return (i.core == j.core) & (i.id + 1 == j.id)


@define_fun
def same_vadd(i, j):
    return i.virtual_address == j.virtual_address


@define_fun
def is_fence(i):
    return i.type == UOPType.Fence


def add_edge(src, dest):
    if TRACKED is not None:
        TRACKED.append((src, dest))
    return edge_exists(src, dest)

@define_fun
def edge_exists(src, dest):
    return src.node_exists & dest.node_exists & (src.time < dest.time)


def add_edges(*edges):
    return forall(edges, lambda e:
        add_edge(e[0], e[1])
    )


def edges_exist(*edges):
    return forall(edges, lambda e:
        edge_exists(e[0], e[1])
    )

def nodes_exist(*nodes):
    return forall(nodes, lambda n:
        node_exists(n)
    )


def known_data(i):
    return i.known_data


def same_node(n1, n2):
    return (n1.time == n2.time) & (n1.node_exists == n2.node_exists)


@define_fun
def same_core(i1, i2):
    #if repr(i1.core) in ASSIGNED_VARIABLES and repr(i2.core) in ASSIGNED_VARIABLES:
    #    return CVCBool(ASSIGNED_VARIABLES[repr(i1.core)] == ASSIGNED_VARIABLES[repr(i2.core)])
    return i1.core == i2.core


@define_fun
def program_order(i1, i2):
    #if repr(i1.core) in ASSIGNED_VARIABLES and repr(i2.core) in ASSIGNED_VARIABLES:
    #    return CVCBool((ASSIGNED_VARIABLES[repr(i1.core)] == ASSIGNED_VARIABLES[repr(i2.core)]) and (ASSIGNED_VARIABLES[repr(i1.id)] < ASSIGNED_VARIABLES[repr(i2.id)]))
    return same_core(i1, i2) & (i1.id < i2.id)


def same_mop(i1, i2):
    return i1.id == i2.id


@define_fun
def same_padd(i1, i2):
    #if repr(i1.physical_address) in ASSIGNED_VARIABLES and repr(i2.physical_address) in ASSIGNED_VARIABLES:
    #    return CVCBool(ASSIGNED_VARIABLES[repr(i1.physical_address)] == ASSIGNED_VARIABLES[repr(i2.physical_address)])
    return i1.physical_address == i2.physical_address


@define_fun
def same_data(i1, i2):
    #if repr(i1.data) in ASSIGNED_VARIABLES and repr(i2.data) in ASSIGNED_VARIABLES:
    #    return CVCBool(ASSIGNED_VARIABLES[repr(i1.data)] == ASSIGNED_VARIABLES[repr(i2.data)])
    return i1.data == i2.data


def data_from_final_at_pa(i):
    return False

@define_fun
def data_from_init_at_pa(i):
    return i.data == 0


def start_tracking():
    global TRACKED
    TRACKED = []


def stop_tracking():
    global TRACKED
    result = TRACKED
    TRACKED = None
    return result
