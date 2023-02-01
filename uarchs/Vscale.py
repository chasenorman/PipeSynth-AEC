from synth import *

class Microop(CVCObject):
    type: UOPType
    core: int
    id: int
    physical_address: int
    virtual_address: int
    data: int
    
    rmw_access: bool
    known_data: bool
    data_from_final_state: bool

    fetch: Node
    decode_execute: Node
    writeback: Node


# --- Nodes ------------------
def fetch(i): return i.fetch
def decode_execute(i): return i.decode_execute
def writeback(i): return i.writeback

# --- Macros ------------------
def no_writes_to_same_pa_between_source_and_read(microops, i):
    return exists(microops, lambda w:
        (is_write(w) & same_padd(w, i) & same_data(w, i) & add_edge(writeback(w), writeback(i)) & ~(exists(microops, lambda w1:
            is_write(w1) & same_padd(i, w1) & ~same_mop(w, w1) & edges_exist((writeback(w), writeback(w1)), (writeback(w1), writeback(i)))))))

def before_or_after_every_write_to_same_pa(microops, i):
    return forall(microops, lambda w:
        ((((is_write(w) & same_padd(w, i))) >> ((add_edge(decode_execute(w), decode_execute(i)) | add_edge(decode_execute(i), decode_execute(w)))))))

def before_all_writes(microops, i):
    return data_from_init_at_pa(i) & forall(microops, lambda w:
        ((((is_write(w) & same_padd(w, i) & ~same_mop(i, w))) >> (add_edge(writeback(i), writeback(w))))))

def write_is_before_final(microops):
    return forall(microops, lambda w:
        forall(microops, lambda w1:
            (((is_write(w) & is_write(w1) & same_padd(w, w1) & ~same_mop(w, w1) & data_from_final_at_pa(w1))) >> (add_edge(writeback(w), writeback(w1))))))

def write_serialization(microops, i):
    return forall(microops, lambda i2:
        (((~(same_mop(i, i2)) & is_write(i2) & same_padd(i, i2))) >> ((add_edge(decode_execute(i), decode_execute(i2)) | add_edge(decode_execute(i2), decode_execute(i))))))


# --- Axioms ------------------
def reads(microops):
    return forall(microops, lambda i:
        ((((is_read(i)) >> (add_edges((fetch(i), decode_execute(i)), (decode_execute(i), writeback(i))))))))

def reads2(microops):
    return forall(microops, lambda i:
        ((((is_read(i)) >> ((before_all_writes(microops, i) | (no_writes_to_same_pa_between_source_and_read(microops, i) & before_or_after_every_write_to_same_pa(microops, i))))))))


def reads2_modified(microops):
    return forall(microops, lambda i:
        ((((is_read(i)) >> ((before_all_writes(microops, i) | (no_writes_to_same_pa_between_source_and_read(microops, i) & before_or_after_every_write_to_same_pa(microops, i))))))))



def writes(microops):
    return forall(microops, lambda i:
        ((((is_write(i)) >> (add_edges((fetch(i), decode_execute(i)), (decode_execute(i), writeback(i))))))))

def writes2(microops):
    return forall(microops, lambda i:
        ((((is_write(i)) >> ((write_is_before_final(microops)))))))

def writes3(microops):
    return forall(microops, lambda i:
        ((((is_write(i)) >> ((write_serialization(microops, i)))))))

def po__fetch(microops):
    return forall(microops, lambda i1:
        forall(microops, lambda i2:
            (((program_order(i1, i2))) >> (add_edge(fetch(i1), fetch(i2))))))

def decode_execute_stage_is_in_order(microops):
    return forall(microops, lambda i1:
        forall(microops, lambda i2:
            (((~same_mop(i1, i2) & program_order(i1, i2))) >> (((edge_exists(fetch(i1), fetch(i2))) >> (add_edge(decode_execute(i1), decode_execute(i2))))))))

def writeback_stage_is_in_order(microops):
    return forall(microops, lambda i1:
        forall(microops, lambda i2:
            (((~same_mop(i1, i2) & program_order(i1, i2))) >> (((edge_exists(decode_execute(i1), decode_execute(i2))) >> (add_edge(writeback(i1), writeback(i2))))))))

def total_order_on_dx(microops):
    return forall(microops, lambda i1:
        forall(microops, lambda i2:
            ((~same_mop(i1, i2)) >> ((edge_exists(decode_execute(i1), decode_execute(i2)) | edge_exists(decode_execute(i2), decode_execute(i1)))))))

def dx_order_implies_wb_order(microops):
    return forall(microops, lambda i1:
        forall(microops, lambda i2:
            ((edge_exists(decode_execute(i1), decode_execute(i2))) >> (add_edge(writeback(i1), writeback(i2))))))

nodes = [fetch, decode_execute, writeback]

"""execution_dictionary = {
'w+wrr_positive.test': [[(0, True), (1, True), (2, True)], [(0, True), (2, True), (3, True)], [(1, True), (3, True), (4, True)], [(2, True), (4, True), (5, True)]],
'rw_positive.test': [[(0, True), (1, True), (2, True)], [(1, True), (2, True), (3, True)]],
'2+2w_positive.test': [[(0, True), (1, True), (2, True)], [(1, True), (2, True), (3, True)], [(2, True), (3, True), (4, True)], [(3, True), (4, True), (5, True)]],
'wwr_positive.test': [[(0, True), (1, True), (2, True)], [(1, True), (2, True), (3, True)], [(2, True), (3, True), (4, True)]],
'coww_positive.test': [[(0, True), (1, True), (2, True)], [(1, True), (2, True), (3, True)]],
'corw_positive.test': [[(1, True), (2, True), (3, True)], [(2, True), (3, True), (4, True)], [(0, True), (1, True), (2, True)]],
'lb_positive.test': [[(2, True), (3, True), (4, True)], [(3, True), (4, True), (5, True)], [(0, True), (1, True), (2, True)], [(1, True), (2, True), (3, True)]],
'wr_positive.test': [[(0, True), (1, True), (2, True)], [(1, True), (2, True), (3, True)]],
'mp_positive.test': [[(2, True), (3, True), (4, True)], [(3, True), (4, True), (5, True)], [(0, True), (1, True), (2, True)], [(1, True), (2, True), (3, True)]],
's_positive.test': [[(0, True), (1, True), (2, True)], [(1, True), (3, True), (4, True)], [(1, True), (2, True), (3, True)], [(2, True), (4, True), (5, True)]],
'corr_positive.test': [[(1, True), (2, True), (3, True)], [(2, True), (3, True), (4, True)], [(0, True), (1, True), (2, True)]],
'cowr_positive.test': [[(0, True), (1, True), (2, True)], [(0, True), (2, True), (3, True)], [(1, True), (3, True), (4, True)]],
'comp_positive.test': [[(2, True), (3, True), (4, True)], [(3, True), (4, True), (5, True)], [(0, True), (1, True), (2, True)], [(1, True), (2, True), (3, True)]],
}"""

execution_dictionary = {'w+wrr_positive.test': [[(3, True), (8, True), (9, True)], [(3, True), (4, True), (5, True)], [(4, True), (5, True), (6, True)], [(5, True), (6, True), (7, True)]],
'rw_positive.test': [[(3, True), (8, True), (10, True)], [(8, True), (10, True), (11, True)]],
'2+2w_positive.test': [[(3, True), (8, True), (10, True)], [(8, True), (10, True), (11, True)], [(3, True), (4, True), (5, True)], [(4, True), (5, True), (6, True)]],
'wwr_positive.test': [[(3, True), (8, True), (10, True)], [(8, True), (10, True), (11, True)], [(10, True), (11, True), (12, True)]],
'coww_positive.test': [[(3, True), (8, True), (10, True)], [(8, True), (10, True), (11, True)]],
'corw_positive.test': [[(3, True), (8, True), (10, True)], [(8, True), (10, True), (11, True)], [(3, True), (4, True), (5, True)]],
'lb_positive.test': [[(3, True), (8, True), (10, True)], [(8, True), (10, True), (11, True)], [(3, True), (4, True), (5, True)], [(4, True), (5, True), (6, True)]],
'wr_positive.test': [[(3, True), (8, True), (10, True)], [(8, True), (10, True), (11, True)]],
'mp_positive.test': [[(3, True), (8, True), (10, True)], [(8, True), (10, True), (11, True)], [(3, True), (4, True), (5, True)], [(4, True), (5, True), (6, True)]],
's_positive.test': [[(3, True), (8, True), (10, True)], [(8, True), (10, True), (11, True)], [(3, True), (4, True), (5, True)], [(4, True), (5, True), (6, True)]],
'corr_positive.test': [[(3, True), (8, True), (10, True)], [(8, True), (10, True), (11, True)], [(3, True), (4, True), (5, True)]],
'cowr_positive.test': [[(3, True), (8, True), (9, True)], [(3, True), (4, True), (5, True)], [(4, True), (5, True), (6, True)]],
'comp_positive.test': [[(3, True), (8, True), (10, True)], [(8, True), (10, True), (11, True)], [(3, True), (4, True), (5, True)], [(4, True), (5, True), (6, True)]],
}

allowed_unary = [(fetch, decode_execute), (decode_execute, writeback)]
allowed_binary = [(fetch, fetch), (decode_execute, decode_execute), (writeback, writeback)]

path = path_axiom(Microop, allowed_unary)
fifo = fifo_axiom(Microop, allowed_binary)
sourcing = sourcing_axiom(Microop, allowed_binary)

axioms = [
    reads, # 2.87user (trivial) 3
    reads2, # 82.55user 10
    writes, # 2.85user (trivial) 2
    writes2, # 2.95user (trivial) 5
    writes3, # 2.69user (trivial) 1
    po__fetch, # 28.1user 8
    decode_execute_stage_is_in_order, # 11.96user 7
    writeback_stage_is_in_order, # 3.19user (trivial) 6
    total_order_on_dx, # 2.92user (trivial) 4
    dx_order_implies_wb_order, # 35.89user 9
]


structure = {
    reads: {path},
    reads2: {fifo, sourcing},
    writes: {path},
    writes2: {fifo},
    writes3: {fifo}, # requires entanglement
    po__fetch: {fifo},
    decode_execute_stage_is_in_order: {fifo},
    writeback_stage_is_in_order: {fifo},
    total_order_on_dx: {fifo},
    dx_order_implies_wb_order: {fifo},
}

axiom_names = {
    'reads': reads, # 2.87user (trivial) 3
    'reads2': reads2, # 82.55user 10
    'writes': writes, # 2.85user (trivial) 2
    'writes2': writes2, # 2.95user (trivial) 5
    'writes3': writes3, # 2.69user (trivial) 1
    'pofetch': po__fetch, # 28.1user 8
    'decodeexecutestageisinorder': decode_execute_stage_is_in_order, # 11.96user 7
    'writebackstageisinorder': writeback_stage_is_in_order, # 3.19user (trivial) 6
    'totalorderondx': total_order_on_dx, # 2.92user (trivial) 4
    'dxorderimplieswborder': dx_order_implies_wb_order, # 35.89user 9
}

co_node = decode_execute
suite = 'litmus-vscale'

Vscale = Microarchitecture(suite,
                           axioms,
                           Microop,
                           nodes,
                           co_node,
                           execution_dictionary,
                           structure,
                           "Vscale",
                           allowed_unary,
                           allowed_binary,
                           axiom_names)