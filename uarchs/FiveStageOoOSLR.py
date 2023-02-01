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
    decode: Node
    execute: Node
    memory_stage: Node
    cache_line_invalidated: Node
    writeback: Node
    store_buffer: Node
    memory_hierarchy: Node


# --- Nodes ------------------
def fetch(i): return i.fetch
def decode(i): return i.decode
def execute(i): return i.execute
def memory_stage(i): return i.memory_stage
def cache_line_invalidated(i): return i.cache_line_invalidated
def writeback(i): return i.writeback
def store_buffer(i): return i.store_buffer
def memory_hierarchy(i): return i.memory_hierarchy

# --- Macros ------------------
def is_latest_matching_stb_entry(microops, w, i):
    return ~exists(microops, lambda w1:
        is_write(w1) & same_vadd(w, w1) & same_core(w, w1) & program_order(w, w1) & program_order(w1, i))

def stb_fwd(microops, i):
    return exists(microops, lambda w:
        (is_write(w) & same_core(w, i) & same_vadd(w, i) & same_data(w, i) & program_order(w, i) & add_edges((memory_stage(w), memory_stage(i)), (memory_stage(i), memory_hierarchy(w)))) & is_latest_matching_stb_entry(microops, w, i))

def stb_empty(microops, i):
    return forall(microops, lambda w:
        ((((is_write(w) & same_core(w, i) & same_vadd(w, i) & program_order(w, i))) >> (add_edge(memory_hierarchy(w), memory_stage(i))))))

def no_writes_to_same_pa_between_source_and_read(microops, i):
    return exists(microops, lambda w:
        (is_write(w) & same_padd(w, i) & same_data(w, i) & add_edge(memory_hierarchy(w), memory_stage(i)) & ~(exists(microops, lambda w1:
            same_padd(i, w1) & edges_exist((memory_hierarchy(w), memory_hierarchy(w1)), (memory_hierarchy(w1), memory_stage(i)))))))

def before_or_after_every_write_to_same_pa(microops, i):
    return forall(microops, lambda w:
        ((((is_write(w) & same_padd(w, i))) >> ((add_edge(memory_hierarchy(w), memory_stage(i)) | add_edge(cache_line_invalidated(i), memory_hierarchy(w)))))))

def before_all_writes(microops, i):
    return data_from_init_at_pa(i) & forall(microops, lambda w:
        ((((is_write(w) & same_padd(w, i) & ~same_mop(i, w))) >> (add_edge(cache_line_invalidated(i), memory_hierarchy(w))))))

def write_is_before_final(microops):
    return forall(microops, lambda w:
        forall(microops, lambda w1:
            (((is_write(w) & is_write(w1) & same_padd(w, w1) & ~same_mop(w, w1) & data_from_final_at_pa(w1))) >> (add_edge(memory_hierarchy(w), memory_hierarchy(w1))))))


# --- Axioms ------------------
def write_serialization(microops):
    return ((forall(microops, lambda i1:
        forall(microops, lambda i2:
            (((~(same_mop(i1, i2)) & is_write(i1) & is_write(i2) & same_padd(i1, i2))) >> ((add_edge(memory_hierarchy(i1), memory_hierarchy(i2)) | add_edge(memory_hierarchy(i2), memory_hierarchy(i1)))))))))

def reads(microops):
    return forall(microops, lambda i:
        ((is_read(i)) >> (add_edges((fetch(i), decode(i)), (decode(i), execute(i)), (execute(i), memory_stage(i)), (memory_stage(i), writeback(i)), (memory_stage(i), cache_line_invalidated(i))) & (stb_fwd(microops, i) | (stb_empty(microops, i) & (before_all_writes(microops, i) | (no_writes_to_same_pa_between_source_and_read(microops, i) & before_or_after_every_write_to_same_pa(microops, i))))))))


def writes(microops):
    return forall(microops, lambda i:
        ((is_write(i)) >> (add_edges((fetch(i), decode(i)), (decode(i), execute(i)), (execute(i), memory_stage(i)), (memory_stage(i), writeback(i)), (writeback(i), store_buffer(i)), (store_buffer(i), memory_hierarchy(i))) & (write_is_before_final(microops)) & (forall(microops, lambda w:
            ((((is_write(w) & same_core(w, i) & program_order(i, w))) >> (add_edges((memory_hierarchy(i), store_buffer(w)))))))))))


def mfence(microops):
    return forall(microops, lambda f:
        ((is_fence(f)) >> (add_edges((fetch(f), decode(f)), (decode(f), execute(f)), (execute(f), memory_stage(f)), (memory_stage(f), writeback(f))) & (forall(microops, lambda w:
            ((((is_write(w) & same_core(w, f) & program_order(w, f))) >> (add_edge(memory_hierarchy(w), execute(f)))))) & (forall(microops, lambda r:
            ((((is_read(r) & same_core(r, f) & program_order(f, r))) >> (add_edge(execute(f), memory_stage(r)))))))))))

def rmw(microops):
    return forall(microops, lambda w:
        ((is_write(w)) >> (((access_type_rmw(w)) >> ((forall(microops, lambda i2:
            ((program_order(w, i2)) >> (is_read(i2) & add_edge(memory_hierarchy(w), memory_stage(i2))))) & (exists(microops, lambda r:
            consecutive(r, w) & is_read(r) & access_type_rmw(r) & ~exists(microops, lambda w1:
                is_write(w1) & same_padd(w, w1) & edges_exist((memory_stage(r), memory_hierarchy(w1)), (memory_hierarchy(w1), memory_hierarchy(w))))))))))))

def po__fetch(microops):
    return forall(microops, lambda i1:
        forall(microops, lambda i2:
            ((program_order(i1, i2)) >> (add_edge(fetch(i1), fetch(i2))))))

def decode_stage_is_in_order(microops):
    return forall(microops, lambda i1:
        forall(microops, lambda i2:
            ((edge_exists(fetch(i1), fetch(i2))) >> (((nodes_exist(decode(i1), decode(i2))) >> (add_edge(decode(i1), decode(i2))))))))

def writeback_is_in_decode_order(microops):
    return forall(microops, lambda i1:
        forall(microops, lambda i2:
            ((edge_exists(decode(i1), decode(i2))) >> (((nodes_exist(writeback(i1), writeback(i2))) >> (add_edge(writeback(i1), writeback(i2))))))))

def stb_fifo(microops):
    return forall(microops, lambda i1:
        forall(microops, lambda i2:
            ((edge_exists(writeback(i1), writeback(i2))) >> (((nodes_exist(store_buffer(i1), store_buffer(i2))) >> (add_edge(store_buffer(i1), store_buffer(i2))))))))

def slr(microops):
    return forall(microops, lambda i1:
        forall(microops, lambda i2:
            ((is_read(i1) & is_read(i2) & program_order(i1, i2)) >> (add_edge(cache_line_invalidated(i1), memory_stage(i2))))))

nodes = [fetch, decode, execute, memory_stage, cache_line_invalidated, writeback, store_buffer, memory_hierarchy]

execution_dictionary = {
'w+wrr_positive.test': [[(1, True), (2, True), (3, True), (4, True), (0, True), (5, True), (6, True), (7, True)], [(0, True), (1, True), (2, True), (3, True), (0, True), (4, True), (5, True), (6, True)], [(1, True), (2, True), (3, True), (8, True), (9, True), (9, True), (7, True), (0, True)], [(2, True), (3, True), (4, True), (10, True), (11, True), (11, True), (8, True), (0, True)]],
'rw_positive.test': [[(0, True), (1, True), (2, True), (3, True), (4, True), (4, True), (0, False), (0, True)], [(1, True), (2, True), (3, True), (4, True), (0, True), (5, True), (6, True), (7, True)]],
'2+2w_positive.test': [[(1, True), (2, True), (3, True), (4, True), (0, True), (5, True), (6, True), (9, True)], [(2, True), (3, True), (4, True), (5, True), (0, True), (6, True), (10, True), (11, True)], [(0, True), (1, True), (2, True), (3, True), (0, True), (4, True), (5, True), (6, True)], [(1, True), (2, True), (3, True), (4, True), (0, True), (5, True), (7, True), (8, True)]],
'rmw1_positive.test': [[(0, True), (1, True), (2, True), (3, True), (6, True), (4, True), (0, True), (0, True)], [(1, True), (2, True), (3, True), (4, True), (0, True), (5, True), (6, True), (7, True)], [(0, True), (1, True), (2, True), (3, True), (0, True), (4, True), (5, True), (8, True)]],
'rmw2_positive.test': [[(1, True), (2, True), (3, True), (4, True), (0, True), (5, True), (6, True), (7, True)], [(0, True), (1, True), (2, True), (3, True), (0, True), (4, True), (5, True), (8, True)], [(1, True), (2, True), (3, True), (9, True), (10, True), (10, True), (7, True), (0, True)], [(2, True), (3, True), (4, True), (5, True), (0, True), (11, True), (12, True), (13, True)]],
'wwr_positive.test': [[(0, True), (1, True), (2, True), (3, True), (0, True), (4, True), (5, True), (6, True)], [(1, True), (2, True), (3, True), (4, True), (0, True), (5, True), (7, True), (8, True)], [(2, True), (3, True), (4, True), (9, True), (10, True), (10, True), (0, False), (0, True)]],
'coww_positive.test': [[(0, True), (1, True), (2, True), (3, True), (0, True), (4, True), (5, True), (6, True)], [(1, True), (2, True), (3, True), (4, True), (0, True), (5, True), (7, True), (8, True)]],
'corw_positive.test': [[(0, True), (1, True), (2, True), (7, True), (8, True), (8, True), (6, True), (0, True)], [(1, True), (2, True), (3, True), (4, True), (0, True), (9, True), (10, True), (11, True)], [(0, True), (1, True), (2, True), (3, True), (0, True), (4, True), (5, True), (6, True)]],
'lb_positive.test': [[(0, True), (1, True), (2, True), (3, True), (4, True), (4, True), (0, True), (0, True)], [(1, True), (2, True), (3, True), (4, True), (0, True), (5, True), (6, True), (7, True)], [(1, True), (2, True), (3, True), (8, True), (9, True), (9, True), (7, True), (0, True)], [(2, True), (3, True), (4, True), (5, True), (0, True), (10, True), (11, True), (12, True)]],
'wr_positive.test': [[(0, True), (1, True), (2, True), (3, True), (0, True), (4, True), (5, True), (6, True)], [(1, True), (2, True), (3, True), (7, True), (8, True), (8, True), (0, False), (0, True)]],
'w+w+rr_positive.test': [[(0, True), (1, True), (2, True), (7, True), (8, True), (8, True), (6, True), (0, True)], [(1, True), (2, True), (3, True), (10, True), (11, True), (11, True), (7, True), (0, True)], [(0, True), (1, True), (2, True), (3, True), (0, True), (4, True), (5, True), (6, True)], [(0, True), (1, True), (2, True), (3, True), (0, True), (4, True), (5, True), (9, True)]],
'mp_positive.test': [[(0, True), (1, True), (2, True), (3, True), (0, True), (4, True), (5, True), (6, True)], [(1, True), (2, True), (3, True), (4, True), (0, True), (6, True), (7, True), (8, True)], [(1, True), (2, True), (3, True), (9, True), (10, True), (10, True), (8, True), (0, True)], [(2, True), (3, True), (4, True), (11, True), (12, True), (12, True), (9, True), (0, True)]],
's_positive.test': [[(0, True), (1, True), (2, True), (3, True), (0, True), (4, True), (5, True), (6, True)], [(1, True), (2, True), (3, True), (4, True), (0, True), (6, True), (7, True), (8, True)], [(1, True), (2, True), (3, True), (9, True), (10, True), (10, True), (8, True), (0, True)], [(2, True), (3, True), (4, True), (5, True), (0, True), (11, True), (12, True), (13, True)]],
'corr_positive.test': [[(0, True), (1, True), (2, True), (3, True), (4, True), (4, True), (0, True), (0, True)], [(1, True), (2, True), (3, True), (5, True), (6, True), (6, True), (6, True), (0, True)], [(0, True), (1, True), (2, True), (3, True), (0, True), (4, True), (5, True), (7, True)]],
'rmw3_positive.test': [[(1, True), (2, True), (3, True), (7, True), (8, True), (8, True), (6, True), (0, True)], [(2, True), (3, True), (4, True), (5, True), (0, True), (9, True), (10, True), (11, True)], [(0, True), (1, True), (2, True), (3, True), (0, True), (4, True), (5, True), (6, True)], [(1, True), (2, True), (3, True), (4, True), (0, True), (8, True), (9, True), (12, True)]],
'cowr_positive.test': [[(1, True), (2, True), (3, True), (4, True), (0, True), (5, True), (6, True), (7, True)], [(0, True), (1, True), (2, True), (3, True), (0, True), (4, True), (5, True), (6, True)], [(1, True), (2, True), (3, True), (8, True), (9, True), (9, True), (7, True), (0, True)]],
'comp_positive.test': [[(0, True), (1, True), (2, True), (3, True), (0, True), (4, True), (5, True), (6, True)], [(1, True), (2, True), (3, True), (4, True), (0, True), (6, True), (7, True), (8, True)], [(1, True), (2, True), (3, True), (9, True), (10, True), (10, True), (8, True), (0, True)], [(2, True), (3, True), (4, True), (11, True), (12, True), (12, True), (9, True), (0, True)]],
'rmw4_positive.test': [[(0, True), (1, True), (2, True), (7, True), (8, True), (8, True), (6, True), (0, True)], [(1, True), (2, True), (3, True), (4, True), (0, True), (9, True), (10, True), (11, True)], [(0, True), (1, True), (2, True), (3, True), (0, True), (4, True), (5, True), (6, True)], [(0, True), (1, True), (2, True), (3, True), (0, True), (4, True), (5, True), (12, True)]],
}

allowed_unary = [(fetch, decode), (decode, execute), (execute, memory_stage), (memory_stage, cache_line_invalidated), (writeback, store_buffer), (store_buffer, memory_hierarchy), (memory_stage, writeback)]
allowed_binary = [
    (memory_stage, memory_stage),
    (cache_line_invalidated, memory_hierarchy),
    (memory_hierarchy, store_buffer),
    (memory_hierarchy, execute),
    (execute, memory_stage),
    (memory_hierarchy, memory_stage),
    (memory_stage, memory_hierarchy),
    (memory_hierarchy, memory_hierarchy),
    (fetch, fetch),
    (decode, decode),
    (writeback, writeback),
    (store_buffer, store_buffer),
    (cache_line_invalidated, memory_stage),
]

path = path_axiom(Microop, allowed_unary)
fifo = fifo_axiom(Microop, allowed_binary)
fifo2 = fifo_axiom(Microop, allowed_binary)
fifo3 = fifo_axiom(Microop, allowed_binary)
sourcing = sourcing_axiom(Microop, allowed_binary)

axioms = [
    write_serialization, # 810.50user 6
    reads,
    writes, # 5486.21user 9
    mfence, # 42.93user (trivial) 2
    rmw, # 643.94user 8
    po__fetch, # 182.71user 3
    decode_stage_is_in_order, # 639.97user 4
    writeback_is_in_decode_order, # 762.63user 5
    stb_fifo, # 12.20user (trivial) 1
    slr, # 1155.38user 7
]


structure = {
    write_serialization: {fifo},
    reads: {path, fifo, fifo2, fifo3, sourcing},
    writes: {path, fifo},
    mfence: {},
    rmw: {sourcing},
    po__fetch: {fifo},
    decode_stage_is_in_order: {fifo},
    writeback_is_in_decode_order: {fifo},
    stb_fifo: {fifo},
    slr: {fifo},
}

axiom_names = {
    'writeserialization': write_serialization, # 810.50user 6
    'reads': reads,
    'writes': writes, # 5486.21user 9
    'mfence': mfence, # 42.93user (trivial) 2
    'rmw': rmw, # 643.94user 8
    'pofetch': po__fetch, # 182.71user 3
    'decodestageisinorder': decode_stage_is_in_order, # 639.97user 4
    'writebackisindecodeorder': writeback_is_in_decode_order, # 762.63user 5
    'stbfifo': stb_fifo, # 12.20user (trivial) 1
    'slr': slr, # 1155.38user 7
}

co_node = memory_hierarchy
suite = 'litmus'

FiveStageOoOSLR = Microarchitecture(suite,
                                    axioms,
                                    Microop,
                                    nodes,
                                    co_node,
                                    execution_dictionary,
                                    structure,
                                    "FiveStageOoOSLR",
                                    allowed_unary,
                                    allowed_binary,
                                    axiom_names)