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
    writeback: Node
    store_buffer: Node
    vi_cl_request: Node
    vi_cl_create: Node
    vi_cl_invalidate: Node
    vi_cl_expire: Node


# --- Nodes ------------------
def fetch(i): return i.fetch
def decode(i): return i.decode
def execute(i): return i.execute
def memory_stage(i): return i.memory_stage
def writeback(i): return i.writeback
def store_buffer(i): return i.store_buffer
def vi_cl_request(i): return i.vi_cl_request
def vi_cl_create(i): return i.vi_cl_create
def vi_cl_invalidate(i): return i.vi_cl_invalidate
def vi_cl_expire(i): return i.vi_cl_expire

# --- Macros ------------------
def stb_fwd(microops, i):
    return exists(microops, lambda w:
        is_write(w) & same_vadd(w, i) & same_core(w, i) & same_data(w, i) & add_edges((memory_stage(w), memory_stage(i)), (memory_stage(i), vi_cl_create(w))) & ~exists(microops, lambda w1:
            is_write(w1) & same_vadd(w, w1) & same_core(w, w1) & program_order(w, w1) & program_order(w1, i)))

def stb_empty(microops, i):
    return forall(microops, lambda w:
        (((is_write(w)) >> (((same_core(w, i)) >> (((same_vadd(w, i)) >> (((program_order(w, i)) >> (add_edge(vi_cl_create(w), memory_stage(i))))))))))))

def find_l1_vi_cl_normal(microops, i):
    return exists(microops, lambda s:
        (same_padd(s, i) & same_data(s, i) & same_core(s, i) & add_edges((vi_cl_create(s), memory_stage(i)), (memory_stage(i), vi_cl_invalidate(s)), (vi_cl_create(s), vi_cl_invalidate(s)))))

def find_l1_vi_cl_peekaboo(microops, i):
    return (~access_type_rmw(i)) & add_edges((vi_cl_invalidate(i), vi_cl_create(i)), (vi_cl_create(i), memory_stage(i)), (memory_stage(i), vi_cl_expire(i))) & forall(microops, lambda i1:
        ((program_order(i1, i)) >> (((((is_read(i1)) >> (add_edge(memory_stage(i1), vi_cl_request(i))))) & (((is_write(i1)) >> (add_edge(vi_cl_create(i1), vi_cl_request(i)))))))))

def find_l1_vi_cl(microops, i):
    return find_l1_vi_cl_normal(microops, i) | find_l1_vi_cl_peekaboo(microops, i)

def l1_vi_cl_source_initial(microops, i):
    return data_from_init_at_pa(i) & forall(microops, lambda w:
        (((is_write(w)) >> (((same_padd(w, i)) >> (((~same_mop(i, w)) >> (add_edge(vi_cl_invalidate(i), vi_cl_create(w))))))))))

def l1_vi_cl_source(microops, i):
    return exists(microops, lambda i1:
        (same_padd(i, i1) & ~same_mop(i, i1) & same_data(i, i1) & add_edge(vi_cl_create(i1), vi_cl_create(i)) & add_edge(vi_cl_create(i1), vi_cl_invalidate(i1)) & ~exists(microops, lambda i2:
            same_padd(i, i2) & is_write(i2) & edges_exist((vi_cl_create(i1), vi_cl_create(i2)), (vi_cl_create(i2), vi_cl_create(i))))))

# --- Axioms ------------------
def write_is_before_final(microops):
    return forall(microops, lambda w:
        (forall(microops, lambda w1:
            ((is_write(w)) >> (((is_write(w1)) >> (((same_padd(w, w1)) >> (((~same_mop(w, w1)) >> (((data_from_final_at_pa(w1)) >> (add_edge(vi_cl_invalidate(w), vi_cl_create(w1)))))))))))))))

def reads(microops):
    return forall(microops, lambda i:
        ((is_read(i)) >> (add_edges((fetch(i), decode(i)), (decode(i), execute(i)), (execute(i), memory_stage(i)), (memory_stage(i), writeback(i))) & (((known_data(i)) >> ((stb_fwd(microops, i) | (stb_empty(microops, i) & find_l1_vi_cl(microops, i)))))))))

def writes(microops):
    return forall(microops, lambda i:
        ((is_write(i)) >> (add_edges((fetch(i), decode(i)), (decode(i), execute(i)), (execute(i), memory_stage(i)), (memory_stage(i), writeback(i)), (writeback(i), store_buffer(i)), (store_buffer(i), vi_cl_create(i)), (vi_cl_create(i), vi_cl_invalidate(i)), (vi_cl_invalidate(i), vi_cl_expire(i))))))

def mfence(microops):
    return forall(microops, lambda f:
        ((is_fence(f)) >> (add_edges((fetch(f), decode(f)), (decode(f), execute(f)), (execute(f), memory_stage(f)), (memory_stage(f), writeback(f))) & (forall(microops, lambda w:
            ((((is_write(w) & same_core(w, f) & program_order(w, f))) >> (add_edge(vi_cl_create(w), execute(f))))))))))

def rmw(microops):
    return forall(microops, lambda w:
        ((is_write(w)) >> (((access_type_rmw(w)) >> ((forall(microops, lambda i2:
            ((program_order(w, i2)) >> (is_read(i2) & add_edge(vi_cl_create(w), memory_stage(i2))))) & (exists(microops, lambda r:
            consecutive(r, w) & is_read(r) & access_type_rmw(r) & ~exists(microops, lambda w1:
                is_write(w1) & same_padd(w, w1) & edges_exist((memory_stage(r), vi_cl_create(w1)), (vi_cl_create(w1), vi_cl_create(w))))))))))))

def po__fetch(microops):
    return forall(microops, lambda i1:
        forall(microops, lambda i2:
            (((same_core(i1, i2) & program_order(i1, i2))) >> (add_edge(fetch(i1), fetch(i2))))))

def decode_stage_is_in_order(microops):
    return forall(microops, lambda i1:
        forall(microops, lambda i2:
            (((same_core(i1, i2) >> (((edge_exists(fetch(i1), fetch(i2))) >> (((nodes_exist(decode(i1), decode(i2))) >> (add_edge(decode(i1), decode(i2))))))))))))

def execute_stage_is_in_order(microops):
    return forall(microops, lambda i1:
        forall(microops, lambda i2:
            (((same_core(i1, i2) >> (((edge_exists(decode(i1), decode(i2))) >> (((nodes_exist(execute(i1), execute(i2))) >> (add_edge(execute(i1), execute(i2))))))))))))

def memory_stage_is_in_order(microops):
    return forall(microops, lambda i1:
        forall(microops, lambda i2:
            (((same_core(i1, i2) >> (((edge_exists(execute(i1), execute(i2))) >> (((nodes_exist(memory_stage(i1), memory_stage(i2))) >> (add_edge(memory_stage(i1), memory_stage(i2))))))))))))

def writeback_stage_is_in_order(microops):
    return forall(microops, lambda i1:
        forall(microops, lambda i2:
            (((same_core(i1, i2) >> (((edge_exists(memory_stage(i1), memory_stage(i2))) >> (((nodes_exist(writeback(i1), writeback(i2))) >> (add_edge(writeback(i1), writeback(i2))))))))))))

def stb_fifo(microops):
    return forall(microops, lambda i1:
        forall(microops, lambda i2:
            (((same_core(i1, i2) >> (((edge_exists(writeback(i1), writeback(i2))) >> (((nodes_exist(store_buffer(i1), store_buffer(i2))) >> (add_edge(store_buffer(i1), store_buffer(i2))))))))))))

def stb__one_at_a_time(microops):
    return forall(microops, lambda i1:
        forall(microops, lambda i2:
            (((same_core(i1, i2) >> (((edge_exists(store_buffer(i1), store_buffer(i2))) >> (((nodes_exist(vi_cl_create(i1), store_buffer(i2))) >> (add_edge(vi_cl_create(i1), store_buffer(i2))))))))))))

def l1_vi_c_ls(microops):
    return forall(microops, lambda i:
        (((is_read(i)) >> ((((node_exists(vi_cl_create(i)) | node_exists(vi_cl_expire(i)) | node_exists(vi_cl_request(i)) | node_exists(vi_cl_invalidate(i)))) >> ((add_edges((vi_cl_request(i), vi_cl_create(i)), (vi_cl_request(i), vi_cl_invalidate(i)), (vi_cl_create(i), vi_cl_expire(i)), (vi_cl_invalidate(i), vi_cl_expire(i))) & (l1_vi_cl_source_initial(microops, i) | l1_vi_cl_source(microops, i)))))))))

def swmr(microops):
    return ((forall(microops, lambda i1:
        ((is_write(i1)) >> ((((node_exists(vi_cl_create(i1)) | node_exists(vi_cl_expire(i1)) | node_exists(vi_cl_request(i1)) | node_exists(vi_cl_invalidate(i1)))) >> (forall(microops, lambda i2:
            (((node_exists(vi_cl_create(i2)) | node_exists(vi_cl_expire(i2)) | node_exists(vi_cl_request(i2)) | node_exists(vi_cl_invalidate(i2)))) >> ((((~same_mop(i1, i2))) >> (((is_write(i1)) >> (((same_padd(i1, i2)) >> (((add_edge(vi_cl_invalidate(i2), vi_cl_create(i1))) | (add_edge(vi_cl_create(i1), vi_cl_create(i2))))))))))))))))))))

def l1_vi_cl_no_dups(microops):
    return ((forall(microops, lambda i1:
        ((((node_exists(vi_cl_create(i1)) | node_exists(vi_cl_expire(i1)) | node_exists(vi_cl_request(i1)) | node_exists(vi_cl_invalidate(i1)))) >> (forall(microops, lambda i2:
            ((((~same_mop(i1, i2))) >> (((same_core(i1, i2)) >> (((same_padd(i1, i2)) >> ((((node_exists(vi_cl_create(i2)) | node_exists(vi_cl_expire(i2)) | node_exists(vi_cl_request(i2)) | node_exists(vi_cl_invalidate(i2)))) >> (add_edge(vi_cl_expire(i1), vi_cl_create(i2)) | add_edge(vi_cl_expire(i2), vi_cl_create(i1))))))))))))))))))

nodes = [fetch, decode, execute, memory_stage, writeback, store_buffer, vi_cl_request, vi_cl_create, vi_cl_invalidate, vi_cl_expire]

execution_dictionary = {
'w+wrr_positive.test': [[(0, True), (1, True), (2, True), (3, True), (4, True), (5, True), (0, True), (8, True), (9, True), (10, True)], [(0, True), (1, True), (2, True), (3, True), (4, True), (5, True), (0, True), (6, True), (7, True), (8, True)], [(1, True), (2, True), (3, True), (10, True), (11, True), (7, True), (0, False), (1, False), (0, False), (0, False)], [(2, True), (3, True), (4, True), (11, True), (12, True), (8, True), (0, True), (9, True), (12, True), (13, True)]],
'rw_positive.test': [[(0, True), (1, True), (2, True), (3, True), (4, True), (0, True), (0, True), (2, True), (1, True), (4, True)], [(1, True), (2, True), (3, True), (4, True), (5, True), (6, True), (0, True), (7, True), (8, True), (9, True)]],
'2+2w_positive.test': [[(0, True), (1, True), (2, True), (3, True), (4, True), (9, True), (0, True), (10, True), (11, True), (12, True)], [(1, True), (2, True), (3, True), (4, True), (5, True), (11, True), (0, True), (12, True), (13, True), (14, True)], [(0, True), (1, True), (2, True), (3, True), (4, True), (5, True), (0, True), (6, True), (7, True), (8, True)], [(1, True), (2, True), (3, True), (4, True), (5, True), (7, True), (0, True), (8, True), (9, True), (10, True)]],
'rmw1_positive.test': [[(0, True), (1, True), (2, True), (3, True), (4, True), (0, False), (1, True), (2, True), (4, True), (5, True)], [(1, True), (2, True), (3, True), (4, True), (5, True), (6, True), (0, True), (7, True), (8, True), (9, True)], [(0, True), (1, True), (2, True), (3, True), (4, True), (5, True), (0, True), (9, True), (10, True), (11, True)]],
'rmw2_positive.test': [[(0, True), (1, True), (2, True), (3, True), (4, True), (5, True), (0, True), (6, True), (7, True), (8, True)], [(0, True), (1, True), (2, True), (5, True), (6, True), (7, True), (0, True), (8, True), (10, True), (11, True)], [(1, True), (2, True), (3, True), (9, True), (10, True), (9, True), (4, True), (12, True), (5, True), (13, True)], [(2, True), (3, True), (4, True), (10, True), (11, True), (13, True), (0, True), (14, True), (15, True), (16, True)]],
'wwr_positive.test': [[(0, True), (1, True), (2, True), (3, True), (4, True), (5, True), (0, True), (6, True), (7, True), (8, True)], [(1, True), (2, True), (3, True), (4, True), (5, True), (7, True), (0, True), (9, True), (11, True), (12, True)], [(2, True), (3, True), (4, True), (10, True), (11, True), (10, True), (0, False), (1, False), (0, False), (0, False)]],
'coww_positive.test': [[(0, True), (1, True), (2, True), (3, True), (4, True), (5, True), (0, True), (6, True), (7, True), (8, True)], [(1, True), (2, True), (3, True), (4, True), (5, True), (7, True), (0, True), (9, True), (10, True), (11, True)]],
'corw_positive.test': [[(0, True), (1, True), (2, True), (8, True), (9, True), (0, True), (0, True), (7, True), (1, True), (9, True)], [(1, True), (2, True), (3, True), (9, True), (10, True), (11, True), (0, True), (12, True), (13, True), (14, True)], [(0, True), (1, True), (2, True), (3, True), (4, True), (5, True), (0, True), (6, True), (7, True), (8, True)]],
'lb_positive.test': [[(0, True), (1, True), (2, True), (3, True), (4, True), (0, True), (0, True), (2, True), (1, True), (4, True)], [(1, True), (2, True), (3, True), (4, True), (5, True), (6, True), (0, True), (7, True), (8, True), (9, True)], [(0, True), (1, True), (2, True), (9, True), (10, True), (0, True), (0, True), (8, True), (1, True), (10, True)], [(1, True), (2, True), (3, True), (10, True), (11, True), (12, True), (0, True), (13, True), (14, True), (15, True)]],
'wr_positive.test': [[(0, True), (1, True), (2, True), (3, True), (4, True), (5, True), (0, True), (6, True), (8, True), (9, True)], [(1, True), (2, True), (3, True), (7, True), (8, True), (7, True), (0, False), (1, False), (0, False), (0, False)]],
'w+w+rr_positive.test': [[(0, True), (1, True), (2, True), (8, True), (9, True), (0, True), (0, True), (7, True), (1, True), (9, True)], [(1, True), (2, True), (3, True), (13, True), (14, True), (8, True), (9, True), (12, True), (10, True), (14, True)], [(0, True), (1, True), (2, True), (3, True), (4, True), (5, True), (0, True), (6, True), (7, True), (8, True)], [(0, True), (1, True), (2, True), (3, True), (4, True), (5, True), (0, True), (11, True), (12, True), (13, True)]],
'mp_positive.test': [[(0, True), (1, True), (2, True), (3, True), (4, True), (5, True), (0, True), (6, True), (7, True), (8, True)], [(1, True), (2, True), (3, True), (4, True), (5, True), (7, True), (0, True), (8, True), (9, True), (10, True)], [(0, True), (1, True), (2, True), (10, True), (11, True), (0, True), (0, True), (9, True), (1, True), (11, True)], [(1, True), (2, True), (3, True), (14, True), (15, True), (10, True), (11, True), (13, True), (12, True), (15, True)]],
's_positive.test': [[(0, True), (1, True), (2, True), (3, True), (4, True), (5, True), (0, True), (6, True), (7, True), (8, True)], [(1, True), (2, True), (3, True), (4, True), (5, True), (7, True), (0, True), (8, True), (9, True), (10, True)], [(0, True), (1, True), (2, True), (10, True), (11, True), (0, True), (0, True), (9, True), (1, True), (11, True)], [(1, True), (2, True), (3, True), (11, True), (12, True), (13, True), (0, True), (14, True), (15, True), (16, True)]],
'corr_positive.test': [[(0, True), (1, True), (2, True), (3, True), (4, True), (0, True), (0, False), (1, False), (0, False), (0, False)], [(1, True), (2, True), (3, True), (4, True), (5, True), (1, True), (0, True), (1, True), (5, True), (6, True)], [(0, True), (1, True), (2, True), (3, True), (4, True), (5, True), (0, True), (6, True), (7, True), (8, True)]],
'rmw3_positive.test': [[(0, True), (1, True), (2, True), (8, True), (9, True), (0, False), (0, True), (7, True), (9, True), (10, True)], [(1, True), (2, True), (3, True), (9, True), (10, True), (11, True), (0, True), (12, True), (13, True), (14, True)], [(0, True), (1, True), (2, True), (3, True), (4, True), (5, True), (0, True), (6, True), (7, True), (8, True)], [(1, True), (2, True), (3, True), (4, True), (5, True), (7, True), (0, True), (14, True), (15, True), (16, True)]],
'cowr_positive.test': [[(0, True), (1, True), (2, True), (3, True), (4, True), (5, True), (0, True), (9, True), (10, True), (11, True)], [(0, True), (1, True), (2, True), (3, True), (4, True), (5, True), (0, True), (6, True), (7, True), (8, True)], [(1, True), (2, True), (3, True), (11, True), (12, True), (7, True), (7, True), (10, True), (8, True), (12, True)]],
'comp_positive.test': [[(0, True), (1, True), (2, True), (3, True), (4, True), (5, True), (0, True), (6, True), (7, True), (8, True)], [(1, True), (2, True), (3, True), (4, True), (5, True), (7, True), (0, True), (9, True), (10, True), (11, True)], [(0, True), (1, True), (2, True), (11, True), (12, True), (0, True), (0, False), (1, False), (0, False), (0, False)], [(1, True), (2, True), (3, True), (12, True), (13, True), (1, True), (0, True), (10, True), (13, True), (14, True)]],
'rmw4_positive.test': [[(0, True), (1, True), (2, True), (8, True), (9, True), (0, False), (0, True), (7, True), (9, True), (10, True)], [(1, True), (2, True), (3, True), (9, True), (10, True), (11, True), (0, True), (12, True), (13, True), (14, True)], [(0, True), (1, True), (2, True), (3, True), (4, True), (5, True), (0, True), (6, True), (7, True), (8, True)], [(0, True), (1, True), (2, True), (3, True), (4, True), (5, True), (0, True), (14, True), (15, True), (16, True)]],
}

allowed_unary = [
    (vi_cl_invalidate, vi_cl_create),
    (vi_cl_create, memory_stage),
    (memory_stage, vi_cl_expire),
    (vi_cl_request, vi_cl_create),
    (vi_cl_request, vi_cl_invalidate),
    (vi_cl_create, vi_cl_expire),
    (writeback, store_buffer),
    (store_buffer, vi_cl_create),
    (vi_cl_invalidate, vi_cl_expire),
    (fetch, decode),
    (decode, execute),
    (execute, memory_stage),
    (memory_stage, writeback),
    (vi_cl_create, vi_cl_invalidate)
]

allowed_binary = [
    (memory_stage, vi_cl_invalidate),
    (memory_stage, vi_cl_request),
    (vi_cl_create, vi_cl_request),
    (vi_cl_create, execute),
    (vi_cl_create, memory_stage),
    (memory_stage, vi_cl_create),
    (fetch, fetch),
    (decode, decode),
    (execute, execute),
    (memory_stage, memory_stage),
    (writeback, writeback),
    (store_buffer, store_buffer),
    (vi_cl_create, store_buffer),
    (vi_cl_invalidate, vi_cl_create),
    (vi_cl_create, vi_cl_create),
    (vi_cl_expire, vi_cl_create),
]

path = path_axiom(Microop, allowed_unary)
fifo = fifo_axiom(Microop, allowed_binary)
sourcing = sourcing_axiom(Microop, allowed_binary)
fifo2 = fifo_axiom(Microop, allowed_binary)
fifo3 = fifo_axiom(Microop, allowed_binary)

axioms = [
    write_is_before_final, # 18.41user (trivial) 2
    reads,
    writes, # 457.14user
    mfence, # 49.48user (trivial) 3
    rmw, # 692.77user
    po__fetch, # 540.29user 4
    decode_stage_is_in_order, # 2406.52user 9
    execute_stage_is_in_order, # 2766.97user 11
    memory_stage_is_in_order, # 1451.80user 7
    writeback_stage_is_in_order, # 959.14user 6
    stb_fifo, # 2104.05user 8
    stb__one_at_a_time, # 634.72user 5
    l1_vi_c_ls,
    swmr, # 2562.95user 10
    l1_vi_cl_no_dups, # 17.42user (trivial) 1
]

structure = {
    write_is_before_final: {fifo},
    reads: {path, fifo, fifo2, fifo3, sourcing},
    writes: {path},
    mfence: {},
    rmw: {sourcing},
    po__fetch: {fifo},
    decode_stage_is_in_order: {fifo},
    execute_stage_is_in_order: {fifo},
    memory_stage_is_in_order: {fifo},
    writeback_stage_is_in_order: {fifo},
    stb_fifo: {fifo},
    stb__one_at_a_time: {fifo},
    l1_vi_c_ls: {path, fifo, sourcing},
    swmr: {fifo},
    l1_vi_cl_no_dups: {fifo},
}

axiom_names = {
    'writeisbeforefinal': write_is_before_final, # 18.41user (trivial) 2
    'reads': reads,
    'writes': writes, # 457.14user
    'mfence': mfence, # 49.48user (trivial) 3
    'rmw': rmw, # 692.77user
    'pofetch': po__fetch, # 540.29user 4
    'decodestageisinorder': decode_stage_is_in_order, # 2406.52user 9
    'executestageisinorder': execute_stage_is_in_order, # 2766.97user 11
    'memorystageisinorder': memory_stage_is_in_order, # 1451.80user 7
    'writebackstageisinorder': writeback_stage_is_in_order, # 959.14user 6
    'stbfifo': stb_fifo, # 2104.05user 8
    'stboneatatime': stb__one_at_a_time, # 634.72user 5
    'l1vicls': l1_vi_c_ls,
    'swmr': swmr, # 2562.95user 10
    'l1viclnodups': l1_vi_cl_no_dups, # 17.42user (trivial) 1
}


co_node = vi_cl_create
suite = 'litmus'

FiveStagePeekaboo = Microarchitecture(suite,
                                      axioms,
                                      Microop,
                                      nodes,
                                      co_node,
                                      execution_dictionary,
                                      structure,
                                      "FiveStagePeekaboo",
                                      allowed_unary,
                                      allowed_binary,
                                      axiom_names)