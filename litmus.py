# Read .test files and convert to SMT-LIB, create riscV binaries and parse verilator output

from uspec import *
import os
import json
import subprocess


uop_dict = {'Read': UOPType.Read, 'Write': UOPType.Write, 'Fence': UOPType.Fence}
rmw_dict = {'normal': False, 'RMW': True}


writes = [["04500023", "04600023", "04700023", "05c00023", "05d00023", "05e00023", "05f00023"],
 ["045000a3", "046000a3", "047000a3", "05c000a3", "05d000a3", "05e000a3", "05f000a3"],
 ["04500123", "04600123", "04700123", "05c00123", "05d00123", "05e00123", "05f00123"],
 ["045001a3", "046001a3", "047001a3", "05c001a3", "05d001a3", "05e001a3", "05f001a3"],
 ["04500223", "04600223", "04700223", "05c00223", "05d00223", "05e00223", "05f00223"],
 ["045002a3", "046002a3", "047002a3", "05c002a3", "05d002a3", "05e002a3", "05f002a3"]]


def litmus_test(filename, axioms, microop_t, nodes, co_node, time_matrix=None, risc_v=False, get_microops=False, synth_axioms=None):
    if synth_axioms is None:
        synth_axioms = axioms
    microops = []
    setup = True
    constraint = True
    alternative_seen = False
    current_core = 0
    num_on_core = 0
    result = ["00000013"]
    with open(filename) as fp:
        assert fp.readline().strip() == 'Alternative'
        for line in fp.readlines():
            if line.strip() == 'Alternative':
                alternative_seen = True
            elif line.strip() == 'Forbidden':
                constraint &= forall(axioms, lambda a: a(microops))
                setup &= forall(microops, lambda m: forall(nodes, lambda n:
                            (n(m).time < len(nodes) * len(microops)) & (n(m).time >= 0)
                         ))
                if get_microops:
                    return setup & constraint, microops
                return setup & constraint
            elif line.strip() == 'Permitted':
                constraint &= forall(synth_axioms, lambda a: a(microops))
                setup &= forall(microops, lambda m: forall(nodes, lambda n:
                            (n(m).time < len(nodes) * len(microops)) & (n(m).time >= 0)
                         ))
                if time_matrix:
                    for (m, times) in zip(microops, time_matrix):
                        for (node, value) in zip(nodes, times):
                            setup &= (node(m).time == value[0]) & (node(m).node_exists == value[1])
                    return setup & (~constraint)
                else:
                    if risc_v:
                        result += ["00000013"] * (4 - num_on_core) + ["feedfeed"]
                        result += ["00000000"] * (8 * 4 - len(result))
                        with open(f'riscv/{os.path.basename(os.path.splitext(filename)[0])}.hex', 'w') as fp2:
                            for i in range(0, len(result), 4):
                                fp2.write(result[i + 3] + result[i + 2] + result[i + 1] + result[i] + '\n')
                    return setup & constraint, microops
            elif alternative_seen:
                continue
            elif line.startswith('Relationship'):
                tokens = line.split()
                assert tokens[4] == '->'
                if tokens[1] == 'co':
                    constraint &= add_edge(co_node(microops[int(tokens[2])]), co_node(microops[int(tokens[5])]))
            else:
                tokens = line.replace('(','').replace(')','').split()
                assert len(tokens) == 14
                assert tokens[6] == 'VA'
                assert tokens[9] == 'PA'
                assert tokens[12] == 'Data'
                m = microop_t()
                core = int(tokens[1])
                setup &= (m.id == int(tokens[0])) & \
                        (m.core == core) & \
                        (m.type == uop_dict[tokens[4]]) & \
                        (m.rmw_access == rmw_dict[tokens[5]]) & \
                        (m.virtual_address == int(tokens[7])) & \
                        (m.physical_address == int(tokens[10])) & \
                        (m.data == int(tokens[13])) & \
                        (m.known_data == CVCBool(value=True)) & \
                        (m.data_from_final_state == CVCBool(value=False))
                microops.append(m)
                if core != current_core:
                    current_core = core
                    result += ["00000013"]*(4 - num_on_core) + ["feedfeed"]
                    num_on_core = 0
                if tokens[4] == 'Read':
                    result += [f"04{int(tokens[10])}00003"]
                elif tokens[4] == 'Write':
                    result += [writes[int(tokens[10])][int(tokens[13])]]
                num_on_core += 1



def generate_timestamps(filename, axioms, microop_t, nodes, co_node):
    constraint, microops = litmus_test(filename, axioms, microop_t, nodes, co_node)
    solver = pycvc5.Solver()
    solver.setOption('produce-models', 'true')
    assert_formula(solver, constraint)
    print(check(solver))
    result = []
    for m in microops:
        t = []
        for n in nodes:
            t.append((int(str(solver.getValue(to_cvc(n(m).time, solver)))),
                      str(solver.getValue(to_cvc(n(m).node_exists, solver))) == "true"))
        result.append(t)
    return result


def get_simulator_timestamps(filename):
    cmd = ['./run.sh', f'../../pyuhb/riscv/{filename}.hex']
    output = subprocess.Popen(cmd, stdout=subprocess.PIPE, cwd='../processors/multi_vscale').communicate()[0]
    timestamps = dict()
    has_effect = list()
    for line in output.splitlines():
        if line.startswith(b'{'):
            j = json.loads(line)
            timestamps[(j['pc'], j['stage'])] = j['t']
            if j['stage'] == 'RESP':
                has_effect.append(j['pc'])
                print('RESP', j['pc'], j['val'])
            if j['stage'] == 'Update':
                has_effect.append(j['pc'])
                print('Update', j['pc'], j['value'])
    has_effect.sort(key=lambda i: int(i, 16))
    print(f"'{filename}': {[[timestamps[(i, 'IF')], timestamps[(i, 'DX')], timestamps[(i, 'WB')]] for i in has_effect]},")


def test_suite(folder, axioms, microop_t, nodes, co_node, execution_dictionary, use_simulator=False, synth_axioms=None):
    poisoned = False
    result = False
    for f in os.listdir(folder):
        if f.startswith('.'):
            continue
        joined = os.path.join(folder, f)
        test = litmus_test(joined, axioms, microop_t, nodes, co_node, execution_dictionary.get(f, None), risc_v=use_simulator, synth_axioms=synth_axioms)
        if isinstance(test, tuple):
            poisoned = True
            if use_simulator:
                get_simulator_timestamps(os.path.splitext(f)[0])
            else:
                constraint, microops = test
                solver = pycvc5.Solver()
                solver.setOption('produce-models', 'true')
                assert_formula(solver, constraint)
                check(solver, quiet=True)
                result = []
                for m in microops:
                    t = []
                    for n in nodes:
                        t.append((int(str(solver.getValue(to_cvc(n(m).time, solver)))), str(solver.getValue(to_cvc(n(m).node_exists, solver))) == "true"))
                    result.append(t)
                print(f"'{f}': {result},")
        if not poisoned:
            result |= test
    if poisoned:
        print('test suite missing exeuction traces, suitable assignments generated.')
    return result