import sys
import uarchs.Vscale
import uarchs.FiveStage
import uarchs.FiveStageOoOSLR
import uarchs.FiveStagePeekaboo
from synth import *

microarchitectures = {'vscale': uarchs.Vscale.Vscale,
                      'fivestage': uarchs.FiveStage.FiveStage,
                      'fivestageoooslr': uarchs.FiveStageOoOSLR.FiveStageOoOSLR,
                      'fivestagepeekaboo': uarchs.FiveStagePeekaboo.FiveStagePeekaboo}

if __name__ == "__main__":
    if len(sys.argv) == 1:
        print(f"Available microarchitectures: {', '.join(microarchitectures)}")
        exit()

    architecture_name = sys.argv[1].lower().replace('.py', '')
    if architecture_name not in microarchitectures:
        print(f"No such microarchitecture {architecture_name}")
        print(f"Available microarchitectures: {', '.join(microarchitectures)}")
        exit()

    microarchitecture = microarchitectures[sys.argv[1].lower().replace('.py', '')]

    if len(sys.argv) == 3 and sys.argv[2].lower() == 'all':
        for an in microarchitecture.axiom_names:
            new_axioms = microarchitecture.axioms.copy()
            axiom = microarchitecture.axiom_names[an]
            new_axioms.remove(axiom)
            new_axioms += list(microarchitecture.structure[axiom])
            path = "out"
            if not os.path.exists(path):
                os.mkdir(path)
            DEFAULT_FILE = f'out/{microarchitecture.name}-{an}.sy'
            synth = pycvc5.Solver()
            FILE_POINTERS[synth] = open(DEFAULT_FILE, 'w')
            SYGUS_SOLVERS.add(synth)
            set_logic(synth)

            assert_formula(synth, test_suite(microarchitecture.suite,
                                         new_axioms,
                                         microarchitecture.Microop,
                                         microarchitecture.nodes,
                                         microarchitecture.co_node,
                                         microarchitecture.execution_dictionary))
            check(synth)
        exit()


    DEFAULT_FILE = f'out/{microarchitecture.name}'

    has_template = False
    new_axioms = microarchitecture.axioms
    for arg in sys.argv[2:]:
        sanitized = ''.join(c for c in arg if c.isalnum()).lower()
        if sanitized in microarchitecture.axiom_names:
            new_axioms.remove(microarchitecture.axiom_names[sanitized])
        elif sanitized == 'path':
            has_template = True
            new_axioms.append(path_axiom(microarchitecture.Microop, microarchitecture.allowed_unary))
        elif sanitized == 'fifo':
            has_template = True
            new_axioms.append(fifo_axiom(microarchitecture.Microop, microarchitecture.allowed_binary))
        elif sanitized == 'sourcing':
            has_template = True
            new_axioms.append(sourcing_axiom(microarchitecture.Microop, microarchitecture.allowed_binary))
        else:
            print(f'unknown axiom/template {arg}')
            print(f"Available axioms: {', '.join(microarchitecture.axiom_names)}")
            print(f"Available templates: path, fifo, sourcing")
            exit()
        DEFAULT_FILE += f'-{sanitized}'

    if not has_template:
        new_axioms.append(empty(microarchitecture.Microop))

    DEFAULT_FILE += '.sy'

    s = pycvc5.Solver()
    FILE_POINTERS[s] = open(DEFAULT_FILE, 'w')

    SYGUS_SOLVERS.add(s)
    set_logic(s)
    assert_formula(s, test_suite(microarchitecture.suite,
                                 new_axioms,
                                 microarchitecture.Microop,
                                 microarchitecture.nodes,
                                 microarchitecture.co_node,
                                 microarchitecture.execution_dictionary))
    check(s)
