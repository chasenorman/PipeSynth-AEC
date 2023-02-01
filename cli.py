import argparse
import pyuhb
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

def help():
    print("Enter Available microarchitectures:")
    for arch in microarchitectures:
        print(arch)
def main():
    parser = argparse.ArgumentParser(description = "PipeSynth")
    # defining arguments for parser object
    parser.add_argument("-u", "--uarch", type=str, nargs=1,
                        metavar="uarch", default=None,
                        help="Microachiectures to be synthesized ")

    parser.add_argument("-a", "--axioms", type=str, nargs="*",
                        metavar="axioms", default=None,
                        help="Axioms to be synthesized: Type 'all' to synthesize all single-axiom synthesis")

    parser.add_argument("-t", "--templates", type=str, nargs="*",
                        metavar="templates", default=None,
                        help="Synthesis Templates")

    # parse the arguments from standard input
    args = parser.parse_args()

    if args.uarch is None:
        help()
    elif args.axioms and args.templates and len(args.axioms) == len(args.templates):
        benchmark(args)
    elif len(args.axioms) == 1 and args.axioms[0] == "all":
        benchmark(args)
    else:
        print("Wrong Command Line Input")


def benchmark(args):
    uarch = args.uarch[0]
    axioms = args.axioms
    templates = args.templates
    global  microarchitectures

    microarchitecture = microarchitectures[uarch]

    if axioms[0] == "all":
        print(f"Doing Single Axiom Synthesis for {uarch}")

        for an in microarchitecture.axiom_names:
            # single axiom template
            new_axioms = microarchitecture.axioms.copy()
            axiom = microarchitecture.axiom_names[an]
            new_axioms.remove(axiom)
            new_axioms.extend(list(microarchitecture.structure[axiom]))
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
    else:
        print(f"Doing Mult Axiom Synthesis for {uarch}")

        DEFAULT_FILE = f'out/{microarchitecture.name}'
        new_axioms = microarchitecture.axioms

        #Remove axioms
        for axiom in axioms:
            if axiom in microarchitecture.axiom_names:
                new_axioms.remove(microarchitecture.axiom_names[axiom])
            else:
                print(f'unknown axiom {axiom}')
                print(f"Available axioms: {', '.join(microarchitecture.axiom_names)}")
            DEFAULT_FILE += f'-{axiom}'

        #Add back with templates
        for t in templates:
            if t == "path":
                new_axioms.append(path_axiom(microarchitecture.Microop,
                                             microarchitecture.allowed_unary))
            elif t == "fifo":
                new_axioms.append(fifo_axiom(microarchitecture.Microop,
                                             microarchitecture.allowed_binary))
            elif t == "sourcing":
                new_axioms.append(sourcing_axiom(microarchitecture.Microop,
                                                 microarchitecture.allowed_binary))
            else:
                print(f'unknown template {t}')
                print(f"Available templates: path, fifo, sourcing")
            DEFAULT_FILE += f'-{t}'


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

if __name__ == "__main__":
    main()

