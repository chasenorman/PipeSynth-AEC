# PipeSynth

PipeSynth is a methology and automated tool for synthesizing microarchitectural ordering axioms
from small programs (litmus tests) and execution traces.

### Citing PipeSynth

If you use our tool in your work, we would appreciate it if you cite our paper(s):

Chase Norman, Adwait Godbole, and Yatin A. Manerkar.
"PipeSynth: Automated Synthesis of Microarchitectural Axioms for Memory Consistency", 
28th International Conference on Architectural Support for Programming Languages and Operating Systems (ASPLOS), March 2023.

### Contacting the authors

If you have any comments, questions, or feedback, please contact Chase Norman
at c_@berkeley.edu or visit our GitHub page, https://github.com/chasenorman/PipeSynth-AEC.

### Status

At this point, PipeSynth is a research tool rather than an industry-strength
synthesis toolchain.  We do appreciate any suggestions or feedback either
in approach or in implementation.  If you are interested in any particular
feature, missing item, or implementation detail, please contact the authors and
we will try to help out as best we can.

## Building and Using PipeSynth

### Prerequisites

PipeSynth is written in Python and uses the CVC5 SMT solver to generate the first-order
microarchitectural ordering axioms. PipeSynth requires Python 3.8 (or later), and CVC5 (0.0.4 for python api and 1.0.2 for SyGuS solving)
The authors have compiled and executed PipeSynth successfully on MacOS.

- Python
  - tested with Python 3.8.10
- CVC5
  - tested with CVC5 0.0.4 for Python API library
  - tested with CVC5 1.0.2 for solving SyGuS-IF files generated from PipeSynth
(all of the above tested on a macOS Ventura from Apple Silcon)

### Python Build Dependencies
PipeSynth uses a number of tools and libraries. 
- [Cpython](https://cython.org)
- [scikit-build](https://pypi.org/project/scikit-build/)
- [pytest](https://docs.pytest.org/en/6.2.x/)

#### Install CVC5 0.0.4 Python Library 
- [Download cvc5-0.0.4 Source Code](https://github.com/cvc5/cvc5/releases?page=2)
    ```shell
    # change the directory to the source code folder
    # build cvc5 0.0.4
    ./configure.sh --python-bindings --auto-download 
    cd build
    # use -jN for parallel build with N threads
    make 
    # install cvc5 0.0.4
    sudo make install
    sudo cp -r ./build/lib/* $( python -c 'import sysconfig; print(sysconfig.get_paths()["purelib"])') 

    ```
#### Install CVC5 1.0.2 Solver Binary Distribution
- [Just download cvc5-1.0.2 distributed binary](https://github.com/cvc5/cvc5/releases/)
  - Download different OS version of CVC5 and rename it to cvc5
  - Put the CVC5 binary in the project folder
## Usage


Basic Usage:
```shell
# For uarch vscale, we generate SyGuS files by replacing po_fetch axiom with fifo templates
python3 main.py vscale po_fetch fifo
# Run CVC5 1.0.2 to solve generated SyGuS files
./benchmark
```

The SyGuS files will appear in the out/ directory. The benchmark script 
will run all SyGuS files in the directory and write to a file 
`out/results.txt` with synthesis results and times. 

## Sample Usage

1. `python3 main.py fivestage all`
2. `python3 main.py vscale writes3 writes reads totalorderondx fifo`
3. `python3 main.py fivestageoooslr writes path fifo`

## Design Approach

PipeSynth is an automated formal methodology and tool for the pre-RTL formal synthesis of microarchitectural ordering axioms in the domain 
 specific µspec language. Given a partial µspec ordering specification, litmus tests, and observable execution traces,
 PipeSynth can automatically synthesise additional µspec ordering axioms that are necessary to guarantee correctness
for the provided tests and traces. PipeSynth thus helps architects and hardware engineers automatically generate formal
ordering specifications for their microarchitectures even if they do not have prior formal methods expertise. 
In doing so, it will enable the increased use of formal verification for emerging microarchitectures. 
This will help catch bugs faster and substantially improve the correctness of the processors of tomorrow.

### FAQ


For building CVC5:



Q: When run `./configure.sh --python-bindings --auto-download`, it shows `-- Could NOT find PythonLibs (missing: PYTHON_LIBRARIES PYTHON_INCLUDE_DIRS) `
error message

A: Add `-DPYTHON_INCLUDE_DIR=$(python -c "import sysconfig; print(sysconfig.get_path('include'))")`
and `-DPYTHON_LIBRARY=$(python -c "import sysconfig; print(sysconfig.get_config_var('LIBDIR'))")` in the configure.sh .
