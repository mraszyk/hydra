# HYDRA/VYDRA

HYDRA is a monitor for metric temporal logic (MTL) and metric dynamic logic (MDL).
HYDRA takes as input a MTL or MDL formula and a trace stored in a file
and outputs a sequence of Boolean verdicts denoting the satisfaction (or violation)
of the formula at every position in the trace (for formulas involving
future operators, the trace of verdicts may be incomplete if no verdict
for a time-point can be inferred by the monitor from the given trace).

VYDRA is a formally verified implementation of HYDRA's algorithm.
We used the [Isabelle/HOL](https://isabelle.in.tum.de/) proof assistant to define HYDRA's algorithm,
prove its correctness, and export verified code in OCaml.
The formalization is available as the AFP entry [`VYDRA_MDL`](https://www.isa-afp.org/entries/VYDRA_MDL.html)

This repository is the supplementary material for Martin Raszyk's PhD thesis.

---

# Directory Structure:

- `Dockerfile` - Dockerfile for this supplementary material
- `hydra` - HYDRA's executable
- `vydra` - VYDRA's executable
- `mdl2mdl` - tool converting MDL formulas to MDL^{Aerial} formulas
- `run_exp.sh` - script to run the experiments (see below for more details)
- `run_tests.sh` - script to run the correctness tests (see below for more details)
- `evaluation/` contains tools for running the experiments and correctness tests
- `examples/` contains example formulas and logs
- `src/` contains HYDRA's source code (in C++) and VYDRA's source code (the formally verified core in `verified.ml` and unverified code to parse the formula and trace in OCaml and C)
- `aerial/`, `monpoly/`, and `reelay-codegen/` contain third-party tools for the empirical evaluation

---

# Build

We recommend running the experiments using `docker` and the provided `Dockerfile`.
Please set up at least 8 GiB of main memory for your Docker container.
Note that the first command below will take some time to finish.
```
sudo docker build --no-cache -t hydra .
sudo docker run -it hydra
```
Once you run the second command above you will
obtain a shell with all the tools installed.

---

# Usage

To run HYDRA type:
```
$ ./hydra ${formula} ${log}
```
To run VYDRA type:
```
$ ./vydra ${formula} ${log}
```
where
```
${formula} = path to a text file with a MTL/MDL formula
${log}     = path to a text file with a log
```

MDL Syntax

```
{f} ::=   true
        | false
        | {ID}
        | NOT {f}
        | {f} AND {f}
        | {f} OR  {f}
        | PREV {i} {f}
        | NEXT {i} {f}
        | {f} SINCE {i} {f}
        | {f} UNTIL {i} {f}
        | ◁ {i} {r}
        | ▷ {i} {r}

{r} ::=   {f} ?
        | {f}
        | {r} + {r}
        | {r} {r}
        | {r} *

{i} ::= [ {NUM} , {U} ]
{U} ::= {NUM} | INFINITY
```
where `{NUM}` is a nonnegative integer and `{ID}` is an identifier (atomic proposition).
Non-terminals are enclosed in curly braces.

The semantics of MTL and MDL formulas and MDL regular expressions is defined as follows:
```
i |= true                holds
i |= false               does not hold
i |= {ID}                iff the atomic proposition {ID} is observed at the i-th time-point
i |= {f} AND {g}         iff i |= {f} and i |= {g}
i |= {f} OR {g}          iff i |= {f} or i |= {g}
i |= PREV[a, b] {f}      iff i > 0, \tau_i - \tau_{i - 1} \in [a, b], and i - 1 |= {f}
i |= NEXT[a, b] {f}      iff \tau_{i + 1} - \tau_i \in [a, b] and i + 1 |= {f}
i |= {f} SINCE[a, b] {g} iff \exists j <= i. \tau_{i} - \tau_{j} \in [a, b], j |= {g}, k |= {f}, for all j < k <= i
i |= {f} UNTIL[a, b] {g} iff \exists j >= i. \tau_{j} - \tau_{i} \in [a, b], j |= {g}, k |= {f}, for all i <= k < j
i |= ◁ [a, b] {r}        iff \exists j <= i. \tau_{i} - \tau_{j} \in [a, b] and (j, i + 1) \in R(r)
i |= ▷ [a, b] {r}        iff \exists j >= i. \tau_{j} - \tau_{i} \in [a, b] and (i, j + 1) \in R(r)

R({f} ?)     = { (i, i)     | i |= {f} }
R({f})       = { (i, i + 1) | i |= {f} }
R({r} + {s}) = R({r}) |_| R({s})
R({r} {s})   = R({r})  .  R({s})
R({r}*)      = R({r})*
```

Log Syntax

```
{L} :=   @{NUM} {ID}*
       | @{NUM} {ID}* \n {L}
```

where `{NUM}` is a nonnegative integer and `{ID}` is an identifier (atomic proposition).
Numbers preceeded by `'@'` character are timestamps
that must be (non-strictly) monotonically increasing.

Example of a property expressible in both MTL and MDL:

```
$ cat examples/ex.mtl
p0 OR (p1 UNTIL[2,2] p2)

$ cat examples/ex.mdl
p0 OR (▷ [2,2] p1* p2)

$ cat examples/ex.log
@0 p1 p2
@0 p0 p2
@1 p1
@4 p0 p2
@4 p1 p2
@6 p0 p1 p2
@7 p1

$ ./hydra ./examples/ex.mtl ./examples/ex.log
0:0 false
0:1 true
1:0 false
4:0 true
4:1 true

$ ./vydra ./examples/ex.mtl ./examples/ex.log
0:0 false
0:1 true
1:0 false
4:0 true
4:1 true

$ ./hydra ./examples/ex.mdl ./examples/ex.log
0:0 false
0:1 true
1:0 false
4:0 true
4:1 true

$ ./vydra ./examples/ex.mdl ./examples/ex.log
0:0 false
0:1 true
1:0 false
4:0 true
4:1 true
```

HYDRA and VYDRA also support formulas in metric dynamic logic
as defined in the paper [Almost Event-Rate Independent Monitoring](https://link.springer.com/article/10.1007/s10703-018-00328-3):
```
$ cat examples/ex.mdlaerial
p0 OR (▷ [2,2] (p1? .)* p2?)

$ ./hydra ./examples/ex.mdlaerial ./examples/ex.log -mdlaerial
0:0 false
0:1 true
1:0 false
4:0 true
4:1 true

$ ./vydra ./examples/ex.mdlaerial ./examples/ex.log -mdlaerial
0:0 false
0:1 true
1:0 false
4:0 true
4:1 true
```

---

# Tests

To test HYDRA against VYDRA (formally verified using Isabelle/HOL), run

```
$ ./run_tests.sh
```

In total, 120 tests are executed (they take a few minutes to finish).
The tests are conducted on pseudorandom formulas and a pseudorandom trace.
The parameters are summarized here:

- Formulas: MTL/MDL
- Formula size: 1, 2, 3, 4, 8, 16
- Max. interval bounds: 0, 1, 2, 4, 8
- Trace length: 40'000
- Event rate: 4
- Max. time-stamp difference: 4

Failed tests are reported by storing the corresponding formulas
in files `evaluation/bug_*`.

---

# Evaluation

To reproduce the experiments from the thesis, run

```
$ ./run_exp.sh config_thesis.py
```

After the script `run_exp.sh config_thesis.py` successfully finishes,
the raw data from the experiments are contained in `evaluation/stats/`
and the plots are stored in `evaluation/figs/`.
The timeout per repetition (default: 200s) can be
configured in the section `exp_config` of the configuration file
`config_thesis.py`.

If the time or memory usage does not fit into the predefined
ranges in the plots, you can adjust the ranges by setting
`plot_config_exp[exp_name]["yrange"]["time"]` and
`plot_config_exp[exp_name]["yrange"]["space"]`
(where `exp_name` is, e.g., `exp_size_mtl`)
in the configuration file `config_thesis.py`
and then rerun `python3 proc.py config_thesis.py`
in the directory `evaluation/`.

The individual experiments are described in Section 3.3.
The mapping of the experiment names is summarized here:
- Figure 3.22  -> `exp_scaling_pmtl`, `exp_scaling_mtl`, `exp_scaling_mdl`
- Figure 3.23  -> `exp_mtl_fixed`
- Figure 3.25  -> `exp_size_pmtl`, `exp_size_mtl`, `exp_size_mdl`
- Figure 3.26  -> `exp_mtl_exp`, `exp_mdl_bw_quad`, `exp_mdl_fw_quad`
