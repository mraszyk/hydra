# HYDRA

HYDRA is a monitor for metric temporal logic (MTL) and metric dynamic logic (MDL).
The two versions, called HYDRA(MTL) and HYDRA(MDL), are presented in the papers

Multi-Head Monitoring of Metric Temporal Logic,  
Multi-Head Monitoring of Metric Dynamic Logic,

accepted at [ATVA 2019](https://doi.org/10.1007/978-3-030-31784-3_9)
and [ATVA 2020](https://doi.org/10.1007/978-3-030-59152-6_13), respectively.

This artifact is the supplementary material for these papers.

HYDRA takes as input an MTL or MDL formula and a trace stored in a file
and outputs a sequence of verdicts denoting the satisfaction (or violation)
of the formula at every position in the trace (for formulas involving
future operators, the trace of verdicts may be incomplete if no verdict
for a time-point can be inferred by the monitor from the given trace).

---

# Directory Structure:

- `atva19.pdf` - paper on HYDRA(MTL)
- `atva20.pdf` - paper on HYDRA(MDL)
- `Dockerfile` - Dockerfile for this supplementary material
- `hydra` - HYDRA's executable
- `vydra` - VYDRA's executable
- `run_exp.sh` - script to run the experiments (see below for more details)
- `run_tests.sh` - script to run the correctness tests (see below for more details)
- `evaluation/` contains tools for running the experiments and correctness tests
- `examples/` contains example formulas and logs
- `html/` contains the generated HTML page of the formalization in Isabelle/HOL
- `src/` contains HYDRA's source code (in C++) and VYDRA's source code (the formally verified core in `verified.ml` and unverified code to parse the formula and trace in OCaml and C)
- `thys/` contains the formalization of HYDRA(MDL) in Isabelle
- `aerial/`, `monpoly/`, `pcre2/`, `reelay-codegen/` contain third-party tools for the empirical evaluation

---

# Formalization in Isabelle/HOL

The formal development can be browsed as a generated HTML page (open `html/index.html`).
An alternative way to study the theory files is to open them in Isabelle/jEdit.

The raw Isabelle sources are included in the directory `thys`.

The formalization can been processed with Isabelle2021, which can be downloaded from

https://isabelle.in.tum.de/

and installed following the standard instructions from

https://isabelle.in.tum.de/installation.html

It also requires the Archive of Formal Proofs, which can be downloaded from

https://www.isa-afp.org/download.html

and installed following the standard instructions from

https://www.isa-afp.org/using.html

To build the theories, export the verified OCaml code, and regenerate the HTML page, run
```
isabelle build -o browser_info -c -e -v -D thys
```
in the root directory of this artifact.
Instructions where to find the verified OCaml code and the generated html sources are printed in the console.

---

# Build

We recommend running the experiments using `docker` and the provided `Dockerfile`.
Please set up at least 8 GiB of main memory for your Docker container.
Note that the first command below will take some time to finish (roughly 15 minutes).
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
${formula} = path to a text file with an MTL/MDL formula
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
        | .
        | {r} + {r}
        | {r} {r}
        | {r} *

{i}  ::= [ {NUM} , {UP} ]
{UP} ::= {NUM} | INFINITY
```

where `{NUM}` is a nonnegative integer and `{ID}` is an identifier.
Non-terminals are enclosed in curly braces.

The semantics of temporal match operators is defined as follows:
```
i |= ◁ [a, b] {r} iff \exists j <= i. \tau_i - \tau_j \in [a, b] /\ (j, i) \in R(r)
i |= ▷ [a, b] {r} iff \exists j >= i. \tau_j - \tau_i \in [a, b] /\ (i, j) \in R(r)
```

Log Syntax

```
{L} :=   @{NUM} {ID}*
       | @{NUM} {ID}* \n {L}
```

where `{NUM}` is a nonnegative integer and `{ID}` is an identifier.
Numbers preceeded by `'@'` character are timestamps
that must be (non-strictly) monotonically increasing.

Example of a property expressible in both MTL and MDL:

```
$ cat examples/ex.mtl
p0 OR (p1 UNTIL[2,2] p2)

$ cat examples/ex.mdl
p0 OR (▷ [2,2] (p1? .)* p2?)

$ cat examples/ex.log
@0 p1 p2
@0 p0 p2
@1 p1
@4 p0 p2
@4 p1 p2
@6 p0 p1 p2
@7 p1

$ ./hydra ./examples/ex.mtl ./examples/ex.log
Monitoring (p0 OR (p1 UNTIL[2,2] p2))
0:0 false
0:1 true
1:0 false
4:0 true
4:1 true
Bye.

$ ./hydra ./examples/ex.mdl ./examples/ex.log
Monitoring (p0 OR (▷ [2,2] ((((p1?) .)*) (p2?))))
0:0 false
0:1 true
1:0 false
4:0 true
4:1 true
Bye.

$ ./vydra ./examples/ex.mdl ./examples/ex.log
0:0 false
0:1 true
1:0 false
4:0 true
4:1 true
```

---

# Tests

To test HYDRA against VYDRA (the formally verified algorithm), run

```
$ ./run_tests.sh
```

In total, 120 tests are executed (they take a few minutes to finish).
The tests are conducted on pseudorandom formulas and a pseudorandom trace.
The parameters are summarized here:

- Number of subformulas: 1, 2, 3, 4, 8, 16
- Formula's maximum interval bounds: 0, 1, 2, 4, 8
- Event rate: 4
- Trace length: 40'000

---

# Evaluation

To reproduce the experiments from the papers, run

```
$ ./run_exp.sh config_atva19.py
$ ./run_exp.sh config_atva20.py
```

We remark that the sources of R2U2 were sent to us
in a private communication and are thus not included
in this artifact.

Moreover, the space complexity of HYDRA(MTL) has been improved
to be interval-oblivous in this artifact.

After the script `run_exp.sh config_*.py` successfully finishes,
the raw data from the experiments are contained in `evaluation/stats/`,
and the plots are stored in `evaluation/figs/`.
The number of repetitions of the same experiment (default: 2) and
a timeout per repetition (default: 10s and 90s, respectively) can be set in
the section `exp_config` of the configuration file `config_*.py`

If the time or memory usage does not fit into the predefined
ranges in the plots, you can adjust the ranges by setting
`plot_config_exp[exp_name]["yrange"]["time"]` and
`plot_config_types[exp_name]["yrange"]["space"]`
(where exp_name is, e.g., exp_size)
in the configuration file `config_*.py`
and then rerun `python3 proc.py config_*.py`
in the directory `evaluation/`.

The individual experiments for HYDRA(MTL) are described
in Section 6 of the paper presented at [ATVA 2019](https://doi.org/10.1007/978-3-030-31784-3_9).
The mapping of the experiment names is summarized here:
- Experiment 1 -> `exp_trace`
- Experiment 2 -> `exp_size`
- Experiment 3 -> `exp_scaling`
- Figure 8     -> `exp_mtl_exp`

The individual experiments for HYDRA(MDL) are described
in Section 5 of the paper presented at [ATVA 2020](https://doi.org/10.1007/978-3-030-59152-6_13).
The mapping of the experiment names is summarized here:
- Experiment IO -> `exp_scaling`
- Experiment SZ -> `exp_size`
- Experiment WC -> `exp_mtl_exp`
- Experiment RL -> `exp_mtl_fixed`
- Experiment RE -> `exp_pcre`
