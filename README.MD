
## Source Code

**Title of the Submitted Paper:** Formally Verified Liveness with Multiparty Session Types in Rocq

---

## Installation Instructions

1. **opam** – Package manager for OCaml  
   Install by following the instructions [here](https://opam.ocaml.org/doc/1.1/Quick_Install.html).
2. **coqc 20.1** – Coq compiler  
    - Run in the terminal: `opam pin add coq 8.20.1`
3. **opam dependencies** – The project depends on paco, mmaps and ssreflect (mathcomp 2.5.0)
    - Run in the terminal:
    ```bash
    opam repo add coq-released https://coq.inria.fr/opam/released 
    opam install coq-paco coq-mmaps coq-mathcomp-ssreflect

---

## Shell Instructions

1. Download the code.
2. Open a terminal.
3. Navigate to the directory containing the code using the `cd` command.
4. Run: `eval $(opam env)` to update the shell environment for Coq.
5. Run: `coq_makefile -f _CoqProject -o Makefile` to generate the Makefile.
6. Run: `make` to compile the library (this may take around 10 minutes, see benchmark.txt). A successful compilation indicates that all results hold.

---

## Table (File - Description): ##

The folder STBase contains files from the recent formalisation of session types that we base this work on (https://github.com/Apiros3/smpst-sr-smer/tree/main/src).
cpdtlib contains some automation tactics from Adam Chlipala's Certified Programming with Dependent Types book (http://adam.chlipala.net/cpdt/).
The contents of the files in the STLive folder are listed below.
---

| | File    | Description |
| -------- | -------- | ------- |
| 1 | `src/assoc.v` | Definition of association |
| 2 | `src/lcontext.v` | Definition of local type tree contexts |
| 3 | `src/path_props.v` | Definition of safety, fairness and liveness properties  | 
| 4 | `src/session.v` | Definition of multiparty sessions |
| 5 | `src/wfltt.v` | Definition of well-formed local type trees | 
| 6 | `lemma/completeness.v` | Proof of completeness of association |
| 7 | `lemma/ltth.v` | Some lemmas on the grafting of local types (NB this is mostly from an earlier flawed proof attempt at liveness, most of the lemmas here are not actually used in the final proof) | 
| 8 | `lemma/liveness_helpers.v` | Some helpers for the proof of liveness by association | 
| 9 | `lemma/multigrafting.v` | Some lemmas on the comparison of graftings of different participants |
| 10 | `lemma/path_assoc.v` | Some lemmas about the extension of association on to paths | 
| 11 | `lemma/safety.v` | Proof of safety by association |
| 12 | `lemma/soundness.v` | Proof of soundness by association |
| 13 | `lemma/subj_red_helpers.v` | Some helper lemmas for the proofs on properties of sessions (NB this file is based on the one from the ) |
| 14 | `lemma/subj_red_prog_fid.v` | Proofs of subject reduction, deadlock-freedom and session fidelity for typed sessions|
| 15 | `lemma/fairness_feasible.v` | Proof of the existence of a fair session reduction path as used in the proof of liveness of typed sessions |
| 16 | `lemma/live_proc.v` | Proof that typed sessions are live |
| 17 | `examples/ex_sess_red.v` | An example illustrating session reductions |
| 18 | `examples/ex_type_semantics.v` | An example illustrating semantics of local type contexts and their properties |
| 19 | `examples/ex_typing` | An extension of an example from earlier work where we type and show the liveness of a simple session |
---