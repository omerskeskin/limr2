
# Source Code

**Title of the Submitted Paper:** Formalising Subject Reduction and Progress for Multiparty Session Processes (Replication)

---

## Software Requirements

1. **opam** – Package manager for OCaml  
   Install by following the instructions [here](https://opam.ocaml.org/doc/1.1/Quick_Install.html).
2. **coqc 20.0** – Coq compiler  
    - Run in the terminal: `opam pin add coq 8.20.0`
3. **coqide** – Integrated development environment for Coq <br>
    - Run in the terminal: `opam install coqide`
4. **ssreflect** – Coq library for formalized mathematics <br>
    - Run in the terminal:
    ```bash
    opam repo add coq-released https://coq.inria.fr/opam/released
    opam install coq-mathcomp-ssreflect
5. **paco** – Coq library for implementing parametrized coinduction <br>
    - Run in the terminal:
    ```bash
    opam repo add coq-released https://coq.inria.fr/opam/released 
    opam install coq-paco

---

## Shell Instructions

1. Fetch the code from [here](https://anonymous.4open.science/r/smpst-sr-smer-4563/README.md).
2. Open a terminal.
3. Navigate to the directory containing the code using the `cd` command.
4. Run: `eval $(opam env)` to update the shell environment for Coq.
5. Run: `coq_makefile -f _CoqProject -o Makefile` to generate the Makefile.
6. Run: `make` to compile the library (this may take up to 2 minutes). A successful compilation indicates that all results hold.

---

## Exploring Proofs in CoqIDE
- After the compilation is finished, you can open and explore the proof files using CoqIDE. 
- For instance, you can run (inside the directory containing the code) `coqide lemma/main.v` to open the `main.v` file and step through the proofs interactively.
- Refer to the [documentation](https://coq.inria.fr/doc/V8.18.0/refman/practical-tools/coqide.html) for instructions on managing code using CoqIDE.

---

### Table (File - Description):

---

| | File    | Description |
| -------- | -------- | ------- |
| 1 | `src/sim.v` | Simple lemmas deriving from the library |
| 2 | `src/header.v` | Defines constructors needed to define specific session type constructors and lemmas relating to them |
| 3 | `src/expr.v` | Definition of session expressions and sorts | 
| 4 | `src/process.v` | Definition of session processes and some helper lemmas |
| 5 | `src/local.v` | Definition of Local Tree / Types and subtyping, along with properties relating to them | 
| 6 | `src/global.v` | Definition of Global Tree / Types and properties relating to them |
| 7 | `src/gttreeh.v` | Definition of Global Type Tree Context Holes and related properties | 
| 8 | `src/part.v` | Definition of participants and related properties |
| 9 | `src/balanced.v` | Definition of balanced global trees and related properties | 
| 10 | `src/typecheck.v` | Definition of typing rules for expressions and processes, with related properties |
| 11 | `src/step.v` | Definition of Global Trees taking a step |
| 12 | `src/merge.v` | Definition of the merging operator and related properties |
| 13 | `src/projection.v` | Definition of projection |
| 14 | `src/session.v` | Definitions related to sessions |
| 15 | `lemma/inversion.v` | Inversion Lemma for processes |
| 16 | `lemma/inversion_expr.v` | Inversion Lemma for expressions |
| 17 | `lemma/substitution_helper.v` | Helper functions for substitution lemma |
| 18 | `lemma/substitution.v` | Substitution Lemma for process and expression variables |
| 19 | `lemma/decidable_helper.v` | Helper functions relating to participant decidability |
| 20 | `lemma/decidable.v` | Lemmas regarding participant decidability |
| 21 | `lemma/expr.v` | Lemmas regarding expression evaluation |
| 22 | `lemma/part.v` | Lemmas regarding participants on subtrees |
| 23 | `lemma/step.v` | Lemmas regarding well-formedness of global trees after taking a step |
| 24 | `lemma/projection_helper.v` | Helper functions for projection related lemmas |
| 25 | `lemma/projection.v` | Lemmas regarding projections after global trees take a step | 
| 26 | `lemma/main_helper.v` | Helper functions for main theorems |
| 27 | `lemma/main.v` | Main Theorems |

---