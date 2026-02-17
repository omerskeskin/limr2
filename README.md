
# Source Code

**Title of the Submitted Paper:** Formally Verified Liveness with Multiparty Session Types in Rocq

---

## Installation Instructions

---

### Table (File - Description):
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
| 7 | `lemma/liveness_helpers.v` | Some helpers for the proof of liveness by association | 
| 8 | `lemma/multigrafting.v` | Some lemmas on the comparison of graftings of different participants |
| 9 | `lemma/path_assoc.v` | Some lemmas about the extension of association on to paths | 
| 10 | `lemma/safety.v` | Proof of safety by association |
| 11 | `lemma/soundness.v` | Proof of soundness by association |
| 12 | `lemma/subj_red_helpers.v` | Some helper lemmas for the proofs on properties of sessions (NB this file is based on the one from the ) |
| 13 | `lemma/subj_red_prog_fid.v` | Proofs of subject reduction, deadlock-freedom and session fidelity for typed sessions|
| 14 | `lemma/fairness_feasible.v` | Proof of the existence of a fair session reduction path as used in the proof of liveness of typed sessions |
| 14 | `lemma/live_proc.v` | Proof that typed sessions are live |
---