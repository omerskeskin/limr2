From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Coq.Program.Equality Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
From SST Require Import src.header src.sim src.expr src.process src.local 
src.global src.balanced src.typecheck src.part src.gttreeh src.path_props src.step src.merge src.projection src.session src.lcontext.  
From SST Require Import lemma.inversion lemma.path_assoc lemma.inversion_expr lemma.completeness lemma.substitution_helper lemma.substitution lemma.decidable_helper lemma.decidable lemma.expr lemma.part lemma.step 
lemma.projection_helper lemma.subj_red_prog_fid lemma.projection lemma.subj_red_helpers lemma.soundness lemma.liveness_helpers.

Definition proc_path_valid_criteria := (fun x1 (l:label)  x2  =>
  match (x1,x2) with 
    | (g1,g2) => betaP g1 g2 
  end).

Definition proc_valid_pathC := valid_path_GC proc_path_valid_criteria.

Definition betaRtc := clos_refl_trans session betaP.

Print path_assoc.

Search "local" "path".

CoInductive typ_path  (R: coseq (session * option label) -> coseq (tctx * option label) -> Prop) :  coseq (session * option label) -> coseq (tctx * option label) -> Prop :=
    | typ_nil : typ_path R conil conil
    | typ_cocons : forall M gamma ms gs l, typ_sess  M gamma -> typ_path R ms gs ->
        typ_path R (cocons (M,l) ms) (cocons (gamma,l) gs).

Definition live_sess Mp := forall M, betaRtc Mp M -> (forall p q ell e P' M', unfoldP M ( (p <-- p_send q ell e P') ||| M') -> exists M'',
betaRtc M ((p <-- P')|||M''))
/\
(forall p q llp M', unfoldP M ( (p <-- p_recv q llp) ||| M') -> exists M'' P' k,
onth k llp = Some P' /\
betaRtc M ((p <-- P')|||M'')).


