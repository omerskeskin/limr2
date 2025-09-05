From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Coq.Program.Equality Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
From SST Require Import src.header src.sim src.expr src.process src.local 
src.global src.balanced src.typecheck src.part src.gttreeh src.path_props src.step src.merge src.projection src.session src.lcontext.  
From SST Require Import lemma.inversion lemma.inversion_expr lemma.completeness lemma.substitution_helper lemma.substitution lemma.decidable_helper lemma.decidable lemma.expr lemma.part lemma.step 
lemma.projection_helper lemma.subj_red_prog lemma.projection lemma.main_helper lemma.soundness lemma.liveness_helpers. 

Inductive betaRtc : session -> session -> Prop:=
    | betaRt_unf : forall a b, unfoldP a b -> betaRtc a b
    | betaRt_beta : forall a b, betaP a b -> betaRtc a b
    | betaRtrans : forall a b c, betaRtc a b -> betaRtc b c -> betaRtc a c.

Definition all_guarded P := forall n, exists m, guardP n m P.

Lemma guard_ite_inv : forall e P Q, all_guarded (p_ite e P Q) -> all_guarded P /\ all_guarded Q. 
Proof.
    intros;split;unfold all_guarded in *;
        intros; specialize (H n); destr_hyps; inversion H;subst;
        try solve [
        exists 0; constructor |  exists m;easy].
Qed.

Lemma guarded_after_unfold : forall P P', all_guarded P ->  betaPr P P' -> all_guarded P'.
Proof.
    intros. unfold all_guarded in *.
    Search guardP.
    inversion H0;subst.
    intros. specialize (H n). destr_hyps. inversion H;subst. exists 0. constructor.
    Search substitutionP.
    eapply substitution_helper.inj_substP in H1;try exact H3;subst;exists m;easy.
Qed.

Lemma guarded_after_multi_unfold : forall P P', all_guarded P ->  multi betaPr P P' -> all_guarded P'.
Proof.
    intros.
    induction H0;try easy.
    eapply IHmulti. eapply guarded_after_unfold with (P:=x);easy.
Qed.

(*session fidelity
*)

(*show that a fair session path exists from M
this path is associated* with a fair path gamma
gamma eventually has a p,q transition by liveness
at that point, the corresponding M also transitions by weak session fidelity
*)
Definition live_sess (Mp:session) := forall M p q ell e P' Mr, betaRtc Mp M -> 
    ((unfoldP M (p <-- p_send q ell e P' ||| Mr)) -> exists M', betaRtc M M' /\
    exists Mr', unfoldP M' ((p <-- P') ||| Mr')).
