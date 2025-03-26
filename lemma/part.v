From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
From SST Require Import src.header src.sim src.expr src.process src.local src.global src.balanced src.typecheck src.part src.gttreeh.
From SST Require Import lemma.inversion lemma.inversion_expr lemma.substitution_helper lemma.substitution lemma.decidable_helper lemma.decidable lemma.expr.

Lemma part_cont_false_all_s : forall ys2 s s' p,
      p <> s -> p <> s' ->
      wfgCw (gtt_send s s' ys2) ->
      (isgPartsC p (gtt_send s s' ys2) -> False) ->
      List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ (isgPartsC p g -> False))) ys2.
Proof.
  intros.
  apply Forall_forall; intros.
  destruct x.
  - destruct p0. right. exists s0. exists g. split. easy.
    intros. apply H2.
    specialize(in_some_implies_onth (s0, g) ys2 H3); intros. destruct H5 as (n,H5).
    clear H3 H2.
    unfold wfgCw in H1. destruct H1 as (Gl,(Ha,(Hb,Hc))).
    specialize(guard_breakG_s2 (gtt_send s s' ys2) Gl Hc Hb Ha); intros.
    clear Ha Hb Hc. clear Gl.
    destruct H1 as (Gl,(Ha,(Hb,(Hc,Hd)))).
    destruct Ha. subst. pinversion Hd; try easy. apply gttT_mon.
    destruct H1 as (p1,(q1,(lis,He))). subst. pinversion Hd; try easy. subst.
    unfold isgPartsC in H4.
    destruct H4 as (G1,(He,(Hf,Hg))).
    unfold isgPartsC.
    exists (g_send s s' (overwrite_lis n (Some (s0, G1)) lis)).
    clear Hc Hd.
    specialize(guard_cont Hb); intros. clear Hb.
    revert H2 H1 H5 Hg Hf He H0 H. revert lis G1 g s0 s s' p ys2.
    induction n; intros; try easy.
    - destruct ys2; try easy. destruct lis; try easy.
      inversion H2. subst. clear H2. inversion H1. subst. clear H1.
      simpl in H5. subst. destruct H7; try easy. destruct H1 as (s1,(g1,(g2,(Hta,(Htb,Htc))))).
      inversion Htb. subst. destruct H4; try easy.
      destruct H1 as (s2,(g3,(Htd,Hte))). inversion Htd. subst.
      split. pfold. constructor; try easy. constructor; try easy.
      right. exists s2. exists G1. exists g2. split. easy. split. easy. left. easy.
      split. apply guard_cont_b. constructor; try easy. 
      right. exists s2. exists G1. easy.
      apply pa_sendr with (n := 0) (s := s2) (g := G1); try easy.
    - destruct ys2; try easy. destruct lis; try easy.
      inversion H2. subst. clear H2. inversion H1. subst. clear H1.
      specialize(IHn lis G1 g s0 s s' p ys2).
      assert(gttTC (g_send s s' (overwrite_lis n (Some (s0, G1)) lis)) (gtt_send s s' ys2) /\
      (forall n0 : fin, exists m : fin, guardG n0 m (g_send s s' (overwrite_lis n (Some (s0, G1)) lis))) /\
      isgParts p (g_send s s' (overwrite_lis n (Some (s0, G1)) lis))).
      apply IHn; try easy.
      destruct H1 as (Hta,(Htb,Htc)).
      clear H6 H9 IHn.
      pinversion Hta. subst. clear Hta.
      specialize(guard_cont Htb); intros. clear Htb.
      split.
      - pfold. constructor. constructor; try easy.
      - split. apply guard_cont_b. constructor; try easy.
      - inversion Htc. subst. easy. subst. easy.
        subst.
        apply pa_sendr with (n := S n0) (s := s1) (g := g0); try easy.
    apply gttT_mon.
    apply gttT_mon.
    left. easy.
Qed.

Lemma part_cont_false_all : forall ys2 s s' p,
      p <> s -> p <> s' ->
      wfgC (gtt_send s s' ys2) ->
      (isgPartsC p (gtt_send s s' ys2) -> False) ->
      List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ (isgPartsC p g -> False))) ys2.
Proof.
  intros. apply part_cont_false_all_s with (s := s) (s' := s'); try easy.
  unfold wfgC in *. unfold wfgCw.
  destruct H1. exists x. easy.
Qed.
