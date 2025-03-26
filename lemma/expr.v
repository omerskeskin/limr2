From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
From SST Require Import src.header src.sim src.expr src.typecheck.
From SST Require Import lemma.inversion_expr.

Lemma expr_eval_n : forall e, typ_expr nil e snat -> (exists k, stepE e (e_val (vnat k))).
Proof.
  induction e; intros; try easy.
  - specialize(inv_expr_var (e_var n) n nil snat H (erefl (e_var n))); intros.
    destruct H0 as (S',(Ha,Hb)). destruct n; try easy.
  - specialize(inv_expr_vali nil (e_val v) snat v H (erefl (e_val v))); intros.
    destruct H0.
    - destruct H0 as (k,(Ha,Hb)). subst. easy.
    - destruct H0. destruct H0 as (k,(Ha,Hb)). subst. exists k. constructor.
    - destruct H0 as (k,(Ha,Hb)). subst. easy.
  - specialize(inv_expr_succ nil (e_succ e) snat e H (erefl (e_succ e))); intros.
    destruct H0 as (H0,H1). destruct H1. specialize(IHe H0). destruct IHe as (k,Ha). exists (k+1). constructor. easy. easy.
  - specialize(inv_expr_neg nil (e_neg e) snat e H (erefl (e_neg e))); intros.
    easy.
  - specialize(inv_expr_not nil (e_not e) snat e H (erefl (e_not e))); intros.
    destruct H0. easy.
  - specialize(inv_expr_gt nil (e_gt e1 e2) snat e1 e2 H (erefl (e_gt e1 e2))); intros.
    destruct H0 as (Ha,(Hb,Hc)). easy.
  - specialize(inv_expr_plus nil (e_plus e1 e2) snat e1 e2 H (erefl (e_plus e1 e2))); intros.
    easy.
  - specialize(inv_expr_det nil (e_det e1 e2) snat e1 e2 H (erefl (e_det e1 e2))); intros.
    destruct H0 as (k,(Ha,(Hb,Hc))). inversion Hc. subst.
    specialize(IHe1 Ha). destruct IHe1. exists x. constructor. easy.
Qed.

Lemma expr_eval_i : forall e, typ_expr nil e sint -> (exists k, stepE e (e_val (vint k))) \/ (exists k, stepE e (e_val (vnat k))).
Proof.
  induction e; intros; try easy.
  - specialize(inv_expr_var (e_var n) n nil sint H (erefl (e_var n))); intros.
    destruct H0 as (S',(Ha,Hb)). destruct n; try easy.
  - specialize(inv_expr_vali nil (e_val v) sint v H (erefl (e_val v))); intros.
    destruct H0.
    - destruct H0 as (k,(Ha,Hb)). subst. left. exists k. constructor.
    - destruct H0. destruct H0 as (k,(Ha,Hb)). subst. right. exists k. constructor.
    - destruct H0 as (k,(Ha,Hb)). subst. easy.
  - specialize(inv_expr_succ nil (e_succ e) sint e H (erefl (e_succ e))); intros.
    destruct H0 as (H0,H1). destruct H1. right. easy.
    specialize(expr_eval_n e H0); intros. destruct H2 as (k,H2). 
    right. exists (k+1). constructor. easy.
  - specialize(inv_expr_neg nil (e_neg e) sint e H (erefl (e_neg e))); intros.
    destruct H0. specialize(IHe H1).
    destruct IHe.
    - destruct H2 as (k,Ha). left. exists (Z.opp k). constructor. easy.
    - destruct H2 as (k,Ha). left. exists (Z.opp (Z.of_nat k)). apply ec_neg2. easy.
  - specialize(inv_expr_not nil (e_not e) sint e H (erefl (e_not e))); intros.
    destruct H0. easy.
  - specialize(inv_expr_gt nil (e_gt e1 e2) sint e1 e2 H (erefl (e_gt e1 e2))); intros.
    destruct H0 as (Ha,(Hb,Hc)). easy.
  - specialize(inv_expr_plus nil (e_plus e1 e2) sint e1 e2 H (erefl (e_plus e1 e2))); intros.
    destruct H0 as (Ha,(Hb,Hc)). specialize(IHe1 Hb). specialize(IHe2 Hc).
    left.
    - destruct IHe1.
      destruct H0 as (k,H0).
      destruct IHe2.
      - destruct H1 as (k1,H1). exists (Z.add k k1). constructor; try easy.
      - destruct H1 as (k1,H1). exists (Z.add k (Z.of_nat k1)). constructor; try easy.
    - destruct H0 as (k,H0).
      destruct IHe2.
      - destruct H1 as (k1,H1). exists (Z.add (Z.of_nat k) k1). constructor; try easy.
      - destruct H1 as (k1,H1). exists (Z.add (Z.of_nat k) (Z.of_nat k1)). constructor; try easy.
  - specialize(inv_expr_det nil (e_det e1 e2) sint e1 e2 H (erefl (e_det e1 e2))); intros.
    destruct H0 as (k,(Ha,(Hb,Hc))). inversion Hc. subst.
    - specialize(expr_eval_n e1 Ha); intros. destruct H0 as (k,Hd). right. exists k. constructor. easy.
    - subst.
      specialize(IHe1 Ha). destruct IHe1.
      destruct H0. left. exists x. constructor. easy.
      destruct H0. right. exists x. constructor. easy.
Qed.

Lemma expr_eval_b : forall e, typ_expr nil e sbool -> (stepE e (e_val (vbool true)) \/ stepE e (e_val (vbool false))).
Proof.
  induction e; intros; try easy.
  - specialize(inv_expr_var (e_var n) n nil sbool H (erefl (e_var n))); intros.
    destruct H0 as (S',(Ha,Hb)). destruct n; try easy.
  - specialize(inv_expr_vali nil (e_val v) sbool v H (erefl (e_val v))); intros.
    destruct H0.
    - destruct H0 as (k,(Ha,Hb)). easy.
    - destruct H0. destruct H0 as (k,(Ha,Hb)). subst. inversion Ha.
    - destruct H0 as (k,(Ha,Hb)). subst. destruct k. left. apply ec_refl. right. apply ec_refl. 
  - specialize(inv_expr_succ nil (e_succ e) sbool e H (erefl (e_succ e))); intros.
    destruct H0 as (H0,H1). destruct H1. right. easy. easy.
  - specialize(inv_expr_neg nil (e_neg e) sbool e H (erefl (e_neg e))); intros.
    easy.
  - specialize(inv_expr_not nil (e_not e) sbool e H (erefl (e_not e))); intros.
    destruct H0.
    specialize(IHe H1).
    destruct IHe. right. constructor; try easy.
    left. constructor; try easy.
  - specialize(inv_expr_gt nil (e_gt e1 e2) sbool e1 e2 H (erefl (e_gt e1 e2))); intros.
    destruct H0 as (Ha,(Hb,Hc)).
    specialize(expr_eval_i e1 Hb); intros. 
    specialize(expr_eval_i e2 Hc); intros.
    clear Ha H IHe1 IHe2.
    destruct H0.
    - destruct H as (k,H).
      destruct H1.
      - destruct H0 as (k1,H0). 
        specialize(Zle_or_lt k k1); intros. destruct H1. 
        right. apply ec_gt_f3 with (m := k) (n := k1); try easy.
        left. apply ec_gt_t3 with (m := k) (n := k1); try easy.
      - destruct H0 as (k1,H0).
        specialize(Zle_or_lt k (Z.of_nat k1)); intros. destruct H1. 
        right. apply ec_gt_f2 with (m := k) (n := k1); try easy.
        left. apply ec_gt_t2 with (m := k) (n := k1); try easy.
    - destruct H as (k,H).
      destruct H1.
      - destruct H0 as (k1,H0).
        specialize(Zle_or_lt (Z.of_nat k) k1); intros. destruct H1. 
        right. apply ec_gt_f1 with (m := k) (n := k1); try easy.
        left. apply ec_gt_t1 with (m := k) (n := k1); try easy.
      - destruct H0 as (k1,H0).
        specialize(Zle_or_lt (Z.of_nat k) (Z.of_nat k1)); intros. destruct H1. 
        right. apply ec_gt_f0 with (m := k) (n := k1); try easy.
        left. apply ec_gt_t0 with (m := k) (n := k1); try easy.
  - specialize(inv_expr_plus nil (e_plus e1 e2) sbool e1 e2 H (erefl (e_plus e1 e2))); intros.
    easy.
  - specialize(inv_expr_det nil (e_det e1 e2) sbool e1 e2 H (erefl (e_det e1 e2))); intros.
    destruct H0 as (k,(Ha,(Hb,Hc))). inversion Hc. subst.
    specialize(IHe1 Ha). destruct IHe1. left. constructor. easy. right. constructor. easy.
Qed.

Lemma expr_eval_ss : forall ex S, typ_expr nil ex S -> exists v, stepE ex (e_val v).
Proof.
  intros.
  destruct S. 
  - specialize(expr_eval_b ex H); intros. destruct H0. exists (vbool true). easy. exists (vbool false). easy.
  - specialize(expr_eval_i ex H); intros. destruct H0. destruct H0. exists (vint x). easy. destruct H0. exists (vnat x). easy.
  - specialize(expr_eval_n ex H); intros. destruct H0. exists (vnat x). easy.
Qed.

Lemma expr_typ_step : forall Gs e e' S, typ_expr Gs e S -> stepE e e' -> typ_expr Gs e' S.
Proof.
  intros. revert H. revert S. induction H0; intros; try easy.
  - specialize(inv_expr_succ Gs (e_succ e) S e H (erefl (e_succ e))); intros.
    destruct H1. destruct H2; subst.
    apply sc_valn.
    apply sc_sub with (s := snat). apply sc_valn. apply sni.
  - specialize(inv_expr_neg Gs (e_neg e) S e H (erefl (e_neg e))); intros.
    destruct H1. subst. apply sc_vali.
  - specialize(inv_expr_neg Gs (e_neg e) S e H (erefl (e_neg e))); intros.
    destruct H1. subst. apply sc_vali.
  - specialize(inv_expr_not Gs (e_not e) S e H (erefl (e_not e))); intros.
    destruct H1. subst. apply sc_valb.
  - specialize(inv_expr_not Gs (e_not e) S e H (erefl (e_not e))); intros.
    destruct H1. subst. apply sc_valb.
  - specialize(inv_expr_gt Gs (e_gt e e') S e e' H0 (erefl (e_gt e e'))); intros.
    destruct H1. destruct H2. subst. apply sc_valb.
  - specialize(inv_expr_gt Gs (e_gt e e') S e e' H0 (erefl (e_gt e e'))); intros.
    destruct H1. destruct H2. subst. apply sc_valb.
  - specialize(inv_expr_gt Gs (e_gt e e') S e e' H0 (erefl (e_gt e e'))); intros.
    destruct H1. destruct H2. subst. apply sc_valb.
  - specialize(inv_expr_gt Gs (e_gt e e') S e e' H0 (erefl (e_gt e e'))); intros.
    destruct H1. destruct H2. subst. apply sc_valb.
  - specialize(inv_expr_gt Gs (e_gt e e') S e e' H0 (erefl (e_gt e e'))); intros.
    destruct H1. destruct H2. subst. apply sc_valb.
  - specialize(inv_expr_gt Gs (e_gt e e') S e e' H0 (erefl (e_gt e e'))); intros.
    destruct H1. destruct H2. subst. apply sc_valb.
  - specialize(inv_expr_gt Gs (e_gt e e') S e e' H0 (erefl (e_gt e e'))); intros.
    destruct H1. destruct H2. subst. apply sc_valb.
  - specialize(inv_expr_gt Gs (e_gt e e') S e e' H0 (erefl (e_gt e e'))); intros.
    destruct H1. destruct H2. subst. apply sc_valb.
  - specialize(inv_expr_plus Gs (e_plus e e') S e e' H (erefl (e_plus e e'))); intros.
    destruct H0. destruct H1. subst. apply sc_vali.
  - specialize(inv_expr_plus Gs (e_plus e e') S e e' H (erefl (e_plus e e'))); intros.
    destruct H0. destruct H1. subst. apply sc_vali.
  - specialize(inv_expr_plus Gs (e_plus e e') S e e' H (erefl (e_plus e e'))); intros.
    destruct H0. destruct H1. subst. apply sc_vali.
  - specialize(inv_expr_plus Gs (e_plus e e') S e e' H (erefl (e_plus e e'))); intros.
    destruct H0. destruct H1. subst. apply sc_vali.
  - specialize(inv_expr_det Gs (e_det m n) S m n H (erefl (e_det m n))); intros.
    destruct H1. destruct H1. destruct H2.
    apply sc_sub with (s := x); intros; try easy. apply IHstepE; try easy.
  - specialize(inv_expr_det Gs (e_det m n) S m n H (erefl (e_det m n))); intros.
    destruct H1. destruct H1. destruct H2.
    apply sc_sub with (s := x); intros; try easy. apply IHstepE; try easy.
  - specialize(IHstepE1 S H). specialize(IHstepE2 S). apply IHstepE2; try easy.
Qed.