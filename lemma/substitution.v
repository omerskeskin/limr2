From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
From SST Require Import src.header src.sim src.expr src.process src.local src.global src.balanced src.typecheck.
From SST Require Import lemma.inversion lemma.inversion_expr lemma.substitution_helper.

Lemma subst_proc_var : forall P Q T T' Gs GtA GtB X Q' m n, wtyped Q
  -> typ_proc Gs (GtA ++ (Some T :: GtB)) P T' -> length GtA = X
  -> substitutionP X m n Q P Q' -> typ_proc Gs (GtA ++ GtB) (incr_free 0 0 m n Q) T
  -> typ_proc Gs (GtA ++ GtB) Q' T'.
Proof.
  intros P. induction P using process_ind_ref.
  
  (* p_var *)
  intros. inversion H2; subst. 
  - specialize(inv_proc_var (p_var (length GtA)) (length GtA) T' Gs (GtA ++ Some T :: GtB) H0 (erefl (p_var (length GtA)))); intros.
    destruct H1. destruct H1. destruct H4.
    specialize(onth_exact GtA GtB (Some T)); intros.
    apply tc_sub with (t := x); try easy.
    specialize(eq_trans (esym H1) H6); intros. inversion H7. subst. easy.
    apply typable_implies_wfC with (P := (p_var (length GtA))) (Gs := Gs) (Gt := (GtA ++ Some T :: GtB)).
    easy.
  - specialize(inv_proc_var (p_var 0) 0 T' Gs (GtA ++ Some T :: GtB) H0 (erefl (p_var 0))); intros.
    destruct H1. destruct H1. destruct H4. destruct GtA; try easy.
    simpl in H1. subst.
    apply tc_sub with (t := x); try easy.
    apply tc_var; try easy.
    apply typable_implies_wfC with (P := p_var 0) (Gs := Gs) (Gt := ((Some x :: GtA) ++ Some T :: GtB)). easy.
  - specialize(inv_proc_var (p_var y.+1) y.+1 T' Gs (GtA ++ Some T :: GtB) H0 (erefl (p_var y.+1))); intros.
    destruct H1. destruct H1. destruct H4.
    apply tc_sub with (t := x); intros; try easy.
    apply tc_var; try easy.
    specialize(onth_more GtA GtB y (Some T) H10); intros.
    apply eq_trans with (y := (onth y.+1 (GtA ++ Some T :: GtB))); try easy.
    apply typable_implies_wfC with (P := p_var y.+1) (Gs := Gs) (Gt := (GtA ++ Some T :: GtB)). easy.
  - specialize(inv_proc_var (p_var y.+1) y.+1 T' Gs (GtA ++ Some T :: GtB) H0 (erefl (p_var y.+1))); intros.
    destruct H1. destruct H1. destruct H4.
    apply tc_sub with (t := x); intros; try easy.
    apply tc_var; try easy.
    specialize(onth_less GtA GtB y (Some T) H10 H5); intros.
    apply eq_trans with (y := onth y.+1 (GtA ++ Some T :: GtB)); try easy.
    apply typable_implies_wfC with (P := (p_var y.+1)) (Gs := Gs) (Gt := (GtA ++ Some T :: GtB)). easy.
  
  (* p_inact *)
  intros. inversion H2. subst.
  specialize(inv_proc_inact p_inact T' Gs (GtA ++ Some T :: GtB) H0 (erefl p_inact)); intros. subst. 
  constructor.
  
  (* p_send *)
  intros. inversion H2. subst.
  specialize(inv_proc_send pt lb ex P (p_send pt lb ex P) Gs (GtA ++ Some T :: GtB) T' H0 (erefl (p_send pt lb ex P))); intros.
  destruct H1. destruct H1. destruct H1. destruct H4.
  apply tc_sub with (t := (ltt_send pt (extendLis lb (Some (x, x0))))); try easy.
  constructor; try easy.
  apply IHP with (Q := Q) (T := T) (X := length GtA) (m := m) (n := n); try easy.
  apply typable_implies_wfC with (P := (p_send pt lb ex P)) (Gs := Gs) (Gt := (GtA ++ Some T :: GtB)). easy.
  
  (* p_recv *)
  intros. inversion H3. subst.
  specialize(inv_proc_recv pt llp (p_recv pt llp) Gs (GtA ++ Some T :: GtB) T' H1 (erefl (p_recv pt llp))); intros.
  destruct H2. destruct H2. destruct H5. destruct H6.
  apply tc_sub with (t := ltt_recv pt x); try easy.
  constructor; try easy.
  specialize(Forall2_length H12); intros.
  apply eq_trans with (y := length llp); try easy. 
  apply subst_proc_var_helper_1 with (llp := llp) (GtA := GtA) (m := m) (n := n) (Q := Q); try easy.
  apply subst_proc_var_recv_helper with (llp := llp) (Q := Q) (m := m) (n := n) (T := T); try easy.
  apply typable_implies_wfC with (P := (p_recv pt llp)) (Gs := Gs) (Gt := (GtA ++ Some T :: GtB)). easy.
  
  (* p_ite *)
  intros. inversion H2. subst.
  specialize(inv_proc_ite (p_ite e P1 P2) e P1 P2 T' Gs (GtA ++ Some T :: GtB) H0 (erefl (p_ite e P1 P2))); intros.
  destruct H1. destruct H1. destruct H1. destruct H4. destruct H5. destruct H6.
  apply tc_ite; try easy.
  - apply tc_sub with (t := x); try easy. 
    apply IHP1 with (Q := Q) (T := T) (X := length GtA) (m := m) (n := n); try easy.
    apply typable_implies_wfC with (P := p_ite e P1 P2) (Gs := Gs) (Gt := (GtA ++ Some T :: GtB)). easy.
  - apply tc_sub with (t := x0); try easy.
    apply IHP2 with (Q := Q) (T := T) (X := length GtA) (m := m) (n := n); try easy.
    apply typable_implies_wfC with (P := p_ite e P1 P2) (Gs := Gs) (Gt := (GtA ++ Some T :: GtB)). easy.
  
  (* p_rec *)
  intros. inversion H2. subst.
  specialize(inv_proc_rec (p_rec P) P T' Gs (GtA ++ Some T :: GtB) H0 (erefl (p_rec P))); intros.
  destruct H1. destruct H1.
  apply tc_sub with (t := x); try easy.
  apply tc_mu.
  specialize(IHP Q T x Gs (Some x :: GtA) GtB (length (Some x :: GtA)) Q'0 m.+1 n H); intros.
  apply IHP; try easy.
  apply slideT; try easy.
  apply typable_implies_wfC with (P := p_rec P) (Gs := Gs) (Gt := (GtA ++ Some T :: GtB)). easy.
Qed.

Lemma inj_substP : forall [P' m n k P Q Q0], 
    substitutionP m n k P P' Q -> 
    substitutionP m n k P P' Q0 -> 
    Q = Q0.
Proof.
  induction P' using process_ind_ref; intros.
  - inversion H; try easy.
    subst. 
    inversion H0; try easy.
    subst.
    inversion H0; try easy.
    subst.
    inversion H0; try easy. subst.
    specialize(triad_le m y H7 H9); intros. easy.
    subst. inversion H0; try easy.
    subst.
    destruct m; try easy.
    specialize(triad_le y m H7 H9); intros. easy.
  - inversion H. subst. inversion H0. subst. easy.
  - inversion H. subst.
    inversion H0. subst.
    specialize(IHP' m n k P Q' Q'0 H10 H11). subst. easy.
  - inversion H0. subst. inversion H1. subst.
    assert(ys = ys0).
    {
      clear H0 H1. revert H10 H9 H. revert m n k P ys ys0. clear pt.
      induction llp; intros.
      - destruct ys0; try easy. destruct ys; try easy.
      - destruct ys0; try easy. destruct ys; try easy.
        inversion H10. subst. clear H10. inversion H9. subst. clear H9.
        inversion H. subst. clear H.
        specialize(IHllp m n k P ys ys0 H5 H7 H6); intros. subst. clear H6 H7 H5.
        destruct H3. 
        - destruct H. subst. destruct H4. destruct H. subst. easy.
          destruct H as (k1,(l1,Ha)). easy.
        - destruct H as (k1,(l1,(Ha,(Hb,Hc)))). subst.
          destruct H4; try easy. destruct H as (k2,(l2,(Hf,(Hd,He)))). inversion Hf. subst.
          specialize(H2 m n (S k) P l1 l2 Hc He). subst. easy.
    }
    subst. easy.
  - inversion H. subst. inversion H0. subst.
    specialize(IHP'1 m n k P Q1 Q3 H9 H11); intros. subst. 
    specialize(IHP'2 m n k P Q2 Q4 H10 H12); intros. subst. easy.
  - inversion H. subst. inversion H0. subst.
    specialize(IHP' (S m) (S n) k P Q' Q'0 H6 H7). subst. easy. 
Qed.

Lemma subst_proc_varf : forall P Q T T' Gs Gt Q',
     typ_proc Gs (Some T :: Gt) P T' 
  -> substitutionP 0 0 0 Q P Q' -> typ_proc Gs Gt Q T
  -> typ_proc Gs Gt Q' T'.
Proof.
  intros.
  specialize(subst_proc_var P Q T T' Gs nil Gt 0 Q' 0 0); intros.
  simpl in H2. apply H2; try easy.
  apply typable_implies_wtyped with (Gs := Gs) (Gt := Gt) (T := T). easy.
  specialize(trivial_incr 0 0 Q); intros.
  replace (incr_free 0 0 0 0 Q) with Q. easy.
Qed.

Lemma _subst_expr_var : forall v Gs Gt P S T,
        typ_proc (Some S :: Gs) Gt P T -> 
        typ_expr Gs v S -> 
        typ_proc Gs Gt (subst_expr_proc P v 0 0) T.
Proof.
  intros. 
  specialize(_subst_expr_var_helper v 0 P nil Gs Gt S T); intros. simpl in H1. apply H1; try easy.
  specialize(trivial_incrE 0 v); intros. replace (incr_freeE 0 0 v) with v. easy.
Qed.