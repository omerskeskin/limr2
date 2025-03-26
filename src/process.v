From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
From SST Require Import src.header src.sim src.expr.

Section process.

Inductive process : Type := 
  | p_send : part -> label -> expr -> process -> process
  | p_recv : part -> list(option process) -> process 
  | p_ite : expr -> process -> process -> process
  | p_rec : process -> process
  | p_var : nat -> process
  | p_inact : process.

Section process_ind_ref.
  Variable P : process -> Prop.
  Hypothesis P_var : forall n, P (p_var n).
  Hypothesis P_inact : P (p_inact).
  Hypothesis P_send : forall pt lb ex pr, P pr -> P (p_send pt lb ex pr).
  Hypothesis P_recv : forall pt llp, Forall (fun u => 
      match u with 
        | Some k => P k 
        | None   => True 
      end) llp -> P (p_recv pt llp).
  Hypothesis P_ite : forall e P1 P2, P P1 -> P P2 -> P (p_ite e P1 P2).
  Hypothesis P_rec : forall pr, P pr -> P (p_rec pr).
  
  Fixpoint process_ind_ref p : P p.
  Proof.
    destruct p.
    - apply (P_send s n e p (process_ind_ref p)).
    - apply (P_recv).
      induction l as [ | c l IH].
      clear process_ind_ref. 
      - easy.
      - apply (Forall_cons); intros. destruct c. 
        - generalize (process_ind_ref p); intros. easy. easy.
        - apply IH.
    - apply (P_ite e p1 p2 (process_ind_ref p1) (process_ind_ref p2)).
    - apply (P_rec p (process_ind_ref p)). 
    - apply (P_var n).
    - apply (P_inact).
Qed.

End process_ind_ref.

Inductive wtyped : process -> Prop := 
  | wp_var : forall n, wtyped (p_var n)
  | wp_inact : wtyped p_inact
  | wp_send: forall pt lb ex pr, wtyped pr -> wtyped (p_send pt lb ex pr)
  | wp_recv : forall pt llp, SList llp -> List.Forall (fun u => (u = None) \/ (exists k, u = Some k /\ wtyped k)) llp -> wtyped (p_recv pt llp)
  | wp_ite : forall e P1 P2, wtyped P1 -> wtyped P2 -> wtyped (p_ite e P1 P2)
  | wp_rec : forall pr, wtyped pr -> wtyped (p_rec pr).

Section substitution.

Fixpoint incr_freeE (fv m : fin) (e : expr) :=
  match e with
    | e_var n    => e_var (if fv <= n then (n + m)%coq_nat else n)
    | e_val v    => e_val v 
    | e_succ n   => e_succ (incr_freeE fv m n)
    | e_neg n    => e_neg (incr_freeE fv m n)
    | e_not n    => e_not (incr_freeE fv m n)
    | e_gt u v   => e_gt (incr_freeE fv m u) (incr_freeE fv m v)
    | e_plus u v => e_plus (incr_freeE fv m u) (incr_freeE fv m v) 
    | e_det u v  => e_det (incr_freeE fv m u) (incr_freeE fv m v)
  end. 

Fixpoint incr_free (fvP fvE m k : fin) (P : process) : process :=
  match P with 
    | p_var n          => p_var (if fvP <= n then ((n + m)%coq_nat) else n)
    | p_inact          => p_inact
    | p_send p l e P'  => p_send p l (incr_freeE fvE k e) (incr_free fvP fvE m k P')
    | p_recv p llp     => p_recv p (List.map (
        fun u => match u with 
          | Some p' => Some (incr_free fvP (S fvE) m k p')
          | None    => None
        end) llp)
    | p_ite e P1 P2    => p_ite (incr_freeE fvE k e) (incr_free fvP fvE m k P1) (incr_free fvP fvE m k P2)
    | p_rec P'         => p_rec (incr_free (S fvP) fvE m k P')
  end.

Definition subst_relation (A : Type) : Type := fin -> fin -> fin -> A -> A -> A -> Prop.

(* relation of sub_from, sub_to, proc_before_sub, proc_after_sub, rec case, ensures is fresh in both x and P *)
Inductive substitutionP : subst_relation process :=
  | sub_var_is   : forall P x m n,              substitutionP x m n P (p_var x) (incr_free 0 0 m n P)
  | sub_var_notz : forall P x m n, x <> 0 ->    substitutionP x m n P (p_var 0) (p_var 0)
  | sub_var_not1 : forall P x y m n, x <> S y -> x <= y -> substitutionP x m n P (p_var (S y)) (p_var y)
  | sub_var_not2 : forall P x y m n, x <> S y -> y < x  -> substitutionP x m n P (p_var (S y)) (p_var (S y))
  | sub_inact    : forall P x m n,              substitutionP x m n P (p_inact) (p_inact)
  | sub_send     : forall P x m n pt l e P' Q', substitutionP x m n P P' Q' -> substitutionP x m n P (p_send pt l e P') (p_send pt l e Q')
  | sub_recv     : forall P x m n pt xs ys, 
  List.Forall2 (fun u v => 
    (u = None /\ v = None) \/
    (exists k l, u = Some k /\ v = Some l /\ substitutionP x m (S n) P k l)  
  ) xs ys -> substitutionP x m n P (p_recv pt xs) (p_recv pt ys)
  | sub_ite       : forall P x m n e P1 P2 Q1 Q2, substitutionP x m n P P1 Q1 -> substitutionP x m n P P2 Q2 -> substitutionP x m n P (p_ite e P1 P2) (p_ite e Q1 Q2)
  | sub_rec       : forall P x m n P' Q', substitutionP (S x) (S m) n P P' Q' -> substitutionP x m n P (p_rec P') (p_rec Q').

End substitution.

Inductive peq_w : process -> process -> Prop := 
  | peq_var : forall n, peq_w (p_var n) (p_var n)
  | peq_inact : peq_w p_inact p_inact
  | peq_send : forall pt lb e e' p1 p2, peq_w p1 p2 -> peq_w (p_send pt lb e p1) (p_send pt lb e' p2)
  | peq_recv : forall pt xs ys, Forall2 (fun u v => (u = None /\ v = None) \/ (exists p p', u = Some p /\ v = Some p' /\ peq_w p p')) xs ys -> peq_w (p_recv pt xs) (p_recv pt ys)
  | peq_ite  : forall e1 p1 q1 e2 p2 q2, peq_w p1 p2 -> peq_w q1 q2 -> peq_w (p_ite e1 p1 q1) (p_ite e2 p2 q2)
  | peq_rec : forall p1 p2, peq_w p1 p2 -> peq_w (p_rec p1) (p_rec p2).

Fixpoint subst_expr (n d : fin) (e : expr) (e1 : expr) : expr :=
  match e1 with 
    | e_var 0     => if Nat.eqb n 0 then (incr_freeE 0 d e) else e_var 0
    | e_var (S m) => if Nat.eqb (S m) n then (incr_freeE 0 d e) else 
                     if Nat.ltb (S m) n then e_var (S m) else e_var m 
    | e_succ e' => e_succ (subst_expr n d e e')
    | e_neg e' => e_neg (subst_expr n d e e')
    | e_not e' => e_not (subst_expr n d e e')
    | e_gt e' e'' => e_gt (subst_expr n d e e') (subst_expr n d e e'')
    | e_plus e' e'' => e_plus (subst_expr n d e e') (subst_expr n d e e'')
    | e_det e' e'' => e_det (subst_expr n d e e') (subst_expr n d e e'')
    | _ => e1
  end.

Fixpoint subst_expr_proc (p : process) (e : expr) (n d : fin) : process :=
  match p with 
    | p_send pt l e' P => p_send pt l (subst_expr n d e e') (subst_expr_proc P e n d)
    | p_ite e' P Q     => p_ite (subst_expr n d e e') (subst_expr_proc P e n d) (subst_expr_proc Q e n d)
    | p_recv pt lst    => p_recv pt (map (fun x => match x with
                                                | None => None
                                                | Some y => Some (subst_expr_proc y e (S n) (S d))
                                               end) lst)
    | p_rec P          => p_rec (subst_expr_proc P e n d)
    | _ => p
  end.

Inductive guardP : fin -> fin -> process -> Prop :=  
  | gp_nil : forall m G, guardP 0 m G
  | gp_inact : forall n m, guardP n m p_inact
  | gp_send : forall n m pt l e g, guardP n m g -> guardP (S n) m (p_send pt l e g)
  | gp_recv : forall n m p lis, List.Forall (fun u => u = None \/ (exists g, u = Some g /\ guardP n m g)) lis -> guardP (S n) m (p_recv p lis)
  | gp_ite : forall n m P Q e, guardP n m P -> guardP n m Q -> guardP n (S m) (p_ite e P Q)
  | gp_rec : forall n m g Q, substitutionP 0 0 0 (p_rec g) g Q -> guardP n m Q -> guardP n (S m) (p_rec g).

Inductive betaPr : relation process := 
  | betaPr_sin : forall P Q, substitutionP 0 0 0 (p_rec P) P Q -> betaPr (p_rec P) Q.

End process.

Lemma guardP_cont_recv_n : forall l xs y q, 
       (forall n : fin, exists m : fin, guardP n m (p_recv q xs)) -> 
        onth l xs = Some y -> 
        (forall n : fin, exists m : fin, guardP n m y).
Proof.
  induction l; intros; try easy.
  - destruct xs; try easy.
    simpl in H0. subst. specialize(H (Nat.succ n)).
    destruct H. inversion H. subst.
    inversion H3. subst. destruct H2; try easy.
    destruct H0 as (g,(Ha,Hb)). inversion Ha. subst. exists x. easy.
  - destruct xs; try easy.
    specialize(IHl xs y q). apply IHl; try easy.
    intros. specialize(H n0). destruct H.
    inversion H. subst. exists 0. constructor.
    subst. exists x. inversion H4. subst. constructor; try easy.
Qed. 

Lemma peq_after_incr : forall g p0 m n k l,
        peq_w g p0 -> 
        peq_w (incr_free m n k l g) (incr_free m n k l p0).
Proof.
  induction g using process_ind_ref; intros; try easy.
  - inversion H. subst. constructor.
  - inversion H. subst. constructor.
  - inversion H. subst. constructor; try easy. apply IHg; try easy.
  - inversion H0. subst. constructor; try easy.
    revert H4 H. clear H0. revert llp m n k l.
    induction ys; intros; try easy.
    - destruct llp; try easy.
    - destruct llp; try easy.
      inversion H. subst. clear H. inversion H4. subst. clear H4.
      specialize(IHys llp m n k l H7 H3). constructor; try easy. clear IHys H3 H7.
      destruct H5.
      - destruct H. subst. left. easy.
      - destruct H as (p1,(p2,(Ha,(Hb,Hc)))). subst.
        right. exists (incr_free m (S n) k l p1). exists (incr_free m (S n) k l p2). split. easy.
        split. easy.
        apply H2; try easy.
  - inversion H. subst. constructor. apply IHg1; try easy. apply IHg2; try easy.
  - inversion H. subst. constructor. apply IHg; try easy.
Qed.

Lemma peq_after_subst : forall g1 g Q m n k p0 p1,
        substitutionP m n k g g1 Q -> 
        peq_w g p0 -> peq_w g1 p1 ->
        exists Q' : process, substitutionP m n k p0 p1 Q' /\ peq_w Q Q'.
Proof.
  induction g1 using process_ind_ref; intros.
  - inversion H1. subst.
    inversion H. subst.
    - exists (incr_free 0 0 n0 k p0). split. constructor. 
      apply peq_after_incr; try easy.
    - subst. exists (p_var 0). split. constructor. easy. constructor.
    - subst. exists (p_var y). split. constructor; try easy. constructor.
    - subst. exists (p_var (S y)). split. constructor; try easy. constructor.
  - inversion H1. subst. 
    inversion H. subst. exists p_inact. split. constructor. constructor.
  - inversion H1. subst.
    inversion H. subst.
    specialize(IHg1 g Q' m n k p0 p3 H12 H0 H7). destruct IHg1 as (q1,(Ha,Hb)).
    exists (p_send pt lb e' q1). split. constructor; try easy. constructor; try easy.
  - inversion H2. subst. inversion H0. subst.
    clear H2 H0.
    assert(exists ys3, Forall2 (fun u v => (u = None /\ v = None) \/ (exists p p', u = Some p /\ v = Some p' /\ substitutionP m n (S k) p0 p p')) ys ys3 /\ Forall2 (fun u v => (u = None /\ v = None) \/ (exists p p', u = Some p /\ v = Some p' /\ peq_w p p')) ys0 ys3).
    {
      revert H11 H6 H1 H.
      revert llp g m n k p0 ys0.
      induction ys; intros.
      - destruct llp; try easy. destruct ys0; try easy. exists nil. easy.
      - destruct llp; try easy. destruct ys0; try easy.
        inversion H11. subst. clear H11. inversion H6. subst. clear H6.
        inversion H. subst. clear H.
        specialize(IHys llp g m n k p0 ys0 H7 H9 H1 H6).
        clear H6 H9 H7.
        destruct IHys as (ys3,(Ha,Hb)).
        destruct H4.
        - destruct H. subst. destruct H5. destruct H. subst.
          exists (None :: ys3). split. constructor; try easy. left. easy. constructor; try easy. left. easy. 
          destruct H as (p1,(p2,Hc)). easy.
        - destruct H as (k1,(l1,(Hc,(Hd,He)))). subst.
          destruct H5; try easy. destruct H as (p1,(p2,(Hf,(Hg,Hh)))). inversion Hf. subst.
          specialize(H3 g l1 m n (S k) p0 p2 He H1 Hh).
          destruct H3 as (q1,(Hg,Hi)).
          exists (Some q1 :: ys3).
          - split. constructor; try easy. right. exists p2. exists q1. easy.
          - constructor; try easy. right. exists l1. exists q1. easy.
    }
    destruct H0 as (ys3,(Ha,Hb)). exists (p_recv pt ys3).
    split. constructor; try easy. constructor; try easy. 
  - inversion H1. subst. inversion H. subst.
    specialize(IHg1_1 g Q1 m n k p0 p3 H12 H0 H6). destruct IHg1_1 as (q1,(Ha,Hb)).
    specialize(IHg1_2 g Q2 m n k p0 q2 H13 H0 H7). destruct IHg1_2 as (q3,(Hc,Hd)).
    exists (p_ite e2 q1 q3). split. constructor; try easy. constructor; try easy.
  - inversion H1. subst. inversion H. subst.
    specialize(IHg1 g Q' (S m) (S n) k p0 p3 H8 H0 H3).
    destruct IHg1 as (q1,(Ha,Hb)). exists (p_rec q1).
    split. constructor; try easy.
    constructor; try easy.
Qed.

Lemma guardP_peq_w : forall p1 p2, 
      peq_w p1 p2 -> 
      (forall n : fin, exists m : fin, guardP n m p1) -> 
      (forall n : fin, exists m : fin, guardP n m p2).
Proof.
  intros.
  specialize(H0 n). destruct H0 as (m, H0). exists m.
  revert H0 H. revert p1 p2 m.
  induction n; intros; try easy.
  - constructor.
  - revert IHn H H0. revert n p1 p2.
    induction m; intros; try easy.
    inversion H0.
    - subst. inversion H. subst. constructor.
    - subst. inversion H. subst. constructor. apply IHn with (p1 := g); try easy.
    - subst. inversion H. subst.
      constructor. revert H5 H2 IHn. clear H0 H. revert ys. induction lis; intros; try easy.
      - destruct ys; try easy.
      - destruct ys; try easy. inversion H2. subst. clear H2. inversion H5. subst. clear H5.
        specialize(IHlis ys H7 H3 IHn). constructor; try easy.
        clear IHlis H3 H7.
        destruct H4. left. easy.
        destruct H as (p1,(p2,(Ha,(Hb,Hc)))). subst.
        destruct H1; try easy. destruct H as (g1,(Hd,He)). inversion Hd. subst.
        right. exists p2. split. easy. apply IHn with (p1 := g1); try easy.
    assert(forall (p1 p2 : process),
      peq_w p1 p2 -> guardP (S n) m p1 -> guardP (S n) m p2).
    {
      intros. specialize(IHm n p0 p3). apply IHm; try easy.
    }
    inversion H0. subst.
    - inversion H. constructor.
    - subst. inversion H. subst. constructor. apply IHn with (p1 := g); try easy.
    - subst. inversion H. subst. constructor.
      revert H6 H3. clear H0 H. revert ys.
      induction lis; intros.
      - destruct ys; try easy.
      - destruct ys; try easy. inversion H6. subst. clear H6. inversion H3. subst. clear H3.
        specialize(IHlis ys H7 H5). constructor; try easy.
        destruct H4. left. easy.
        destruct H as (p1,(p2,(Ha,(Hb,Hc)))). subst.
        destruct H2; try easy. destruct H as (g1,(Hd,He)). inversion Hd. subst.
        right. exists p2. split. easy.
        apply IHn with (p1 := g1); try easy.
    - subst. inversion H. subst.
      constructor. apply H1 with (p1 := P); try easy. apply H1 with (p1 := Q); try easy.
    - subst. inversion H. subst.
      assert(exists Q', substitutionP 0 0 0 (p_rec p0) p0 Q' /\ peq_w Q Q').
      {
        apply peq_after_subst with (g1 := g) (g := p_rec g); try easy.
      }
      destruct H2 as (Q1,(Ha,Hb)).
      apply gp_rec with (Q := Q1); try easy.
      apply H1 with (p1 := Q); try easy.
Qed.

Lemma guardP_subst_expr : forall y v j k,
    (forall n : fin, exists m : fin, guardP n m y) -> 
    (forall n : fin, exists m : fin, guardP n m (subst_expr_proc y v j k)).
Proof.
  intros.
  apply guardP_peq_w with (p1 := y); try easy.
  clear H n. revert v j k.
  induction y using process_ind_ref; intros; try easy.
  - simpl. constructor.
  - simpl. constructor.
  - simpl. constructor. apply IHy; try easy.
  - simpl. constructor.
    revert H. revert pt v j k. induction llp; intros; try easy.
    - inversion H. subst. clear H. specialize(IHllp pt v j k H3). constructor; try easy.
      clear H3 IHllp.
      destruct a.
      - right. exists p. exists (subst_expr_proc p v (S j) (S k)). split. easy. split. easy.
        apply H2; try easy.
      - left. easy.
  - simpl. constructor.
    apply IHy1. apply IHy2.
  - simpl. constructor. apply IHy.
Qed.

Lemma guardP_break : forall P,
    (forall n : fin, exists m : fin, guardP n m P) -> 
    exists Q, multi betaPr P Q /\ (Q = p_inact \/ (exists e p1 p2, Q = p_ite e p1 p2) \/ (exists pt lb ex pr, Q = p_send pt lb ex pr) \/ (exists pt llp, Q = p_recv pt llp)).
Proof.
  intros.
  specialize(H 1). destruct H as (m, H).
  revert H. revert P.
  induction m; intros.
  - inversion H.
    - subst. exists p_inact. split. constructor. left. easy.
    - subst. exists (p_send pt l e g). split. constructor. right. right. left. exists pt. exists l. exists e. exists g. easy.
    - subst. exists (p_recv p lis). split. constructor. right. right. right. exists p. exists lis. easy.
  - inversion H. 
    - subst. exists p_inact. split. constructor. left. easy.
    - subst. exists (p_send pt l e g). split. constructor. right. right. left. exists pt. exists l. exists e. exists g. easy.
    - subst. exists (p_recv p lis). split. constructor. right. right. right. exists p. exists lis. easy.
    - subst. exists (p_ite e P0 Q). split. constructor.
      right. left. exists e. exists P0. exists Q. easy.
    - subst. specialize(IHm Q H3).
      destruct IHm as (Q1,(Ha,Hb)). exists Q1. split; try easy.
      apply multi_step with (y := Q); try easy. 
Qed.