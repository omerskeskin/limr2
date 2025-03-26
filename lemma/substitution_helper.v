From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
From SST Require Import src.header src.sim src.expr src.process src.local src.global src.balanced src.typecheck.
From SST Require Import lemma.inversion lemma.inversion_expr.

Lemma slideT_helper : forall llp Gs Gtl tm Gtr l X m k x,
    length Gtl = l ->
    Forall
      (fun u : option process =>
       match u with
       | Some k =>
           forall (X m l k0 : fin) (tm : option ltt) (Gs : ctxS) (Gtl Gtr : list (option ltt)) (T : ltt),
           typ_proc Gs (Gtl ++ Gtr) (incr_free l k0 X m k) T ->
           length Gtl = l -> typ_proc Gs (Gtl ++ tm :: Gtr) (incr_free l k0 X.+1 m k) T
       | None => True
       end) llp ->
    Forall2
       (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gs) (Gtl ++ Gtr) p t))
       (map
          (fun u : option process =>
           match u with
           | Some p' => Some (incr_free l k.+1 X m p')
           | None => None
           end) llp) x ->
    Forall2
      (fun (u : option process) (v : option (sort * ltt)) =>
       u = None /\ v = None \/
       (exists (p : process) (s : sort) (t : ltt),
          u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gs) (Gtl ++ tm :: Gtr) p t))
      (map
         (fun u : option process =>
          match u with
          | Some p' => Some (incr_free l k.+1 X.+1 m p')
          | None => None
          end) llp) x.
Proof.
  intro llp. induction llp; intros; try easy.
  - destruct x; try easy.
  - destruct x; try easy.
    simpl in *.
    specialize(Forall2_cons_iff (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gs) (Gtl ++ Gtr) p t)) (match a with
        | Some p' => Some (incr_free l k.+1 X m p')
        | None => None
        end) o (map
             (fun u : option process =>
              match u with
              | Some p' => Some (incr_free l k.+1 X m p')
              | None => None
              end) llp) x); intros. destruct H2. clear H3. specialize(H2 H1). clear H1.
    destruct H2.
    specialize(Forall_cons_iff (fun u : option process =>
        match u with
        | Some k =>
            forall (X m l k0 : fin) (tm : option ltt) (Gs : ctxS) (Gtl Gtr : list (option ltt)) (T : ltt),
            typ_proc Gs (Gtl ++ Gtr) (incr_free l k0 X m k) T ->
            length Gtl = l -> typ_proc Gs (Gtl ++ tm :: Gtr) (incr_free l k0 X.+1 m k) T
        | None => True
        end) a llp); intros. destruct H3. clear H4. specialize(H3 H0). clear H0. destruct H3.
    apply Forall2_cons; try easy.
    - destruct a; try easy. destruct H1. easy.
      destruct H1. destruct H1. destruct H1. destruct H1. destruct H4. subst.
      right. exists (incr_free (length Gtl) k.+1 X.+1 m p), x1, x2. split. easy. split. easy. 
      inversion H1. subst. apply H0; try easy.
    - destruct H1. destruct H1. subst. left. easy.
      destruct H1. destruct H1. destruct H1. destruct H1. easy.
    apply IHllp; try easy.
Qed.

Lemma slideTp : forall Q X m l k tm Gs Gtl Gtr T,
typ_proc Gs (Gtl ++ Gtr) (incr_free l k X m Q) T -> length Gtl = l -> typ_proc Gs (Gtl ++ [tm] ++ Gtr) (incr_free l k X.+1 m Q) T.
Proof.
  intro Q.
  induction Q using process_ind_ref; intros; try easy.
  - simpl in *. 
    specialize(inv_proc_var (p_var (if l <= n then (n + X)%coq_nat else n)) (if l <= n then (n + X)%coq_nat else n) T Gs (Gtl ++ Gtr) H (erefl (p_var (if l <= n then (n + X)%coq_nat else n)))); intros.
    destruct H1. destruct H1.
    case_eq (l <= n); intros.
    - replace (l <= n) with true in H, H1.
      apply tc_sub with (t := x); try easy. 
      apply tc_var; try easy.
      apply onth_morec with (l := l); try easy.
      specialize(typable_implies_wfC H); intros; try easy.
    - replace (l <= n) with false in H, H1.
      apply tc_sub with (t := x); try easy.
      apply tc_var; try easy.
      apply onth_lessc with (l := l); try easy.
      specialize(typable_implies_wfC H); intros; try easy.
  - simpl in *. 
    specialize(inv_proc_inact p_inact T Gs (Gtl++Gtr) H (erefl p_inact)); intros. subst. 
    apply tc_inact.
  - simpl in *.
    specialize(inv_proc_send pt lb (incr_freeE k m ex) (incr_free l k X m Q) (p_send pt lb (incr_freeE k m ex) (incr_free l k X m Q)) Gs (Gtl ++ Gtr) T H (erefl (p_send pt lb (incr_freeE k m ex) (incr_free l k X m Q)))); intros.
    destruct H1. destruct H1. destruct H1. destruct H2.
    apply tc_sub with (t := (ltt_send pt (extendLis lb (Some (x, x0))))); try easy.
    apply tc_send; try easy.
    apply IHQ. easy. easy.
    specialize(typable_implies_wfC H); intros; try easy.
  - simpl in *.
    specialize(inv_proc_recv pt (map
             (fun u : option process =>
              match u with
              | Some p' => Some (incr_free l k.+1 X m p')
              | None => None
              end) llp) (p_recv pt
          (map
             (fun u : option process =>
              match u with
              | Some p' => Some (incr_free l k.+1 X m p')
              | None => None
              end) llp)) Gs (Gtl ++ Gtr) T H0 (erefl (p_recv pt
          (map
             (fun u : option process =>
              match u with
              | Some p' => Some (incr_free l k.+1 X m p')
              | None => None
              end) llp)))); intros.
    destruct H2. destruct H2. destruct H3. destruct H4. 
    apply tc_sub with (t := (ltt_recv pt x)); try easy. constructor.
    specialize(Forall2_length H4); intros.
    specialize(map_length (fun u : option process =>
           match u with
           | Some p' => Some (incr_free l k.+1 X m p')
           | None => None
           end) llp); intros.
    specialize(eq_trans (esym H6) H7); intros. clear H6 H7.
    apply eq_trans with (y := length llp); try easy. 
    apply map_length; try easy.
    apply SList_map2 with (f := (incr_free l k.+1 X.+1 m)); try easy.
    specialize(SList_map (incr_free l k.+1 X m) llp H5); intros. easy.
    apply slideT_helper; try easy.
    specialize(typable_implies_wfC H0); intros; try easy.
  - simpl in *.
    specialize(inv_proc_ite (p_ite (incr_freeE k m e) (incr_free l k X m Q1) (incr_free l k X m Q2)) (incr_freeE k m e) (incr_free l k X m Q1) (incr_free l k X m Q2) T Gs (Gtl ++ Gtr) H (erefl (p_ite (incr_freeE k m e) (incr_free l k X m Q1) (incr_free l k X m Q2)))); intros.
    destruct H1. destruct H1. destruct H1. destruct H2. destruct H3. destruct H4.
    apply tc_ite; try easy.
    apply tc_sub with (t := x); try easy.
    apply IHQ1; try easy.
    specialize(typable_implies_wfC H); intros; try easy.
    apply tc_sub with (t := x0); try easy.
    apply IHQ2; try easy.
    specialize(typable_implies_wfC H); intros; try easy. 
  - simpl in *. 
    specialize(inv_proc_rec (p_rec (incr_free l.+1 k X m Q)) (incr_free l.+1 k X m Q) T Gs (Gtl++Gtr) H (erefl (p_rec (incr_free l.+1 k X m Q)))); intros.
    destruct H1. destruct H1. 
    specialize(IHQ X m l.+1 k tm Gs (Some x :: Gtl) Gtr x); intros.
    specialize(cat_cons (Some x) Gtl Gtr); intros.
    replace ((Some x :: Gtl) ++ Gtr) with (Some x :: Gtl ++ Gtr) in IHQ.
    specialize(IHQ H1); intros. simpl in IHQ.
    specialize(eq_S (length Gtl) l H0); intros.
    specialize(IHQ H4). clear H0 H4.
    apply tc_sub with (t := x); try easy.
    apply tc_mu; try easy.
    specialize(typable_implies_wfC H1); intros; try easy.
    specialize(typable_implies_wfC H); intros; try easy.
Qed.

Lemma slideT : forall Q X m tm Gs Gt T,
typ_proc Gs Gt (incr_free 0 0 X m Q) T -> typ_proc Gs (tm :: Gt) (incr_free 0 0 X.+1 m Q) T.
Proof.
  intros.
  specialize(slideTp Q X m 0 0 tm Gs [] Gt T H); intros. simpl in H0.
  apply H0; try easy.
Qed.

Lemma slideSp_e : forall k m ex x Gsl Gsr tm,
  typ_expr (Gsl ++ Gsr) (incr_freeE k m ex) x ->
  length Gsl = k ->
  typ_expr (Gsl ++ tm :: Gsr) (incr_freeE k m.+1 ex) x.
Proof. 
  intros k m ex. revert k m. induction ex; intros; try easy.
  - simpl in *. 
    specialize(inv_expr_var (e_var (if k <= n then (n + m)%coq_nat else n)) (if k <= n then (n + m)%coq_nat else n) (Gsl ++ Gsr) x H (erefl (e_var (if k <= n then (n + m)%coq_nat else n)))); intros.
    destruct H1. destruct H1.
    apply sc_sub with (s := x0); try easy.
    apply sc_var.
    case_eq (k <= n); intros.
    - replace (k <= n) with true in H1. subst.
      apply onth_morec with (l := length Gsl); try easy.
    - replace (k <= n) with false in H1. subst.
      apply onth_lessc with (l := length Gsl); try easy.
  - simpl in *. 
    specialize(inv_expr_vali (Gsl ++ Gsr) (e_val v) x v H (erefl (e_val v))); intros.
    destruct H1.
    - subst. destruct H1. destruct H0. subst. apply sc_vali.
    - subst. destruct H1. destruct H0. destruct H0. subst.
      inversion H0. subst. apply sc_sub with (s := snat); try easy. apply sc_valn.
      subst. apply sc_valn.
    - subst. destruct H0. destruct H0. subst. apply sc_valb.
  - simpl in *.
    specialize(inv_expr_succ (Gsl ++ Gsr) (e_succ (incr_freeE k m ex)) x (incr_freeE k m ex) H (erefl (e_succ (incr_freeE k m ex)))); intros.
    destruct H1. destruct H2.
    - subst. apply sc_succ; try easy. apply IHex; try easy.
    - subst. apply sc_sub with (s := snat); try easy. apply sc_succ; try easy. apply IHex; try easy.
      apply sni.
  - simpl in *.
    specialize(inv_expr_neg (Gsl ++ Gsr) (e_neg (incr_freeE k m ex)) x (incr_freeE k m ex) H (erefl (e_neg (incr_freeE k m ex)))); intros.
    destruct H1. subst. apply sc_neg. apply IHex; try easy.
  - simpl in *.
    specialize(inv_expr_not (Gsl ++ Gsr) (e_not (incr_freeE k m ex)) x (incr_freeE k m ex) H (erefl (e_not (incr_freeE k m ex)))); intros. 
    destruct H1. subst. apply sc_not. apply IHex; try easy.
  - simpl in *.
    specialize(inv_expr_gt (Gsl ++ Gsr) (e_gt (incr_freeE k m ex1) (incr_freeE k m ex2)) x (incr_freeE k m ex1) (incr_freeE k m ex2) H (erefl (e_gt (incr_freeE k m ex1) (incr_freeE k m ex2)))); intros.
    destruct H1. destruct H2.
    subst. apply sc_gt. apply IHex1; try easy. apply IHex2; try easy.
  - simpl in *.
    specialize(inv_expr_plus (Gsl ++ Gsr) (e_plus (incr_freeE k m ex1) (incr_freeE k m ex2)) x (incr_freeE k m ex1) (incr_freeE k m ex2) H (erefl (e_plus (incr_freeE k m ex1) (incr_freeE k m ex2)))); intros.
    destruct H1. destruct H2.
    subst. apply sc_plus. apply IHex1; try easy. apply IHex2; try easy.
  - simpl in *.
    specialize(inv_expr_det (Gsl ++ Gsr) (e_det (incr_freeE k m ex1) (incr_freeE k m ex2)) x (incr_freeE k m ex1) (incr_freeE k m ex2) H (erefl (e_det (incr_freeE k m ex1) (incr_freeE k m ex2)))); intros.
    destruct H1. destruct H1. destruct H2.
    constructor; try easy.
    apply IHex1; try easy.
    apply sc_sub with (s := x0); intros; try easy.
    apply IHex2; try easy.
    apply sc_sub with (s := x0); intros; try easy.
Qed.

Lemma slideS_helper : forall llp l k X m x Gsl Gsr Gt tm,
    length Gsl = k ->
    Forall
      (fun u : option process =>
       match u with
       | Some k =>
           forall (X m l k0 : fin) (tm : option sort) (Gsl Gsr : list (option sort)) 
             (Gt : ctxT) (T : ltt),
           typ_proc (Gsl ++ Gsr) Gt (incr_free l k0 X m k) T ->
           length Gsl = k0 -> typ_proc (Gsl ++ tm :: Gsr) Gt (incr_free l k0 X m.+1 k) T
       | None => True
       end) llp ->
    Forall2
       (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gsl ++ Gsr) Gt p t))
       (map
          (fun u : option process =>
           match u with
           | Some p' => Some (incr_free l k.+1 X m p')
           | None => None
           end) llp) x ->
    Forall2
      (fun (u : option process) (v : option (sort * ltt)) =>
       u = None /\ v = None \/
       (exists (p : process) (s : sort) (t : ltt),
          u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gsl ++ tm :: Gsr) Gt p t))
      (map
         (fun u : option process =>
          match u with
          | Some p' => Some (incr_free l k.+1 X m.+1 p')
          | None => None
          end) llp) x.
Proof.
  intro llp. induction llp; intros; try easy.
  - destruct x; try easy.
  - destruct x; try easy.
    specialize(Forall_cons_iff (fun u : option process =>
        match u with
        | Some k =>
            forall (X m l k0 : fin) (tm : option sort) (Gsl Gsr : list (option sort)) 
              (Gt : ctxT) (T : ltt),
            typ_proc (Gsl ++ Gsr) Gt (incr_free l k0 X m k) T ->
            length Gsl = k0 -> typ_proc (Gsl ++ tm :: Gsr) Gt (incr_free l k0 X m.+1 k) T
        | None => True
        end) a llp); intros. destruct H2. specialize(H2 H0). clear H0 H3. destruct H2.
    simpl in *.
    specialize(Forall2_cons_iff (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gsl ++ Gsr) Gt p t)) (match a with
        | Some p' => Some (incr_free l k.+1 X m p')
        | None => None
        end) o (map
             (fun u : option process =>
              match u with
              | Some p' => Some (incr_free l k.+1 X m p')
              | None => None
              end) llp) x); intros.
    destruct H3. specialize(H3 H1). clear H1 H4. destruct H3.
    apply Forall2_cons; try easy.
    - destruct a; try easy. destruct H1. easy.
      destruct H1. destruct H1. destruct H1. destruct H1. inversion H1. subst.
      right. destruct H4. subst. exists (incr_free l (length Gsl).+1 X m.+1 p), x1, x2.
      split. easy. split. easy. 
      specialize(H0 X m l (length Gsl).+1 tm (Some x1 :: Gsl) Gsr Gt x2 H4).
      simpl in H0. apply H0. easy.
    - destruct H1. destruct H1. subst. left; easy.
      destruct H1. destruct H1. destruct H1. destruct H1. easy.
    apply IHllp; try easy.
Qed.

Lemma slideSp : forall Q X m l k tm Gsl Gsr Gt T,
typ_proc (Gsl ++ Gsr) Gt (incr_free l k X m Q) T -> length Gsl = k -> typ_proc (Gsl ++ [tm] ++ Gsr) Gt (incr_free l k X m.+1 Q) T.
Proof.
  intro Q.
  induction Q using process_ind_ref; intros; try easy.
  - simpl in *. 
    specialize(inv_proc_var (p_var (if l <= n then (n + X)%coq_nat else n)) (if l <= n then (n + X)%coq_nat else n) T (Gsl ++ Gsr) Gt H (erefl (p_var (if l <= n then (n + X)%coq_nat else n)))); intros.
    destruct H1. destruct H1.
    apply tc_sub with (t := x); try easy. 
    apply tc_var; try easy.
    specialize(typable_implies_wfC H); intros; try easy.
  - simpl in *.
    specialize(inv_proc_inact p_inact T (Gsl ++ Gsr) Gt H (erefl p_inact)); intros. subst.
    apply tc_inact.
  - simpl in *.
    specialize(inv_proc_send pt lb (incr_freeE k m ex) (incr_free l k X m Q) (p_send pt lb (incr_freeE k m ex) (incr_free l k X m Q)) (Gsl ++ Gsr) Gt T H (erefl (p_send pt lb (incr_freeE k m ex) (incr_free l k X m Q) ))); intros.
    destruct H1. destruct H1. destruct H1. destruct H2.
    apply tc_sub with (t := (ltt_send pt (extendLis lb (Some (x, x0))))); try easy.
    apply tc_send; try easy.
    apply slideSp_e; try easy.
    apply IHQ; try easy.
    specialize(typable_implies_wfC H); intros; try easy. 
  - simpl in *.
    specialize(inv_proc_recv pt (map
             (fun u : option process =>
              match u with
              | Some p' => Some (incr_free l k.+1 X m p')
              | None => None
              end) llp) (p_recv pt
       (map
          (fun u : option process =>
           match u with
           | Some p' => Some (incr_free l k.+1 X m p')
           | None => None
           end) llp)) (Gsl ++ Gsr) Gt T H0 (erefl (p_recv pt
       (map
          (fun u : option process =>
           match u with
           | Some p' => Some (incr_free l k.+1 X m p')
           | None => None
           end) llp)))); intros. 
    destruct H2. destruct H2. destruct H3. destruct H4. 
    apply tc_sub with (t := (ltt_recv pt x)); try easy. 
    constructor.
    specialize(Forall2_length H4); intros. 
    specialize(map_length (fun u : option process =>
           match u with
           | Some p' => Some (incr_free l k.+1 X m p')
           | None => None
           end) llp); intros. 
    specialize(eq_trans (esym H6) H7); intros.
    apply eq_trans with (y := length llp); try easy. apply map_length. clear H2.
    apply SList_map2; try easy.
    specialize(SList_map (incr_free l k.+1 X m) llp H5); intros; try easy.
    apply slideS_helper; try easy.
    specialize(typable_implies_wfC H0); intros; try easy.
  - simpl in *.
    specialize(inv_proc_ite (p_ite (incr_freeE k m e) (incr_free l k X m Q1) (incr_free l k X m Q2)) (incr_freeE k m e) (incr_free l k X m Q1) (incr_free l k X m Q2) T (Gsl ++ Gsr) Gt H (erefl (p_ite (incr_freeE k m e) (incr_free l k X m Q1) (incr_free l k X m Q2)))); intros.
    destruct H1. destruct H1. destruct H1. destruct H2. destruct H3. destruct H4.
    apply tc_ite; try easy.
    apply slideSp_e; try easy.
    apply tc_sub with (t := x); try easy. apply IHQ1; try easy.
    specialize(typable_implies_wfC H); intros; try easy.
    apply tc_sub with (t := x0); try easy. apply IHQ2; try easy.
    specialize(typable_implies_wfC H); intros; try easy.
  - simpl in *.
    specialize(inv_proc_rec (p_rec (incr_free l.+1 k X m Q)) (incr_free l.+1 k X m Q) T (Gsl ++ Gsr) Gt H (erefl (p_rec (incr_free l.+1 k X m Q)))); intros.
    destruct H1. destruct H1. 
    apply tc_sub with (t := x); try easy.
    apply tc_mu. try easy.
    apply IHQ; try easy.
    specialize(typable_implies_wfC H1); intros; try easy.
    specialize(typable_implies_wfC H); intros; try easy.
Qed.

Lemma slideS : forall Q X m tm Gs Gt T,
typ_proc Gs Gt (incr_free 0 0 X m Q) T -> typ_proc (tm :: Gs) Gt (incr_free 0 0 X m.+1 Q) T.
Proof.
  intros.
  specialize(slideSp Q X m 0 0 tm [] Gs Gt T H); intros. simpl in H0.
  apply H0; try easy.
Qed.

Lemma subst_proc_var_helper_1 : forall llp ys (GtA : list (option ltt)) m n Q,
      SList llp ->      
      Forall2
        (fun u v : option process =>
         u = None /\ v = None \/
         (exists k l : process, u = Some k /\ v = Some l /\ substitutionP (length GtA) m n.+1 Q k l))
        llp ys -> 
      SList ys.
Proof.
  intro llp. induction llp; intros; try easy.
  inversion H0. subst. clear H0.
  destruct H3. destruct H0. subst. apply SList_b. 
  - apply IHllp with (GtA := GtA) (m := m) (n := n) (Q := Q); try easy.
  - destruct H0. destruct H0. destruct H0. destruct H1. subst.
    specialize(SList_f (Some x) llp H); intros.
    destruct H0. apply SList_b. apply IHllp with (GtA := GtA) (m := m) (n := n) (Q := Q); try easy.
    destruct H0. subst. inversion H5. subst. easy.
Qed.

Lemma subst_proc_var_recv_helper : forall llp Q Gs GtA GtB m n T ys x,
  wtyped Q ->
  typ_proc Gs (GtA ++ GtB) (incr_free 0 0 m n Q) T ->
  Forall
      (fun u : option process =>
       match u with
       | Some k =>
           forall (Q : process) (T T' : ltt) (Gs : ctxS) (GtA GtB : list (option ltt)) 
             (X : fin) (Q' : process) (m n : fin),
           wtyped Q ->
           typ_proc Gs (GtA ++ Some T :: GtB) k T' ->
           length GtA = X ->
           substitutionP X m n Q k Q' ->
           typ_proc Gs (GtA ++ GtB) (incr_free 0 0 m n Q) T -> typ_proc Gs (GtA ++ GtB) Q' T'
       | None => True
       end) llp ->
  Forall2
        (fun u v : option process =>
         u = None /\ v = None \/
         (exists k l : process, u = Some k /\ v = Some l /\ substitutionP (length GtA) m n.+1 Q k l))
        llp ys ->
  Forall2
       (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gs) (GtA ++ Some T :: GtB) p t)) llp x ->
  Forall2
  (fun (u : option process) (v : option (sort * ltt)) =>
   u = None /\ v = None \/
   (exists (p : process) (s : sort) (t : ltt),
      u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gs) (GtA ++ GtB) p t)) ys x.
Proof.
  intro llp. induction llp; intros; try easy.
  inversion H2. subst. inversion H3. subst. easy.
  inversion H2. subst. inversion H3. subst. clear H2 H3.
  constructor; try easy.
  - destruct H6. destruct H2. subst.
    left. destruct H7; try easy. destruct H2. destruct H2. destruct H2. easy.
    destruct H2. destruct H2. destruct H2. destruct H3. subst.
    destruct H7; try easy. destruct H2. destruct H2. destruct H2. destruct H2. destruct H3. inversion H2. subst.
    right. exists x0. exists x2. exists x3. split; try easy. split; try easy.
    inversion H1. subst. 
    specialize(H7 Q T x3 (Some x2 :: Gs) GtA GtB (length GtA) x0 m n.+1). 
    apply H7; try easy.
    apply slideS; try easy.
  - inversion H1. subst. clear H1 H6 H7 H4.
    apply IHllp with (Q := Q) (m := m) (n := n) (T := T); try easy.
Qed.

Lemma trivial_incrE : forall n ex, (incr_freeE n 0 ex) = ex.
Proof.
  intros n ex. induction ex; intros; try easy.
  - simpl. destruct (n <= n0); try easy.
    specialize(Nat.add_0_r n0); intros. replace (n0 + 0)%coq_nat with n0. easy.
  - simpl. replace (incr_freeE n 0 ex) with ex. easy.
  - simpl. replace (incr_freeE n 0 ex) with ex. easy.
  - simpl. replace (incr_freeE n 0 ex) with ex. easy.
  - simpl. replace (incr_freeE n 0 ex1) with ex1. replace (incr_freeE n 0 ex2) with ex2. easy.
  - simpl. replace (incr_freeE n 0 ex1) with ex1. replace (incr_freeE n 0 ex2) with ex2. easy.
  - simpl. replace (incr_freeE n 0 ex1) with ex1. replace (incr_freeE n 0 ex2) with ex2. easy.
Qed.

Lemma trivial_incr : forall m n Q, (incr_free m n 0 0 Q) = Q.
Proof.
  intros. revert m n. induction Q using process_ind_ref; intros; simpl; try easy. 
  - destruct (m <= n); try easy.
    specialize(Nat.add_0_r n); intros. replace (n + 0)%coq_nat with n; easy.
  - specialize(trivial_incrE n ex); intros.
    specialize(IHQ m n); intros.
    replace (incr_freeE n 0 ex) with ex. replace (incr_free m n 0 0 Q) with Q. easy.
  - assert (map (fun u => match u with 
        | Some u => Some (incr_free m n.+1 0 0 u)
        | None   => None
      end) llp = llp).
    {
      induction llp. easy. simpl in *.
      specialize(Forall_cons_iff (fun u : option process =>
       match u with
       | Some k => forall m n : fin, incr_free m n 0 0 k = k
       | None => True
       end) a llp); intros.
      destruct H0. specialize(H0 H); intros. clear H1 H. destruct H0.
      specialize(IHllp H0); intros.
      simpl.
      destruct a; try easy. 
      specialize(H m n.+1). replace (incr_free m n.+1 0 0 p) with p. 
      replace (map
     (fun u : option process =>
      match u with
      | Some u0 => Some (incr_free m n.+1 0 0 u0)
      | None => None
      end) llp) with llp. easy.
      replace (map
     (fun u : option process =>
      match u with
      | Some u0 => Some (incr_free m n.+1 0 0 u0)
      | None => None
      end) llp) with llp. easy.
    }
    replace (List.map (fun u : option process =>
        match u with
        | Some p' => Some (incr_free m n.+1 0 0 p')
        | None => None
        end) llp) with llp. easy.
  - specialize(trivial_incrE n e); intros. 
    specialize(IHQ1 m n); intros. specialize(IHQ2 m n); intros.
    replace (incr_freeE n 0 e) with e.
    replace (incr_free m n 0 0 Q1) with Q1. 
    replace (incr_free m n 0 0 Q2) with Q2.
    easy.
  - specialize(IHQ m.+1 n); intros. 
    replace (incr_free m.+1 n 0 0 Q) with Q. easy.
Qed.

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


Lemma expr_subst : forall v ex x d Gsl Gsr S,
        typ_expr (Gsl ++ Gsr) (incr_freeE 0 d v) S ->
        typ_expr (Gsl ++ Some S :: Gsr) ex x ->
        typ_expr (Gsl ++ Gsr) (subst_expr (length Gsl) d v ex) x.
Proof.
  intros v ex. revert v.
  induction ex; intros; try easy.
  - simpl in *.
    specialize(inv_expr_var (e_var n) n (Gsl ++ Some S :: Gsr) x H0 (erefl (e_var n))); intros.
    destruct H1. destruct H1. 
    apply sc_sub with (s := x0); try easy.
    - destruct n; try easy.
      case_eq (Nat.eqb (length Gsl) 0); intros; try easy.
      destruct Gsl; try easy. simpl in *. inversion H1. subst. easy.
    - destruct Gsl; try easy. constructor; try easy.
    destruct Gsl.
    - simpl in *. constructor; try easy.
    - simpl in *.
      case_eq (Nat.eqb n (length Gsl)); intros.
      - specialize(onth_exact Gsl Gsr (Some S)); intros.
        specialize(natb_to_prop n (length Gsl) H3); intros. subst.
        specialize(eq_trans (esym H1) H4); intros. inversion H5. subst. easy.
      case_eq (Datatypes.S n <? Datatypes.S (length Gsl))%nat; intros.
      - specialize(Nat.ltb_lt (Datatypes.S n) (Datatypes.S (length Gsl))); intros.
        destruct H5. specialize(H5 H4). clear H4 H6.
        constructor.
        apply esym. apply onth_sless with (S := S); try easy.
        specialize(PeanoNat.lt_S_n n (length Gsl) H5); intros. 
        apply coq_nat_to_nat. easy.
      - specialize(Nat.ltb_ge(Datatypes.S n) (Datatypes.S (length Gsl))); intros.
        destruct H5. specialize(H5 H4). clear H4 H6.
        constructor.
        apply onth_smore with (S := S); try easy.
        apply natb_to_propf. easy.
        Search((S ?a <= S ?b)%coq_nat).
        specialize(le_S_n (length Gsl) n H5); intros. 
        apply coq_nat_to_nat_le. easy.
  - simpl in *.
    specialize(inv_expr_vali (Gsl ++ Some S :: Gsr) (e_val v) x v H0 (erefl (e_val v))); intros.
    destruct H1.
    - destruct H1. destruct H1. subst. apply sc_vali.
    - destruct H1. destruct H1. destruct H1. subst. apply sc_sub with (s := snat); try easy. apply sc_valn.
    - destruct H1. destruct H1. subst. apply sc_valb.
  - simpl in *.
    specialize(inv_expr_succ (Gsl ++ Some S :: Gsr) (e_succ ex) x ex H0 (erefl (e_succ ex))); intros.
    destruct H1. destruct H2.
    - subst. apply sc_succ. apply IHex with (S := S); try easy.
    - subst. apply sc_sub with (s := snat); try easy. apply sc_succ. apply IHex with (S := S); try easy.
      apply sni.
  - simpl in *.
    specialize(inv_expr_neg (Gsl ++ Some S :: Gsr) (e_neg ex) x ex H0 (erefl (e_neg ex))); intros.
    destruct H1. subst. constructor. apply IHex with (S := S); try easy.
  - simpl in *.
    specialize(inv_expr_not (Gsl ++ Some S :: Gsr) (e_not ex) x ex H0 (erefl (e_not ex))); intros.
    destruct H1. subst. constructor. apply IHex with (S := S); try easy.
  - simpl in *.
    specialize(inv_expr_gt (Gsl ++ Some S :: Gsr) (e_gt ex1 ex2) x ex1 ex2 H0 (erefl (e_gt ex1 ex2))); intros.
    destruct H1. destruct H2. subst.
    constructor. apply IHex1 with (S := S); try easy. apply IHex2 with (S := S); try easy.
  - simpl in *.
    specialize(inv_expr_plus (Gsl ++ Some S :: Gsr) (e_plus ex1 ex2) x ex1 ex2 H0 (erefl (e_plus ex1 ex2))); intros.
    destruct H1. destruct H2. subst.
    constructor. apply IHex1 with (S := S); try easy. apply IHex2 with (S := S); try easy.
  - simpl in *.
    specialize(inv_expr_det (Gsl ++ Some S :: Gsr) (e_det ex1 ex2) x ex1 ex2 H0 (erefl (e_det ex1 ex2))); intros.
    destruct H1. destruct H1. destruct H2.
    apply sc_sub with (s := x0); try easy.
    constructor. apply IHex1 with (S := S); try easy. apply IHex2 with (S := S); try easy.
Qed.

Lemma SList_map_subst_expr_var {A} : forall (llp : list (option process)) v d (Gsl : list A),
  SList llp ->
  SList
  (map
     (fun x0 : option process =>
      match x0 with
      | Some y =>
          Some
            (subst_expr_proc y v (Datatypes.S (length Gsl)) (Datatypes.S d))
      | None => None
      end) llp).
Proof.
  intro llp. induction llp; intros; try easy.
  specialize(SList_f a llp H); intros. destruct H0; subst; try easy.
  apply SList_b. apply IHllp; try easy.
  destruct H0. destruct H1. subst. easy.
Qed.

Lemma slideE : forall v Gs d S x0,
               typ_expr Gs (incr_freeE 0 d v) S ->
               typ_expr (Some x0 ::Gs) (incr_freeE 0 (Datatypes.S d) v) S.
Proof.
  intro v. induction v; intros; try easy.
  - simpl in H.
    specialize(inv_expr_var (e_var (n + d)) (n + d) Gs S H (erefl (e_var (n + d)))); intros.
    destruct H0. destruct H0. apply sc_sub with (s := x); try easy.
    constructor. simpl.
    specialize(Nat.add_succ_r n d); intros.
    replace (n + d.+1)%coq_nat with ((n + d)%coq_nat.+1). simpl. easy.
  - simpl in *.
    specialize(inv_expr_vali Gs (e_val v) S v H (erefl (e_val v))); intros.
    - destruct H0. destruct H0. destruct H0. subst. apply sc_vali.
    - destruct H0. destruct H0. destruct H0. subst. apply sc_sub with (s := snat); try easy. apply sc_valn.
    - destruct H0. destruct H0. subst. apply sc_valb.
  - simpl in *.
    specialize(inv_expr_succ Gs (e_succ (incr_freeE 0 d v)) S (incr_freeE 0 d v) H (erefl (e_succ (incr_freeE 0 d v)))); intros.
    destruct H0. destruct H1. subst. constructor. apply IHv; try easy.
    subst. apply sc_sub with (s := snat). constructor. apply IHv; try easy. apply sni.
  - simpl in *.
    specialize(inv_expr_neg Gs (e_neg (incr_freeE 0 d v)) S (incr_freeE 0 d v) H (erefl (e_neg (incr_freeE 0 d v)))); intros.
    destruct H0. subst. constructor. apply IHv; try easy.
  - simpl in *.
    specialize(inv_expr_not Gs (e_not (incr_freeE 0 d v)) S (incr_freeE 0 d v) H (erefl (e_not (incr_freeE 0 d v)))); intros.
    destruct H0. subst. constructor. apply IHv; try easy.
  - simpl in *.
    specialize(inv_expr_gt Gs (e_gt (incr_freeE 0 d v1) (incr_freeE 0 d v2)) S (incr_freeE 0 d v1) (incr_freeE 0 d v2) H (erefl (e_gt (incr_freeE 0 d v1) (incr_freeE 0 d v2)))); intros.
    destruct H0. subst. constructor. apply IHv1; try easy. apply IHv2; try easy.
  - simpl in *.
    specialize(inv_expr_plus Gs (e_plus (incr_freeE 0 d v1) (incr_freeE 0 d v2)) S (incr_freeE 0 d v1) (incr_freeE 0 d v2) H (erefl (e_plus (incr_freeE 0 d v1) (incr_freeE 0 d v2)))); intros.
    destruct H0. subst. constructor. apply IHv1; try easy. apply IHv2; try easy.
  - simpl in *.
    specialize(inv_expr_det Gs (e_det (incr_freeE 0 d v1) (incr_freeE 0 d v2)) S (incr_freeE 0 d v1) (incr_freeE 0 d v2) H (erefl (e_det (incr_freeE 0 d v1) (incr_freeE 0 d v2)))); intros.
    destruct H0. destruct H0. destruct H1.
    apply sc_sub with (s := x); try easy. constructor. apply IHv1; try easy. apply IHv2; try easy.
Qed.


Lemma _subst_expr_var_helper_recv : forall llp Gsl Gsr Gt d v x S,
    typ_expr (Gsl ++ Gsr) (incr_freeE 0 d v) S ->
    Forall
      (fun u : option process =>
       match u with
       | Some k =>
           forall (v : expr) (d : fin) (Gsl Gsr : list (option sort)) (Gt : ctxT) (S : sort) (T : ltt),
           typ_proc (Gsl ++ Some S :: Gsr) Gt k T ->
           typ_expr (Gsl ++ Gsr) (incr_freeE 0 d v) S ->
           typ_proc (Gsl ++ Gsr) Gt (subst_expr_proc k v (length Gsl) d) T
       | None => True
       end) llp ->
    Forall2
       (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gsl ++ Some S :: Gsr) Gt p t)) llp x ->
    Forall2
        (fun (u : option process) (v0 : option (sort * ltt)) =>
         u = None /\ v0 = None \/
         (exists (p : process) (s : sort) (t : ltt),
            u = Some p /\ v0 = Some (s, t) /\ typ_proc (Some s :: Gsl ++ Gsr) Gt p t))
        (map
           (fun x0 : option process =>
            match x0 with
            | Some y =>
                Some
                  (subst_expr_proc y v (Datatypes.S (length Gsl)) (Datatypes.S d))
            | None => None
            end) llp) x.
Proof.
  intro llp.
  induction llp; intros; try easy.
  inversion H1; subst. easy.
  inversion H1; subst. clear H1. 
  constructor. 
  destruct a; try easy.
  - right. destruct H4; try easy. destruct H1. destruct H1. destruct H1. destruct H1. destruct H2. 
    inversion H1. subst.
    exists (subst_expr_proc x v (Datatypes.S (length Gsl)) (Datatypes.S d)).
    exists x0. exists x1. split; try easy. split; try easy. clear H1.
    inversion H0; subst. clear H0.
    specialize(H4 v (Datatypes.S d) (Some x0 :: Gsl) Gsr Gt S x1).
    apply H4; try easy.
    apply slideE; try easy.
  - left. split; try easy.
    destruct H4; try easy. destruct H1. destruct H1. destruct H1. easy.
  - apply IHllp with (S := S); try easy.
    inversion H0; subst. easy.
Qed.

Lemma _subst_expr_var_helper : forall v d P Gsl Gsr Gt S T, 
        typ_proc (Gsl ++ Some S :: Gsr) Gt P T -> 
        typ_expr (Gsl ++ Gsr) (incr_freeE 0 d v) S -> 
        typ_proc (Gsl ++ Gsr) Gt (subst_expr_proc P v (length Gsl) d) T.
Proof.
  intros v d P. revert v d.
  induction P using process_ind_ref; intros; try easy.
  - specialize(inv_proc_var (p_var n) n T (Gsl ++ Some S :: Gsr) Gt H (erefl (p_var n))); intros.
    destruct H1. destruct H1. destruct H2.
    simpl. apply tc_sub with (t := x); intros; try easy.
    constructor; try easy.
    specialize(typable_implies_wfC H); easy.
  - specialize(inv_proc_inact p_inact T (Gsl ++ Some S :: Gsr) Gt H (erefl (p_inact))); intros.
    subst. simpl. constructor.
  - simpl.
    specialize(inv_proc_send pt lb ex P (p_send pt lb ex P) (Gsl ++ Some S :: Gsr) Gt T H (erefl (p_send pt lb ex P))); intros.
    destruct H1. destruct H1. destruct H1. destruct H2. 
    apply tc_sub with (t := (ltt_send pt (extendLis lb (Some (x, x0))))); intros; try easy.
    constructor; try easy.
    apply expr_subst with (S := S); try easy.
    apply IHP with (S := S); try easy.
    specialize(typable_implies_wfC H); try easy.
  - specialize(inv_proc_recv pt llp (p_recv pt llp) (Gsl ++ Some S :: Gsr) Gt T H0 (erefl (p_recv pt llp))); intros.
    destruct H2. destruct H2. destruct H3. destruct H4.
    apply tc_sub with (t := ltt_recv pt x); intros; try easy. 
    constructor; try easy.
    apply eq_trans with (y := length llp); try easy.
    apply map_length; try easy. 
    apply SList_map_subst_expr_var; try easy.
    apply _subst_expr_var_helper_recv with (S := S); try easy.
    specialize(typable_implies_wfC H0); try easy.
  - specialize(inv_proc_ite (p_ite e P1 P2) e P1 P2 T (Gsl ++ Some S :: Gsr) Gt H (erefl (p_ite e P1 P2))); intros.
    destruct H1. destruct H1. destruct H1. destruct H2. destruct H3. destruct H4.
    specialize(typable_implies_wfC H); intros.
    constructor.
    apply expr_subst with (S := S); try easy.
    apply IHP1 with (S := S); try easy.
    apply tc_sub with (t := x); try easy.
    apply IHP2 with (S := S); try easy.
    apply tc_sub with (t := x0); try easy.
  - specialize(inv_proc_rec (p_rec P) P T (Gsl ++ Some S :: Gsr) Gt H (erefl (p_rec P))); intros.
    destruct H1. destruct H1.
    apply tc_sub with (t := x); try easy.
    simpl in *. constructor. apply IHP with (S := S); try easy.
    specialize(typable_implies_wfC H); try easy. 
Qed.
