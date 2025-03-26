From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
From SST Require Import src.header src.sim src.expr src.process src.local src.global src.balanced.

Definition ctxS := list (option sort).
Definition ctxT := list (option ltt).

Inductive typ_expr: ctxS -> expr -> sort -> Prop :=
  | sc_var : forall c s t, Some t = onth s c -> typ_expr c (e_var s) t
  | sc_vali: forall c i, typ_expr c (e_val (vint i)) sint
  | sc_valn: forall c i, typ_expr c (e_val (vnat i)) snat
  | sc_valb: forall c b, typ_expr c (e_val (vbool b)) sbool
  | sc_succ: forall c e, typ_expr c e snat ->
                         typ_expr c (e_succ e) snat
  | sc_neg : forall c e, typ_expr c e sint ->
                         typ_expr c (e_neg e) sint
  | sc_sub : forall c e s s', typ_expr c e s ->
                                 subsort s s' ->
                                 typ_expr c e s'
  | sc_not : forall c e, typ_expr c e sbool ->
                         typ_expr c (e_not e) sbool
  | sc_gt  : forall c e1 e2, typ_expr c e1 sint ->
                             typ_expr c e2 sint ->
                             typ_expr c (e_gt e1 e2) sbool
  | sc_plus: forall c e1 e2, typ_expr c e1 sint ->
                             typ_expr c e2 sint ->
                             typ_expr c (e_plus e1 e2) sint
  | sc_det  : forall c e1 e2 s, typ_expr c e1 s -> typ_expr c e2 s -> typ_expr c (e_det e1 e2) s.


(*  depth *)
Inductive typ_proc: ctxS -> ctxT -> process -> ltt -> Prop :=
  | tc_inact: forall cs ct,     typ_proc cs ct (p_inact) (ltt_end)
  | tc_var  : forall cs ct s t, Some t = onth s ct -> wfC t ->
                                typ_proc cs ct (p_var s) t
  | tc_mu   : forall cs ct p t,       typ_proc cs (Some t :: ct) p t ->
                                      typ_proc cs ct (p_rec p) t
  | tc_ite  : forall cs ct e p1 p2 T, typ_expr cs e sbool ->
                                      typ_proc cs ct p1 T ->
                                      typ_proc cs ct p2 T ->
                                      typ_proc cs ct (p_ite e p1 p2) T
  | tc_sub  : forall cs ct p t t',    typ_proc cs ct p t ->
                                      subtypeC t t' -> wfC t' ->
                                      typ_proc cs ct p t'
  | tc_recv : forall cs ct p STT P,
                     length P = length STT -> SList P ->
                     Forall2 (fun u v => (u = None /\ v = None) \/ 
                     (exists p s t, u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: cs) ct p t)) P STT ->
                     typ_proc cs ct (p_recv p P) (ltt_recv p STT)
  | tc_send : forall cs ct p l e P S T, typ_expr cs e S ->
                                        typ_proc cs ct P T ->
                                        typ_proc cs ct (p_send p l e P) (ltt_send p (extendLis l (Some (S,T)))).

Section typ_proc_ind_ref.
  Variable P : ctxS -> ctxT -> process -> ltt -> Prop.
  Hypothesis P_inact : forall cs ct, P cs ct p_inact ltt_end.
  Hypothesis P_var   : forall cs ct s t, Some t = onth s ct -> wfC t -> P cs ct (p_var s) t.
  Hypothesis P_mu    : forall cs ct p t, P cs (Some t :: ct) p t -> P cs ct (p_rec p) t.
  Hypothesis P_ite   : forall cs ct e p1 p2 T, typ_expr cs e sbool -> P cs ct p1 T -> P cs ct p2 T -> P cs ct (p_ite e p1 p2) T.
  Hypothesis P_sub   : forall cs ct p t t', P cs ct p t -> subtypeC t t' -> wfC t' -> P cs ct p t'.
  Hypothesis P_recv  : forall cs ct p STT Pr, length Pr = length STT -> SList Pr ->
                     Forall2 (fun u v => (u = None /\ v = None) \/ 
                     (exists p s t, u = Some p /\ v = Some (s, t) /\ P (Some s :: cs) ct p t)) Pr STT ->
                     P cs ct (p_recv p Pr) (ltt_recv p STT).
  Hypothesis P_send  : forall cs ct p l e Pr S T, typ_expr cs e S -> P cs ct Pr T -> P cs ct (p_send p l e Pr) (ltt_send p (extendLis l (Some (S,T)))).
  
  Fixpoint typ_proc_ind_ref (cs : ctxS) (ct : ctxT) (p : process) (T : ltt) (a : typ_proc cs ct p T) {struct a} : P cs ct p T.
  Proof.
    refine (match a with
      | tc_inact s t => P_inact s t 
      | tc_var s t s1 t1 Hsl Hwf => P_var s t s1 t1 Hsl Hwf
      | tc_mu sc tc pr t Ht => P_mu sc tc pr t (typ_proc_ind_ref sc (Some t :: tc) pr t Ht)
      | tc_ite sc tc ex p1 p2 t He Hp1 Hp2 => P_ite sc tc ex p1 p2 t He (typ_proc_ind_ref sc tc p1 t Hp1) (typ_proc_ind_ref sc tc p2 t Hp2)
      | tc_sub sc tc pr t t' Ht Hst Hwf => P_sub sc tc pr t t' (typ_proc_ind_ref sc tc pr t Ht) Hst Hwf
      | tc_recv sc st p STT Pr HST HSl Hm => P_recv sc st p STT Pr HST HSl _
      | tc_send sc tc p l ex Pr Sr Tr He HT => P_send sc tc p l ex Pr Sr Tr He (typ_proc_ind_ref sc tc Pr Tr HT)
    end); try easy.
    revert Hm.
    apply Forall2_mono. intros.
    destruct H. left. easy. destruct H. destruct H. destruct H. right. exists x0, x1, x2.
    destruct H. destruct H0. split. easy. split. easy.
    apply typ_proc_ind_ref. easy.
  Qed.

End typ_proc_ind_ref.

Fixpoint RemoveT (n : fin) (Gt : ctxT) : ctxT :=
  match Gt with 
    | x::xs =>
      match n with 
        | S m => x :: RemoveT m xs
        | 0   => None :: xs 
      end
    | [] => []
  end.

Fixpoint extendT (n : fin) (T : ltt) (Gt : ctxT) : ctxT :=
  match Gt with 
    | x::xs =>
      match n with 
        | S m => x :: extendT m T xs
        | 0   => Some T :: xs 
      end 
    | [] =>
      match n with 
        | S m => None :: extendT m T [] 
        | 0   => [Some T]
      end 
  end.

Lemma remove_var : forall X n T Gt x, X <> n -> onth n (extendT X T Gt) = Some x -> onth n Gt = Some x.
Proof.
  intros X n T Gt. revert X T Gt. induction n; intros; try easy.
  destruct X; try easy. destruct Gt. easy. simpl in H0. simpl. easy.
  destruct X. destruct Gt; try easy. simpl in H0. simpl. 
  destruct n; try easy.
  specialize(Nat.succ_inj_wd_neg X n); intros. destruct H1. 
  specialize(H1 H); intros. clear H2.
  destruct Gt. 
  - simpl in H0.
    specialize(IHn X T [] x H1 H0); intros.
    destruct n; try easy.
  - simpl in *. 
    apply IHn with (X := X) (T := T); try easy.
Qed.

Lemma extend_extract : forall n (T : ltt) Gt, onth n (extendT n T Gt) = Some T.
Proof.
  intro n. induction n.
  intros t gt. revert t. induction gt.
  - intros. easy. intros. easy.
  - destruct Gt; try easy. simpl.
    - apply IHn.
    - simpl. apply IHn.
Qed.

Lemma typable_implies_wfC_helper_p2 : forall x T',
      lttTC (l_rec x) T' ->
      wfL (l_rec x) -> 
      (forall n, exists m, guardL n m (l_rec x)) ->
      exists T, lttTC T T' /\ wfL T /\ (forall n, exists m, guardL n m T) /\ (T = l_end \/ (exists p lis, T = l_send p lis \/ T = l_recv p lis)).
Proof.
      intros.
      specialize(guard_break x H1); intros.
      destruct H2. exists x0. destruct H2.
      split.
      - clear H0 H1 H3.
        revert H. revert T'. induction H2; intros; try easy.
        inversion H. subst. 
        pinversion H0. subst. 
        specialize(subst_injL 0 0 (l_rec G) G Q y H1 H3); intros. subst.
        unfold lttTC. pfold. easy.
        apply lttT_mon.
      - apply IHmultiS; try easy.
        inversion H. subst.
        pinversion H0. subst. 
        specialize(subst_injL 0 0 (l_rec G) G Q y H1 H4); intros. subst.
        unfold lttTC. pfold. easy.
        apply lttT_mon.
      split; try easy.
      - clear H H1 H3.
        revert H0. revert T'. induction H2; intros; try easy.
        inversion H. subst.
        inversion H0. subst.
        specialize(wfL_after_subst y (l_rec G) G 0 0); intros. apply H2; try easy.
      - apply IHmultiS; try easy.
         inversion H. subst.
        inversion H0. subst.
        specialize(wfL_after_subst y (l_rec G) G 0 0); intros. apply H3; try easy.
Qed.

Lemma typable_implies_wfC_helper_recv : forall x p STT,
      lttTC x (ltt_recv p STT) ->
      wfL x -> 
      (forall n, exists m, guardL n m x) ->
      exists T, lttTC (l_recv p T) (ltt_recv p STT) /\ wfL (l_recv p T) /\ (forall n, exists m, guardL n m (l_recv p T)).
Proof.
  induction x using local_ind_ref; intros; try easy.
  - pinversion H.
    apply lttT_mon.
  - pinversion H.
    apply lttT_mon.
  - exists lis. 
    pinversion H0. subst. 
    apply lttT_mon.
  - exists lis.
    pinversion H0. subst.
    split.
    pfold. easy. easy.
    apply lttT_mon.
  - pinversion H. subst.
    
    specialize(typable_implies_wfC_helper_p2 x (ltt_recv p STT)); intros.
    unfold lttTC in H2 at 1. 
    assert (exists T : local,
       lttTC T (ltt_recv p STT) /\
       wfL T /\
       (forall n : fin, exists m : fin, guardL n m T) /\
       (T = l_end \/
        (exists
           (p : string) (lis : seq.seq (option (sort * local))),
           T = l_send p lis \/ T = l_recv p lis))).
    {
      apply H2; try easy.
      pfold. easy.
    }
    clear H2. destruct H5. destruct H2. destruct H5. destruct H6.
    pinversion H2. subst.
    - destruct H7; try easy. destruct H7. destruct H7. destruct H7. easy.
      inversion H7. subst. exists x1. unfold lttTC. split. pfold. easy. easy.
    - subst. destruct H7; try easy. destruct H7. destruct H7. destruct H7; try easy.
    apply lttT_mon.
    apply lttT_mon.
Qed.


Lemma typable_implies_wfC_helper_recv2 : forall STT Pr p,
    SList Pr ->
    Forall2
       (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt), u = Some p /\ v = Some (s, t) /\ wfC t)) Pr STT ->
    wfC (ltt_recv p STT).
Proof.
  induction STT; intros; try easy.
  - destruct Pr; try easy.
  - destruct Pr; try easy.
    inversion H0. subst.
    unfold wfC. destruct H4.
    - destruct H1. subst. 
      specialize(IHSTT Pr p H H6).
      unfold wfC in IHSTT. destruct IHSTT. destruct H1. destruct H2.
      specialize(typable_implies_wfC_helper_recv x p STT H1 H2 H3); intros.
      destruct H4. destruct H4. destruct H5. 
      exists (l_recv p (None :: x0)).
      split.
      - pinversion H4. subst.
        unfold lttTC. pfold. constructor. constructor; try easy. left. easy.
        apply lttT_mon.
      split; try easy.
      - inversion H5. subst. constructor; try easy. constructor; try easy.
        left. easy. 
        intros. specialize(H7 n). destruct H7. inversion H7. subst. exists 0. apply gl_nil.
        subst. exists x1. constructor; try easy. constructor; try easy. left. easy.
    - destruct H1. destruct H1. destruct H1. destruct H1. destruct H2. subst. clear H0.
      unfold wfC in H3. destruct H3. destruct H0. destruct H1.
      specialize(SList_f (Some x) Pr H); intros. destruct H3.
      - specialize(IHSTT Pr p H3 H6). 
        unfold wfC in IHSTT. destruct IHSTT. destruct H4. destruct H5.
        specialize(typable_implies_wfC_helper_recv x3 p STT H4 H5 H7); intros.
        destruct H8. destruct H8. destruct H9.
        exists (l_recv p (Some (x0, x2) :: x4)).
        split.
        - pfold. constructor.
          pinversion H8. subst. constructor; try easy.
          right. exists x0. exists x2. exists x1. split. easy. split. easy.
          left. easy.
          apply lttT_mon.
        split.
        - constructor; try easy.
          specialize(SList_f (Some x) Pr H); intros.
          {
            clear H4 H5 H7 H H0 H1 H2 H3 H9 H10.
            destruct H11.
            apply SList_b. pinversion H8. subst. clear H8. clear p x3 x x0 x1 x2. 
            revert H6 H1 H. revert Pr x4. induction STT; intros; try easy.
            - destruct Pr; try easy.
            - destruct Pr; try easy.
              destruct x4; try easy.
              inversion H6. subst. clear H6. inversion H1. subst. clear H1.
              specialize(SList_f o Pr H); intros. destruct H0.
              - apply SList_b. apply IHSTT with (Pr := Pr); try easy.
              - destruct H0. destruct H1. subst.
                destruct STT; try easy. destruct x4; try easy.
                destruct H4; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. inversion H0. subst.
                destruct H5; try easy. destruct H1. destruct H1. destruct H1. destruct H1. destruct H3. inversion H3. subst. easy.
                apply lttT_mon.
            - destruct H. subst. destruct STT; try easy.
              pinversion H8. subst. destruct x4; try easy.
              apply lttT_mon.
          }
        - pinversion H8. subst. constructor.
          right. exists x0. exists x2. split; try easy.
          inversion H9. subst. easy.
          apply lttT_mon.
        - clear H4 H5 H7 H H0 H1 H6 H3 H8 H9.
          clear STT x3 Pr x x1.
          intros.
          destruct n. exists 0. apply gl_nil.
          specialize(H2 n). specialize(H10 (S n)). destruct H2. destruct H10.
          exists (ssrnat.maxn x1 x). apply gl_recv.
          constructor.
          - right. exists x0. exists x2. split; try easy.
            specialize(guardL_more n x); intros. apply H1; try easy.
            specialize(ssrnat.leq_maxr x1 x); intros. easy.
          - inversion H0. subst. clear H0 H. clear p x0 x2. revert H4. revert n x x1.
            induction x4; intros; try easy.
            inversion H4. subst.
            constructor; try easy.
            destruct H1.
            - left. easy.
            - right. destruct H. destruct H. destruct H. subst. exists x0. exists x2.
              split; try easy.
              specialize(guardL_more n x1 (ssrnat.maxn x1 x) x2 H0); intros.
              apply H.
              specialize(ssrnat.leq_maxl x1 x); intros. easy.
            apply IHx4; try easy.
      - destruct H3. destruct H4. subst.
        destruct STT; try easy. inversion H4. subst.
        exists (l_recv p [Some (x0, x2)]).
        split.
        - unfold lttTC. pfold. constructor.
          constructor. right. exists x0. exists x2. exists x1.
          split. easy. split. easy.
          left. easy.
        - easy.
        split.
        - constructor. easy.
          constructor. right. exists x0. exists x2. split; try easy.
        - easy.
        - intro. 
          destruct n. exists 0. apply gl_nil.
          specialize(H2 n). destruct H2.
          exists x. apply gl_recv. constructor; try easy.
          right. exists x0. exists x2. split. easy. easy.
Qed.
  
Lemma typable_implies_wfC [P : process] [Gs : ctxS] [Gt : ctxT] [T : ltt] :
  typ_proc Gs Gt P T -> wfC T.
Proof.
  intros. induction H using typ_proc_ind_ref; try easy.
  - unfold wfC. exists l_end. split. pfold. constructor. 
    split. apply wfl_end.
    intros. exists 0. apply gl_end.
  - apply typable_implies_wfC_helper_recv2 with (Pr := Pr); try easy.
  - unfold wfC.
    inversion IHtyp_proc. 
    destruct H0. destruct H1.
    exists (l_send p (extendLis l (Some (S, x)))).
    unfold wfC in IHtyp_proc. destruct IHtyp_proc. destruct H3. destruct H4.
    split.
    - unfold lttTC. pfold. constructor.
      induction l; intros; try easy.
      simpl in *.
      - constructor; try easy.
        right. exists S. exists x. exists T. split. easy. split. easy.
        unfold lttTC in H0. left. easy.
      - simpl. constructor; try easy.
        left. easy.
    split.
    - induction l; intros; try easy.
      simpl in *.
      - constructor; try easy.
      - constructor; try easy. right. exists S. exists x. split; try easy.
      - inversion IHl. subst.
        constructor; try easy.
        constructor; try easy. left. easy.
      - intros.
        destruct n; try easy.
        - exists 0. apply gl_nil.
        - specialize(H2 n). destruct H2.
          exists x1. apply gl_send; try easy.
          induction l; intros; try easy.
          - simpl in *. constructor; try easy.
            right. exists S. exists x. split; try easy.
          - simpl. constructor; try easy. left. easy.
Qed.

Lemma typable_implies_wtyped_helper : forall Pr STT,
  Forall2
       (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt), u = Some p /\ v = Some (s, t) /\ wtyped p)) Pr STT ->
  Forall (fun u : option process => u = None \/ (exists k : process, u = Some k /\ wtyped k)) Pr.
Proof.
  intro Pr. induction Pr; intros; try easy.
  destruct STT; try easy.
  specialize(Forall2_cons_iff (fun (u : option process) (v : option (sort * ltt)) =>
       u = None /\ v = None \/
       (exists (p : process) (s : sort) (t : ltt), u = Some p /\ v = Some (s, t) /\ wtyped p)) a o Pr STT); intros.
  destruct H0. specialize(H0 H). clear H H1. destruct H0.
  apply Forall_cons; try easy.
  destruct H.
  - destruct H. subst. left. easy.
  - destruct H. destruct H. destruct H. destruct H. destruct H1. subst.
    right. exists x. easy.
  apply IHPr with (STT := STT); try easy.
Qed.

Lemma typable_implies_wtyped [Gs : ctxS] [Gt : ctxT] [P : process] [T : ltt] : typ_proc Gs Gt P T -> wtyped P.
Proof.
  intros. induction H using typ_proc_ind_ref.
  apply wp_inact.
  apply wp_var.
  apply wp_rec. easy.
  apply wp_ite; try easy. easy.
  apply wp_recv; try easy. 
  - apply typable_implies_wtyped_helper with (STT := STT); try easy.
  apply wp_send. easy.
Qed.