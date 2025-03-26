From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
From SST Require Import src.header src.sim src.expr src.process src.local src.global src.balanced src.typecheck src.part src.gttreeh src.step.

Inductive isMerge : ltt -> list (option ltt) -> Prop :=
  | matm : forall t, isMerge t (Some t :: nil)
  | mconsn : forall t xs, isMerge t xs -> isMerge t (None :: xs) 
  | mconss : forall t xs, isMerge t xs -> isMerge t (Some t :: xs). 

Lemma merge_end_back : forall n ys0 t,
    onth n ys0 = Some ltt_end -> 
    isMerge t ys0 -> 
    t = ltt_end.
Proof.
  induction n; intros; try easy.
  - destruct ys0; try easy. 
    simpl in H. subst. inversion H0. subst. easy. easy.
  - destruct ys0; try easy.
    inversion H0. subst. 
    - destruct n; try easy.
    - subst. specialize(IHn ys0 t). apply IHn; try easy.
    - subst. specialize(IHn ys0 t). apply IHn; try easy.
Qed.

Lemma merge_end_s : forall x T,
    Forall (fun u : option ltt => u = None \/ u = Some ltt_end) x -> 
    isMerge T x -> T = ltt_end.
Proof.
  induction x; intros; try easy.
  - inversion H. subst.
    inversion H0. subst. destruct H3; try easy. inversion H1; try easy.
    subst. specialize(IHx T). apply IHx; try easy.
    subst. specialize(IHx T). apply IHx; try easy.
Qed.

Lemma isMerge_injw : forall t t' r ys0 ys1,
    Forall2
       (fun u v : option ltt =>
        u = None /\ v = None \/
        (exists t t' : ltt, u = Some t /\ v = Some t' /\ paco2 lttIso r t t')) ys0 ys1 ->
    isMerge t ys0 -> isMerge t' ys1 -> paco2 lttIso r t t'.
Proof.
  intros t t' r ys0. revert t t' r.
  induction ys0; intros; try easy. destruct ys1; try easy.
  inversion H. subst. clear H.
  specialize(IHys0 t t' r ys1 H7).
  inversion H0. subst. inversion H1. subst.
  - destruct H5; try easy. destruct H as (t1,(t2,(Ha,(Hb,Hc)))). inversion Ha. inversion Hb. subst. easy.
  - subst. destruct H5; try easy.
    destruct H as (t1,(t2,(Ha,(Hb,Hc)))). easy.
  - subst. destruct H5; try easy. destruct H as (t1,(t2,(Ha,(Hb,Hc)))). inversion Ha. inversion Hb. subst. easy.
  - subst. inversion H1; try easy. subst. destruct H5; try easy.
    destruct H as (t1,(t2,(Ha,(Hb,Hc)))). easy.
  - subst. apply IHys0; try easy.
  - subst. destruct H5; try easy. destruct H as (t1,(t2,(Ha,(Hb,Hc)))). easy.
  - subst. destruct H5; try easy. destruct H as (t1,(t2,(Ha,(Hb,Hc)))). inversion Ha. subst. 
    inversion H1. subst. easy. subst. easy.
Qed.

Lemma canon_rep_part_helper_recv : forall n ys1 x4 p ys,
    onth n ys1 = Some x4 ->
    isMerge (ltt_recv p ys) ys1 -> 
    exists ys1', x4 = ltt_recv p ys1'.
Proof. 
  induction n; intros; try easy.
  - destruct ys1; try easy. simpl in *. subst. 
    inversion H0. subst. exists ys. easy.
    subst. exists ys. easy.
  - destruct ys1; try easy.
    specialize(IHn ys1 x4 p ys). apply IHn; try easy.
    inversion H0; try easy. subst. destruct n; try easy.
Qed.

Lemma canon_rep_part_helper_send : forall n ys2 x3 q x,
    onth n ys2 = Some x3 ->
    isMerge (ltt_send q x) ys2 ->
    exists ys2', x3 = ltt_send q ys2'.
Proof. intro n.
       induction n; intros.
       - inversion H0. subst. simpl in H. inversion H. subst.
         exists x. easy.
         subst. simpl in H. easy.
         subst. simpl in H. inversion H. subst.
       - exists x. easy.
       - destruct ys2; try easy.
         inversion H0. subst. destruct n; try easy.
         subst.
         specialize(IHn ys2 x3 q x). apply IHn; try easy.
         subst.
         specialize(IHn ys2 x3 q x). apply IHn; try easy.
Qed.

Lemma triv_merge : forall T T', isMerge T (Some T' :: nil) -> T = T'.
Proof. intros.
       inversion H. subst. easy. subst.
       easy.
Qed.

Lemma triv_merge2 : forall T xs, isMerge T xs -> isMerge T (None :: xs).
Proof. intros.
       inversion H. subst.
       constructor. easy.
       subst. constructor. easy.
       subst. constructor. easy.
Qed. 

Lemma triv_merge3 : forall T xs, isMerge T xs -> isMerge T (Some T :: xs).
Proof. intros.
       apply mconss with (t := T); try easy.
Qed.

Lemma merge_inv : forall T a xs, isMerge T (a :: xs) -> a = None \/ a = Some T.
Proof.
  intros. inversion H; subst; try easy. right. easy. left. easy. right. easy.
Qed.

Lemma merge_onth_recv : forall n p LQ ys1 gqT,
      isMerge (ltt_recv p LQ) ys1 ->
      onth n ys1 = Some gqT -> 
      exists LQ', gqT = ltt_recv p LQ'.
Proof. intros. eapply canon_rep_part_helper_recv. eauto. eauto. Qed.

Lemma merge_onth_send : forall n q LP ys0 gpT,
      isMerge (ltt_send q LP) ys0 ->
      onth n ys0 = Some gpT ->
      exists LP', gpT = (ltt_send q LP').
Proof. intros. eapply canon_rep_part_helper_send. eauto. eauto. Qed.

Lemma triv_merge_ltt_end : forall ys0,
    isMerge ltt_end ys0 -> List.Forall (fun u => u = None \/ u = Some ltt_end) ys0.
Proof.
  induction ys0; intros; try easy.
  inversion H.
  - subst. constructor; try easy. right. easy.
  - subst. specialize(IHys0 H2). constructor; try easy. left. easy.
  - subst. constructor; try easy. right. easy. 
    apply IHys0; try easy.
Qed.

Lemma merge_label_recv : forall Mp LQ' LQ0' T k l p,
          isMerge (ltt_recv p LQ') Mp ->
          onth k Mp = Some (ltt_recv p LQ0') ->
          onth l LQ0' = Some T ->
          exists T', onth l LQ' = Some T'.
Proof. intros Mp.
  induction Mp; intros; try easy.
  - inversion H. subst. 
    destruct k; try easy. simpl in H0. inversion H0. subst. exists T. easy.
  - simpl in H0. destruct k; try easy.
  - subst. destruct k; try easy.
    specialize(IHMp LQ' LQ0' T k l p). apply IHMp; try easy.
  - subst. destruct k; try easy. simpl in H0. inversion H0. subst. exists T. easy.
  - specialize(IHMp LQ' LQ0' T k l p). apply IHMp; try easy.
Qed.

Lemma merge_label_send : forall Mq LP' LP0' T k l q,
          isMerge (ltt_send q LP') Mq ->
          onth k Mq = Some (ltt_send q LP0') ->
          onth l LP0' = Some T ->
          exists T', onth l LP' = Some T'. 
Proof. intro Mq.
  induction Mq; intros; try easy.
  - inversion H. subst. 
    destruct k; try easy. simpl in H0. inversion H0. subst. exists T. easy.
  - simpl in H0. destruct k; try easy.
  - subst. destruct k; try easy.
    specialize(IHMq LP' LP0' T k l q). apply IHMq; try easy.
  - subst. destruct k; try easy. simpl in H0. inversion H0. subst. exists T. easy.
  - specialize(IHMq LP' LP0' T k l q). apply IHMq; try easy.
Qed.

Lemma merge_send_T : forall n T ys q lp,
        isMerge T ys -> 
        onth n ys = Some (ltt_send q lp) -> 
        exists lp', T = ltt_send q lp'.
Proof.
  induction n; intros; try easy.
  destruct ys; try easy. simpl in H0. subst.
  - inversion H. subst. exists lp. easy. 
  - subst. exists lp. easy.
  destruct ys; try easy. specialize(IHn T ys q lp).
  inversion H.
  - subst. destruct n; try easy.
  - subst. apply IHn; try easy.
  - subst. apply IHn; try easy.
Qed.

Lemma merge_recv_T : forall n T ys q lp,
        isMerge T ys -> 
        onth n ys = Some (ltt_recv q lp) -> 
        exists lp', T = ltt_recv q lp'.
Proof.
  induction n; intros; try easy.
  destruct ys; try easy. simpl in H0. subst.
  - inversion H. subst. exists lp. easy. 
  - subst. exists lp. easy.
  destruct ys; try easy. specialize(IHn T ys q lp).
  inversion H.
  - subst. destruct n; try easy.
  - subst. apply IHn; try easy.
  - subst. apply IHn; try easy.
Qed.
  
Lemma merge_label_sendb : forall ys0 LP LP' ST n l q,
      isMerge (ltt_send q LP) ys0 ->
      onth n ys0 = Some (ltt_send q LP') ->
      onth l LP = Some ST ->
      onth l LP' = Some ST.
Proof. intro ys0.
  induction ys0; intros; try easy.
  - destruct n; try easy. 
    - simpl in *. subst. 
      inversion H. subst.
      - easy.
      - subst. easy.
    - inversion H. subst.
      destruct n; try easy.
      subst. specialize(IHys0 LP LP' ST n l q). apply IHys0; try easy.
      subst. specialize(IHys0 LP LP' ST n l q). apply IHys0; try easy.
Qed.

Lemma merge_constr : forall p LQ ys1 n,
          isMerge (ltt_recv p LQ) ys1 ->
          onth n ys1 = Some ltt_end ->
          False.
Proof. intros p LQ ys1 n.
  revert ys1. induction n; intros; try easy.
  - destruct ys1; try easy. simpl in H0. subst. inversion H; try easy.
  - destruct ys1; try easy. 
    inversion H. subst. destruct n; try easy.
    - subst. specialize(IHn ys1). apply IHn; try easy.
    - subst. specialize(IHn ys1). apply IHn; try easy.
Qed.

Lemma merge_consts : forall q LP ys0 n,
          isMerge (ltt_send q LP) ys0 -> 
          onth n ys0 = Some ltt_end -> 
          False.
Proof. intros q LP ys0 n.
  revert ys0. induction n; intros; try easy.
  - destruct ys0; try easy. simpl in H0. subst. inversion H; try easy.
  - destruct ys0; try easy. 
    inversion H. subst. destruct n; try easy.
    - subst. specialize(IHn ys0). apply IHn; try easy.
    - subst. specialize(IHn ys0). apply IHn; try easy.
Qed.

Lemma merge_slist : forall T ys, isMerge T ys -> SList ys.
Proof. intros.
       induction H; intros.
       simpl. easy.
       simpl. easy.
       simpl. destruct xs.
       easy. easy.
Qed.

Lemma merge_label_recv_s : forall Mp LQ' LQ0' T k l p,
          isMerge (ltt_recv p LQ') Mp ->
          onth k Mp = Some (ltt_recv p LQ0') ->
          onth l LQ0' = Some T ->
          onth l LQ' = Some T.
Proof.
  induction Mp; intros; try easy.
  - destruct k; try easy. simpl in H0. subst.
    - inversion H. subst. easy. subst. easy.
    - inversion H. subst. destruct k; try easy.
      subst. specialize(IHMp LQ' LQ0' T k l p). apply IHMp; try easy.
      subst. specialize(IHMp LQ' LQ0' T k l p). apply IHMp; try easy.
Qed.

Lemma merge_label_send_s : forall Mq LP' LP0' T k l q,
          isMerge (ltt_send q LP') Mq ->
          onth k Mq = Some (ltt_send q LP0') ->
          onth l LP0' = Some T ->
          onth l LP' = Some T. 
Proof.
  induction Mq; intros; try easy.
  - destruct k; try easy. simpl in H0. subst.
    - inversion H. subst. easy. subst. easy.
    - inversion H. subst. destruct k; try easy.
      subst. specialize(IHMq LP' LP0' T k l q). apply IHMq; try easy.
      subst. specialize(IHMq LP' LP0' T k l q). apply IHMq; try easy.
Qed.

Lemma merge_sorts : forall ys0 ys1 p q PT QT,
    Forall2
      (fun u v : option ltt =>
       u = None /\ v = None \/
       (exists lis1 lis2 : seq.seq (option (sort * ltt)),
          u = Some (ltt_recv p lis1) /\
          v = Some (ltt_send q lis2) /\
          Forall2
            (fun u0 v0 : option (sort * ltt) =>
             u0 = None /\ v0 = None \/
             (exists (s : sort) (t t' : ltt), u0 = Some (s, t) /\ v0 = Some (s, t'))) lis2 lis1)) ys0 ys1 -> 
    isMerge (ltt_recv p QT) ys0 -> 
    isMerge (ltt_send q PT) ys1 -> 
    Forall2
      (fun u v : option (sort * ltt) =>
       u = None /\ v = None \/ (exists (s : sort) (g g' : ltt), u = Some (s, g) /\ v = Some (s, g'))) PT QT.
Proof.
  induction ys0; intros; try easy.
  destruct ys1; try easy. inversion H. subst. clear H.
  specialize(merge_inv (ltt_recv p QT) a ys0 H0); intros.
  specialize(merge_inv (ltt_send q PT) o ys1 H1); intros.
  
  destruct H.
  - subst. inversion H0. subst. 
    destruct H2. subst. inversion H1. subst.
    specialize(IHys0 ys1 p q PT QT). apply IHys0; try easy.
    subst. destruct H5; try easy. destruct H as (l1,(l2,(Ha,Hb))). easy.
  - subst.
    destruct H2. subst. destruct H5; try easy.
    destruct H as (l1,(l2,(Ha,Hb))). easy.
    subst. destruct H5; try easy.
    destruct H as (l1,(l2,(Ha,(Hb,Hc)))). inversion Ha. subst. inversion Hb. subst.
    easy.
Qed.
 
Lemma merge_inv_ss : forall n T ys1 t1,
        isMerge T ys1 -> 
        onth n ys1 = Some t1 -> 
        t1 = T.
Proof.
  induction n; intros.
  - destruct ys1; try easy. simpl in H0. subst.
    inversion H; try easy.
  - destruct ys1; try easy.
    specialize(IHn T ys1 t1).
    inversion H; try easy.
    - subst. destruct n; try easy.
    - subst. apply IHn; try easy.
    - subst. apply IHn; try easy.
Qed.