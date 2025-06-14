(* From mathcomp Require Import ssreflect.seq all_ssreflect. *)
From Paco Require Import paco pacotac.
From SST Require Import src.expr src.header src.local CpdtTactics.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations Setoid.
Require Import Coq.Program.Equality.
Import ListNotations.

Notation opt_lbl := nat.
Inductive label: Type :=
  | lrecv: part -> part -> option sort -> opt_lbl -> label
  | lsend: part -> part -> option sort -> opt_lbl -> label
  | lcomm: part -> part -> opt_lbl -> label.

Definition ispSubjl r l :=
  match l with 
  | lsend p q _ _ => p=r
  | lrecv p q _ _=> p=r
  | lcomm p q _ => p=r \/ q=r 
  end. 

From MMaps Require Import MMaps.

Module M := MMaps.RBT.Make(Nat).
Module MF := MMaps.Facts.Properties Nat M.

Definition tctx: Type := M.t ltt.

Definition both (z: nat) (o:option ltt) (o':option ltt) :=
 match o,o' with 
   | Some _, None   => o
   | None, Some _   => o'
   | _,_            => None
 end.

Definition disj_merge (g1 g2:tctx) (H:MF.Disjoint g1 g2) : tctx := 
  M.merge both g1 g2.  


Inductive tctxR: tctx -> label -> tctx -> Prop :=
  | Rsend: forall p q xs n s T,
            p <> q ->
            onth n xs = Some (s, T) ->
            tctxR (M.add p (ltt_send q xs) M.empty) (lsend p q (Some s) n) (M.add p T M.empty)
  | Rrecv: forall p q xs n s T,
            p <> q ->
            onth n xs = Some (s, T) ->
            tctxR (M.add p (ltt_recv q xs) M.empty) (lrecv p q (Some s) n) (M.add p T M.empty)
  | Rcomm: forall p q g1 g1' g2 g2' s s' n (H1: MF.Disjoint g1 g2) (H2: MF.Disjoint g1' g2'), 
            p <> q ->
            tctxR g1 (lsend p q (Some s) n) g1'  ->
            tctxR g2 (lrecv q p (Some s') n) g2' ->
            subsort s s' ->
            tctxR (disj_merge g1 g2 H1) (lcomm p q n) (disj_merge g1' g2' H2)
  | RvarI: forall g l g' p T,
            tctxR g l g' ->
            M.mem p g = false ->
            tctxR (M.add p T g) l (M.add p T g')
  | Rstruct: forall g1 g1' g2 g2' l,
    tctxR g1' l g2' ->
    M.Equal g1 g1' ->
    M.Equal g2 g2' ->
    tctxR g1 l g2.



Definition tctxRE l c := exists c', tctxR c l c'.

Definition tctxRF l c c' := tctxR c l c'.

Lemma opt_lem1 : forall A (x:option A), x <> None -> exists y, x=Some y.
Proof.
  intros; destruct x; try easy. exists a. reflexivity.  
Qed.

Lemma opt_lem2 : forall A (x:option A) (y:A), x=Some y -> x<> None.
Proof.
  intros; destruct x; try easy.  
Qed.


Create HintDb mmaps. 
Hint Rewrite ( @M.add_spec1 ) ( @M.add_spec2) ( @M.remove_spec1)
    ( @M.remove_spec2) ( @M.empty_spec) using easy : mmaps.
(*superseded by spc_merge_find*)
Lemma spc_merge_spec1: forall (g g': tctx) x (Hdisj: MF.Disjoint g g'),  M.In x g\/ M.In x g' -> (M.In x (disj_merge g g' Hdisj)).
Proof.
  intros.
  destruct H.
  {
    specialize (M.merge_spec1 both (@or_introl (M.In x g) (M.In x g') H)) as H_spc.
    
    destruct H_spc. destruct H0. subst.
    apply MF.in_find.
    unfold disj_merge.
    (*prove: both x (M.find x g) (M.find x g') <>=None*)
    assert(Hres:both x (M.find x g) (M.find x g') <> None).
    {
      apply MF.in_find in H.
      unfold MF.Disjoint in Hdisj.
      specialize (Hdisj x).
      apply MF.in_find in H.
      destruct (M.find x g') eqn:H'.
      {
        assert(M.find x g' <> None). {
          apply opt_lem2 with (y:=l).  assumption.
        }
        apply MF.in_find in H0. exfalso.
        apply Hdisj. easy.
      }
      {
        apply MF.in_find in H.
        apply opt_lem1 in H. destruct H. unfold both. rewrite H. easy.
      }
    } 
    apply opt_lem1 in Hres.
    destruct Hres. rewrite H0 in H1. rewrite H1. easy.
  }
  {
    specialize (M.merge_spec1 both (@or_intror (M.In x g) (M.In x g') H)) as H_spc.
    destruct H_spc. destruct H0. subst.
    Check MF.in_find.
    apply MF.in_find.
    unfold disj_merge.
    (*prove: both x (M.find x g) (M.find x g') <>=None*)
    assert(Hres:both x (M.find x g) (M.find x g') <> None).
    {
      apply MF.in_find in H.
      unfold MF.Disjoint in Hdisj.
      specialize (Hdisj x).
      apply MF.in_find in H.
      destruct (M.find x g) eqn:H'.
      {
        assert(M.find x g <> None). {
          apply opt_lem2 with (y:=l).  assumption.
        }
        apply MF.in_find in H0. exfalso.
        apply Hdisj. easy.
      }
      {
        apply MF.in_find in H.
        apply opt_lem1 in H. destruct H. unfold both. rewrite H. easy.
      }
    } 
    apply opt_lem1 in Hres.
    destruct Hres. rewrite H0 in H1. rewrite H1. easy.
  }
Qed.

Lemma spc_merge_find1: forall (g1 g2:tctx) p H_disj x, M.find p g1 = Some x ->
  M.find p (disj_merge g1 g2 H_disj)=Some x.
Proof.
  intros.
  Search M.merge M.find.
  unfold disj_merge.
  rewrite MF.merge_spec1mn; try easy.
  unfold MF.Disjoint in H_disj.
  specialize (H_disj p).
  destruct (M.find p g2) eqn:H_2. 2: {rewrite H. simpl. reflexivity. }
  apply opt_lem2 in H.
  apply opt_lem2 in H_2.
  apply MF.in_find in H.
  apply MF.in_find in H_2. exfalso. exact (H_disj (conj H H_2)). 
Qed.

Lemma spc_merge_find2: forall (g1 g2:tctx) p H_disj x, M.find p g2 = Some x ->
  M.find p (disj_merge g1 g2 H_disj)=Some x.
Proof.
  intros.
  Search M.merge M.find.
  unfold disj_merge.
  rewrite MF.merge_spec1mn; try easy.
  unfold MF.Disjoint in H_disj.
  specialize (H_disj p).
  destruct (M.find p g1) eqn:H_2. 2: {rewrite H. simpl. reflexivity. }
  apply opt_lem2 in H.
  apply opt_lem2 in H_2.
  apply MF.in_find in H.
  apply MF.in_find in H_2. exfalso. exact (H_disj (conj H_2 H)). 
Qed.

Lemma spc_merge_find3 : forall (g1 g2:tctx) p H_disj x, 
  M.find p (disj_merge g1 g2 H_disj)=Some x ->
  (M.find p g1=Some x /\ M.find p g2=None) \/ 
  (M.find p g2=Some x /\ M.find p g1=None).
Proof.
  intros.
  Search M.merge M.find.
  unfold disj_merge in H.
  rewrite  MF.merge_spec1mn in H; destruct (M.find p g1);
  destruct (M.find p g2); crush.
Qed.

Lemma spc_merge_nfind : forall g1 g2 H p, M.find p (disj_merge g1 g2 H) = None ->
  M.find p g1=None /\ M.find p g2=None.
Proof.
  intros.  unfold disj_merge in H0. split;
  rewrite MF.merge_spec1mn in H0; crush;
  destruct (M.find p g1) eqn:H_pg1;destruct (M.find p g2) eqn:H_pg2; unfold both in *; try easy;
  unfold MF.Disjoint in H; apply opt_lem2 in H_pg1; apply MF.in_find in H_pg1;
  apply opt_lem2 in H_pg2; apply MF.in_find in H_pg2; specialize (H p); crush. 
Qed.

Lemma empty_disjoint : forall (g:tctx), MF.Disjoint g M.empty.
Proof.
  intros.
  unfold MF.Disjoint. unfold not. intros.
  destruct H. 
  Search M.In M.empty.
  apply MF.empty_in_iff in H0. assumption.
Qed.

Lemma spc_merge_nfind2 : forall g1 g2 H p,
  M.find p g1=None /\ M.find p g2=None-> M.find p (disj_merge g1 g2 H) = None.
Proof.
  intros.  unfold disj_merge in H0. destruct H0. unfold disj_merge. 
  rewrite MF.merge_spec1mn;crush.
Qed.


Lemma double_find_disjoint : forall (g1 g2 :tctx) y a1 a2, MF.Disjoint g1 g2 -> 
  M.find y g1 = Some a1 
  -> M.find y g2 = Some a2
  -> False.
Proof.
  intros;
  unfold MF.Disjoint in H;
  apply opt_lem2 in H0;
  apply opt_lem2 in H1;
  specialize (H y); apply MF.in_find in H0,H1; crush.
Qed.

Ltac tac_double_find_disjoint := match goal 
    with | 
    [ H1: M.find ?y ?g1 = Some _,
    H2: M.find ?y ?g2 = Some _,
    H3: MF.Disjoint ?g1 ?g2 
    |- _] => exfalso;apply (double_find_disjoint g1 g2 y _ _ H3 H1 H2) end.

Lemma disj_merge_sym : forall g1 g2 H, M.Equal (disj_merge g1 g2 H) (disj_merge g2 g1 (MF.Disjoint_sym H)). 
Proof.
  unfold M.Equal. intros.
  destruct (M.find y g1) eqn:H_yg1;destruct(M.find y g2) eqn:H_yg2;
  destruct(M.find y (disj_merge g1 g2 H)) eqn:H_yg3; 
  (try tac_double_find_disjoint); apply eq_sym; 
  try apply spc_merge_find3 in H_yg3;
  try apply spc_merge_nfind in H_yg3; crush;[
  apply spc_merge_find2;crush| apply spc_merge_find1;crush|
  apply spc_merge_nfind2;crush].
Qed.

Lemma disj_merge_unitr: forall (g:tctx), M.Equal g (disj_merge g M.empty (empty_disjoint g)).
Proof.
  intros. unfold M.Equal. intros. unfold disj_merge.
  Check MF.merge_spec1mn.
  rewrite MF.merge_spec1mn.
  unfold M.find at 3.
  simpl. unfold both. 
  destruct (M.find y g);reflexivity.
  Check Proper.
  unfold Proper.
  unfold "==>".
  intros. subst. reflexivity. intros. unfold both. simpl. reflexivity. 
Qed.

Lemma disj_merge_unitl: forall (g:tctx), M.Equal g (disj_merge  M.empty g (MF.Disjoint_sym (empty_disjoint g))).
Proof.
  intros. assert(M.Equal (disj_merge g M.empty (empty_disjoint g)) (disj_merge  M.empty g (MF.Disjoint_sym (empty_disjoint g)))).
  {
   apply disj_merge_sym. 
  }
  specialize (disj_merge_unitr g). intros. crush.  
Qed.

Lemma dom_preservation_6_9: forall g l g', tctxR g l g' -> M.Eqdom g g'.
Proof.
  intros.
  split.
  {
    induction H.
    {
      intros.
      apply MF.add_in_iff in H1.
      destruct H1.
      {
        subst.
        apply MF.add_in_iff. left. reflexivity.
      }
      {
        apply MF.empty_in_iff in H1. easy.
      }
    }
    {

      intros.
      apply MF.add_in_iff in H1.
      destruct H1.
      {
        subst.
        apply MF.add_in_iff. left. reflexivity.
      }
      {
        apply MF.empty_in_iff in H1. easy.
      }
    }
    {
      intros.
      apply M.merge_spec2 in H5.
      destruct H5.
      {
        apply  IHtctxR1 in H5.
        apply spc_merge_spec1.
        left. easy.
      }
      {
        apply  IHtctxR2 in H5.
        apply spc_merge_spec1.
        right. easy.
      }
    }
    {
      intros.
      rewrite MF.add_in_iff in H1.
      rewrite MF.add_in_iff.
      destruct H1.
      {
        left. easy.
      }
      {
        right. apply  IHtctxR. easy.
      }
    }
    {
      intros.
      unfold M.Equal in H0.
      specialize (H0 y).
      destruct(M.find y g1) eqn:H_mfind.
      {
        apply eq_sym in H0.
        apply (opt_lem2 _ (M.find y g1') _) in H0.
        apply MF.in_find in H0.
        apply IHtctxR in H0.
        unfold M.equal in H1.
        specialize (H1 y).
        apply MF.in_find in H0.
        apply opt_lem1 in H0.
        destruct H0.
        rewrite H0 in H1.
        apply opt_lem2 in H1.
        apply MF.in_find in H1.
        assumption.
      }
      {
        apply MF.not_in_find in H_mfind.
        exfalso. apply H_mfind in H2. assumption.
      }
    }
  }
  {
    induction H.
    {
      intros.
      apply MF.add_in_iff in H1.
      destruct H1.
      {
        subst.
        apply MF.add_in_iff. left. reflexivity.
      }
      {
        apply MF.empty_in_iff in H1. easy.
      }
    }
    {

      intros.
      apply MF.add_in_iff in H1.
      destruct H1.
      {
        subst.
        apply MF.add_in_iff. left. reflexivity.
      }
      {
        apply MF.empty_in_iff in H1. easy.
      }
    }
    {
      intros.
      apply M.merge_spec2 in H5.
      destruct H5.
      {
        apply  IHtctxR1 in H5.
        apply spc_merge_spec1.
        left. easy.
      }
      {
        apply  IHtctxR2 in H5.
        apply spc_merge_spec1.
        right. easy.
      }
    }
    {
      intros.
      rewrite MF.add_in_iff in H1.
      rewrite MF.add_in_iff.
      destruct H1.
      {
        left. easy.
      }
      {
        right. apply  IHtctxR. easy.
      }
    }
    {
      intros.
      unfold M.Equal in H1.
      specialize (H1 y).
      destruct(M.find y g2) eqn:H_mfind.
      {
        apply eq_sym in H1.
        apply (opt_lem2 _ (M.find y g2') _) in H1.
        apply MF.in_find in H1.
        apply IHtctxR in H1.
        specialize (H0 y).
        apply MF.in_find in H1.
        apply opt_lem1 in H1.
        destruct H1.
        rewrite H1 in H0.
        apply opt_lem2 in H0.
        apply MF.in_find in H0.
        assumption.
      }
      {
        apply MF.not_in_find in H_mfind.
        exfalso. apply H_mfind in H2. assumption.
      }
    }
  }
Qed. 

Ltac red_inv_destruct H := 
  destruct H as [H_comm  H'']; destruct H'' as [H_rec H_send].

Lemma lem_6_11a_tctx_send_invert : forall g g' p q s ell, 
  (tctxR g (lsend p q (Some s) ell) g' ->
  exists xs Tp', M.find p g = Some (ltt_send q xs) /\ 
  onth ell xs=Some (s, Tp') /\ M.find p g' = (Some Tp'))
  .
Proof.
  intros.
  dependent induction H; 
  [exists xs; exists T; do 2 rewrite M.add_spec1; crush| |];
  specialize (IHtctxR p q s ell (eq_refl (lsend p q (Some s) ell)));
  destruct IHtctxR; (match goal with | [ Hex: exists _, _ |- _] => destruct Hex end);
  exists x; exists x0.
  destruct H1. destruct H2.
  rewrite MF.not_mem_find in H0.
  destruct (Nat.eq_dec p p0);subst. crush.
  try rewrite M.add_spec2;
  try rewrite M.add_spec2; crush.
  destruct H2.
  destruct H3.
  unfold M.Equal in *. crush.
Qed.

Lemma lem_6_11b_tctx_recv_invert : forall g g' p q s ell, 
  (tctxR g (lrecv p q (Some s) ell) g' ->
  exists xs Tp', M.find p g = Some (ltt_recv q xs) /\ 
  onth ell xs=Some (s, Tp') /\ M.find p g' = (Some Tp')).
Proof.
  intros.
  dependent induction H; 
  [exists xs; exists T; do 2 rewrite M.add_spec1; crush| |];
  specialize (IHtctxR p q s ell (eq_refl (lrecv p q (Some s) ell)));
  destruct IHtctxR; (match goal with | [ Hex: exists _, _ |- _] => destruct Hex end);
  exists x; exists x0.
  destruct H1. destruct H2.
  rewrite MF.not_mem_find in H0.
  destruct (Nat.eq_dec p p0);subst. crush.
  try rewrite M.add_spec2;
  try rewrite M.add_spec2; crush.
  destruct H2.
  destruct H3.
  unfold M.Equal in *. crush.
Qed.

Ltac destr_hyps := repeat (match goal with 
          | [ H: exists _,_|- _] => destruct H 
          | [H: _ /\ _ |-_] => destruct H
          end).


Lemma lem_6_11c_tctx_comm_invert: forall g g' p q ell, 
  tctxR g (lcomm p q ell) g' ->exists s s',
  (exists xsp Tp', M.find p g = Some (ltt_send q xsp) /\ 
  onth ell xsp=Some (s, Tp') /\ M.find p g' = (Some Tp')) /\
  ( exists xsq Tq', M.find q g = Some (ltt_recv p xsq) /\ 
  onth ell xsq=Some (s', Tq') /\ M.find q g' = (Some Tq'))
  /\ subsort s s'.
Proof.
  intros.
  dependent induction H.
  {
    apply lem_6_11a_tctx_send_invert in H0.
    apply lem_6_11b_tctx_recv_invert in H3.
    destr_hyps.
    exists s, s'.
    split.
    exists x1. exists x2.
    apply spc_merge_find1  with (g2:= g2) (H_disj:=H1) in H0.
    apply spc_merge_find1  with (g2:= g2') (H_disj:=H2) in H8. crush.
    split.
    exists x, x0.
    apply spc_merge_find2  with (g1:= g1) (H_disj:=H1) in H3.
    apply spc_merge_find2  with (g1:= g1') (H_disj:=H2) in H6. crush.
    easy.
  }
  {
   specialize (IHtctxR p q ell (eq_refl (lcomm p q ell))).
   destruct (Nat.eq_dec p p0);
   destr_hyps;subst; rewrite MF.not_mem_find in H0; crush. 
   rewrite M.add_spec2.
   exists x,x0.
   split. exists x1. exists x2. rewrite M.add_spec2. crush. easy.
   
   destruct (Nat.eq_dec q p0);subst; crush.
   exists x3. exists x4. rewrite M.add_spec2. rewrite M.add_spec2. crush. 
   unfold "<>". intros. crush. unfold "<>". intros. crush. unfold "<>". intros. crush. 
  }
  {
    specialize (IHtctxR p q ell (eq_refl (lcomm p q ell))).
    destr_hyps. unfold M.Equal in H0 ,H1.
    exists x,x0. split. exists x1. exists x2.  
    specialize (H0 p).
    specialize (H1 p).
    crush.
    split.
    exists x3. exists x4.
    specialize (H0 q).
    specialize (H1 q).
    crush. easy.
  }
Qed.

Ltac red_inv_use H s a :=
  let H_ueq := fresh in set (H_ueq := eq_refl a); apply (H s) in H_ueq.

Definition m_update (p:nat) (t:ltt) (g:tctx) := M.add p t (M.remove p g).

Theorem map_perm_invariance : forall p g t, M.find p g = (Some t) -> 
  M.Equal (m_update p t g) g.
Proof.
  unfold M.Equal; intros. unfold m_update.
  destruct (Nat.eq_dec y p);[
    subst;
    rewrite M.add_spec1;crush 
  |
    rewrite M.add_spec2;try rewrite M.remove_spec2;crush
  ].
Qed.

Lemma singleton_merge x e (g1 g2 :tctx) (Hdisj_1: MF.Disjoint g1 g2) :
  M.find x g1 =None -> M.find x g2 = None 
  -> forall (Hdm: MF.Disjoint g1 (M.add x e g2)), 
  M.Equal (M.add x e (disj_merge g1 g2 Hdisj_1)) (disj_merge g1 (M.add x e (g2)) Hdm).
Proof.
  intros.
  unfold M.Equal. intros; destruct (Nat.eq_dec x y);
  destruct (M.find y g1);destruct (M.find y g1);subst;
  try rewrite M.add_spec1;try rewrite M.add_spec2; crush; 
  unfold disj_merge;rewrite MF.merge_spec1mn; 
  try rewrite M.add_spec1;try rewrite M.add_spec2;
  crush; rewrite MF.merge_spec1mn ; 
  try rewrite M.add_spec1;try rewrite M.add_spec2; crush.
Qed.

Instance EqMEQ {A: Type} : Equivalence (@M.Equal A).
Proof. apply MF.Equal_equiv. Qed.

#[export] Instance RWMEQ {A: Type}: Proper ((@M.Equal A) ==> (@M.Equal A) ==> impl) (@M.Equal A).
Proof. repeat intro.
       unfold M.Equal in *.
       specialize(H y1).
       specialize(H0 y1).
       specialize(H1 y1).
       crush.
Qed.

#[export] Instance RWMRMV {A: Type}: Proper (eq ==> (@M.Equal A) ==> M.Equal) M.remove.
Proof. apply MF.remove_m. Qed.

#[export] Instance RWMADD {A: Type}: Proper (eq ==> eq ==> M.Equal ==> (@M.Equal A)) M.add.
Proof.  apply MF.add_m. Qed.

#[export] Instance RWDSJ {elt: Type}: Proper (M.Equal ==> M.Equal ==> iff) 
(MF.Disjoint (elt:=elt)).
Proof. 
  unfold "==>". 
  constructor;
  apply MF.Disjoint_m;
  apply MF.Equal_Eqdom;crush. 
Qed.

Lemma disj_weakening : forall (g1 g2:tctx) x e, MF.Disjoint g1 (M.add x e g2) ->
  MF.Disjoint g1 g2.
Proof.
  intros.
  unfold MF.Disjoint in *. intros. specialize (H k).
  Search M.In M.add.
  rewrite MF.add_in_iff in H. crush.
Qed.

#[export] Instance RWMMRG {A: Type}: Proper ((eq ==> eq ==> eq ==> eq) ==> (@M.Equal A) ==> (@M.Equal A) ==> (@M.Equal A)) M.merge.
Proof. unfold "==>".  apply MF.merge_m. Qed.

#[export] Instance RWMIN {A: Type}: Proper (eq ==> (@M.Equal A) ==> iff) M.In.
Proof. unfold "==>".  constructor; unfold M.Equal in H0; intros;
subst;specialize (H0 y); try rewrite MF.in_find in *.
rewrite H0 in H1. easy.
rewrite <- H0 in H1. easy.
Qed.


Ltac all_to_find := rewrite MF.in_find in *.

#[export] Instance RWMTCTXR: Proper ((@M.Equal ltt) ==> (eq) ==> (@M.Equal ltt) ==> (iff)) tctxR.
Proof. unfold "==>". constructor; intros; subst. 
apply Rstruct with (g1:=y) (g2:=y1) (g1':=x) (g2':=x1);crush. 
apply Rstruct with (g1:=x) (g2:=x1) (g1':=y) (g2':=y1);crush.
Qed.

Theorem tctxR_weakening (g1 g1' g2 : tctx) (Hdisj_1: MF.Disjoint g1 g2) 
  (Hdisj_2: MF.Disjoint g1' g2):
  forall l, tctxR g1 l g1' -> tctxR (disj_merge g1 g2 Hdisj_1) l 
  (disj_merge g1' g2 Hdisj_2).
Proof.
  intros.
  induction g2 using (MF.map_induction).
  {
    assert (He1 : M.Equal (disj_merge g1 g2 Hdisj_1) g1).
    {
     unfold M.Equal. intros. 
     destruct (M.find y g1) eqn:H_yg1;destruct (M.find y g2) eqn:H_yg2; 
     try tac_double_find_disjoint.
     apply spc_merge_find1 
     with (g2:=g2) (H_disj:=Hdisj_1) in H_yg1. easy.
     unfold MF.Empty in H0. 
     rewrite <- MF.find_mapsto_iff in H_yg2. specialize (H0 y l0). crush.
     apply spc_merge_nfind2. crush. 
    }
    assert (He2 :  M.Equal (disj_merge g1' g2 Hdisj_2) g1').
    {
     unfold M.Equal. intros. 
     destruct (M.find y g1') eqn:H_yg1;destruct (M.find y g2) eqn:H_yg2; 
     try tac_double_find_disjoint.
     apply spc_merge_find1
     with (g2:=g2) (H_disj:=Hdisj_2) in H_yg1. easy.
     unfold MF.Empty in H0. 
     rewrite <- MF.find_mapsto_iff in H_yg2. specialize (H0 y l0). crush.
     apply spc_merge_nfind2. crush. 
    }
    apply Rstruct with (g1:= (disj_merge g1 g2 Hdisj_1)) 
    (g1':= g1) (g2:= (disj_merge g1' g2 Hdisj_2)) 
    (g2':= g1'); try easy.
  }
  {
    assert(Hd: MF.Disjoint g1 g2_1). {
      unfold MF.Add in *;
      rewrite H1 in Hdisj_1;
      apply disj_weakening in Hdisj_1; easy.
    }
    assert(Hd': MF.Disjoint g1' g2_1). {
      unfold MF.Add in *;
      rewrite H1 in Hdisj_2;
      apply disj_weakening in Hdisj_2; easy.
    }
    assert (Hd'': MF.Disjoint g1 (M.add x e (g2_1))).
    {
      unfold MF.Add in H1.
      rewrite <- H1. easy.
    }
    assert (Hd''': MF.Disjoint g1' (M.add x e (g2_1))).
    {
      unfold MF.Add in H1.
      rewrite <- H1. easy.
    }
    assert (He1:  M.Equal (M.add x e (disj_merge g1 g2_1 Hd)) (disj_merge g1 g2_2 Hdisj_1)).
    {
      unfold MF.Add in H1.
      unfold disj_merge.
      setoid_rewrite H1.
      fold disj_merge.
      change (M.merge both g1 g2_1) with (disj_merge g1 g2_1 Hd).
      change (M.merge both g1 (M.add x e g2_1)) with 
      (disj_merge g1 (M.add x e g2_1) Hd'').
      apply singleton_merge; try rewrite MF.not_in_find in H0; crush.
      destruct (M.find x g1) eqn:H_yg1; try easy.
      Search M.Equal M.find.
      setoid_rewrite H1 in Hdisj_1.
      unfold MF.Disjoint in Hd''. specialize (Hd'' x).
      rewrite MF.add_in_iff in Hd''.
      apply opt_lem2 in H_yg1.
      rewrite <- MF.in_find in H_yg1.
      crush.
    }
    assert (He2: M.Equal (M.add x e (disj_merge g1' g2_1 Hd')) 
    (disj_merge g1' g2_2 Hdisj_2)).
    {
     unfold MF.Add in H1.
     unfold disj_merge. 
     setoid_rewrite H1.
     change (M.merge both g1' g2_1) with (disj_merge g1' g2_1 Hd').
     change (M.merge both g1' (M.add x e g2_1)) 
     with (disj_merge g1' (M.add x e g2_1) Hd''' ).
     Check singleton_merge.
     apply singleton_merge; crush.
     rewrite H1 in Hdisj_2.
     destruct (M.find x g1') eqn:Hxg1; crush.
     rewrite MF.in_find in H0.
     unfold MF.Disjoint in Hdisj_2.
     specialize (Hdisj_2 x).
     rewrite MF.add_in_iff in Hdisj_2.
     apply opt_lem2 in Hxg1.
     rewrite <- MF.in_find in Hxg1. crush. rewrite <- MF.not_in_find. easy.
    }
    apply Rstruct with (g1:=disj_merge g1 g2_2 Hdisj_1) 
    (g1':=M.add x e (disj_merge g1 g2_1 Hd))
    (g2':=M.add x e (disj_merge g1' g2_1 Hd'))
    (g2:=disj_merge g1' g2_2 Hdisj_2); crush.
    unfold disj_merge in *.
    setoid_rewrite <- He1.
    setoid_rewrite <- He2.
    apply RvarI;crush.
    rewrite MF.not_mem_find.
    rewrite MF.merge_spec1mn; destruct (M.find x g1) eqn:Hyg1;
    destruct (M.find x g2_1) eqn:Hyg2; crush;
    change (M.In x g2_1 -> False) with (~ M.In x g2_1) in H0; try rewrite MF.not_in_find in H0; crush.
    unfold MF.Disjoint in Hdisj_2.
    specialize (Hdisj_1 x).
    unfold MF.Add in H1.
    rewrite MF.in_find in Hdisj_1.
    apply opt_lem2 in Hyg1.
    setoid_rewrite H1 in Hdisj_1.
    rewrite MF.add_in_iff in Hdisj_1. crush.
  }
Qed.

Theorem tctxR_weakening2 (g1 g1' g2 : tctx) (Hdisj_1: MF.Disjoint g2 g1) 
  (Hdisj_2: MF.Disjoint g2 g1')
  :
  forall l, tctxR g1 l g1' -> tctxR (disj_merge g2 g1 Hdisj_1) l 
  (disj_merge g2 g1' Hdisj_2).
Proof.
  intros.
  apply Rstruct with (g1:=(disj_merge g2 g1 Hdisj_1))
  (g1':=(disj_merge g1 g2 (MF.Disjoint_sym Hdisj_1)))
  (g2' :=(disj_merge g1' g2 (MF.Disjoint_sym Hdisj_2)))
  (g2:=(disj_merge g2 g1' Hdisj_2)); try apply disj_merge_sym.
  apply tctxR_weakening. easy.
Qed.
Lemma not_in_remove : forall k (g:tctx), ~M.In k (M.remove k g).
Proof.
  intros.
  apply MF.remove_1; easy.
Qed.

Theorem simple_red_send : forall p q g ct s xs n,
  p <> q ->
  M.find p g = Some (ltt_send q xs) -> 
  onth n xs= (Some (s,ct)) ->
  tctxR g (lsend p q (Some s) n) (m_update p ct g).
Proof.
  intros.
  assert (Hr_1:tctxR (M.add p (ltt_send q xs) M.empty) 
  (lsend p q (Some s) n) (M.add p ct M.empty)).
  {
    apply Rsend; crush.
  }
  unfold m_update.
  assert (Hd:MF.Disjoint (M.remove p g) (M.add p ct M.empty)).
  {
   unfold MF.Disjoint.
   intros.
   Search M.remove M.In.
   destruct (Nat.eq_dec p k); crush. apply not_in_remove in H3; easy.
   destruct (M.find k (M.add p ct M.empty)) eqn:Hy1.
   Search M.add M.find.
   apply MF.add_neq_o with (m:=M.empty) (e:=ct) in n0.
   Search M.find M.empty.
   rewrite M.empty_spec in n0. crush.
   rewrite MF.in_find in H4. crush.
  }
  assert(He1: M.Equal (M.add p ct (M.remove p g)) 
  (disj_merge (M.remove p g) (M.add p ct M.empty) Hd)).
  {
    unfold M.Equal. intros.
    destruct (Nat.eq_dec p y).
    {
     subst.
     unfold disj_merge.
     rewrite MF.merge_spec1mn.
     rewrite M.add_spec1.
     rewrite M.remove_spec1.
     rewrite M.add_spec1.
     1-3:crush. 
    }
    
    destruct (M.find y g) eqn:H_yg1;
    rewrite M.add_spec2;
    try rewrite MF.remove_neq_o;
    unfold disj_merge;
    try rewrite MF.merge_spec1mn;
    try rewrite MF.remove_neq_o;
    try rewrite M.add_spec2;
    try rewrite M.empty_spec;
    crush.
  }
  assert (Hd2:MF.Disjoint (M.remove p g) (M.add p (ltt_send q xs) M.empty)).
  {
   unfold MF.Disjoint.
   intros.
   destruct (Nat.eq_dec p k); crush. apply not_in_remove in H3; easy.
   destruct (M.find k (M.add p (ltt_send q xs) M.empty)) eqn:Hy1.
   Search M.add M.find.
   apply MF.add_neq_o with (m:=M.empty) (e:=(ltt_send q xs)) in n0.
   Search M.find M.empty.
   rewrite M.empty_spec in n0. crush.
   rewrite MF.in_find in H4. crush.
  }

  assert(He2: M.Equal g 
  (disj_merge (M.remove p g) (M.add p (ltt_send q xs) M.empty) Hd2)).
  {
    Check singleton_merge.
    unfold M.Equal.
    intros.
    unfold disj_merge.
    destruct(Nat.eq_dec y p); rewrite MF.merge_spec1mn;crush.
    rewrite M.remove_spec1;
    rewrite M.add_spec1;crush.
    rewrite M.add_spec2; try rewrite M.empty_spec; try rewrite M.remove_spec2; crush.
    destruct (M.find y g) eqn:Hyg; crush.
  }
  
  unfold m_update.
  apply Rstruct with (g1:=g) 
  (g1':=(disj_merge (M.remove p g) (M.add p (ltt_send q xs) M.empty) Hd2)) 
  (g2' := (disj_merge (M.remove p g) (M.add p ct M.empty) Hd)) 
  (g2:= M.add p ct (M.remove p g));crush.
  apply tctxR_weakening2. 
  assumption.
Qed.


Theorem simple_red_recv : forall p q g ct s xs n,
  p <> q ->
  M.find p g = Some (ltt_recv q xs) -> 
  onth n xs= (Some (s,ct)) ->
  tctxR g (lrecv p q (Some s) n) (m_update p ct g).
Proof.
  intros.
  assert (Hr_1:tctxR (M.add p (ltt_recv q xs) M.empty) 
  (lrecv p q (Some s) n) (M.add p ct M.empty)).
  {
    apply Rrecv; crush.
  }
  unfold m_update.
  assert (Hd:MF.Disjoint (M.remove p g) (M.add p ct M.empty)).
  {
   unfold MF.Disjoint.
   intros.
   Search M.remove M.In.
   destruct (Nat.eq_dec p k); crush. apply not_in_remove in H3; easy.
   destruct (M.find k (M.add p ct M.empty)) eqn:Hy1.
   Search M.add M.find.
   apply MF.add_neq_o with (m:=M.empty) (e:=ct) in n0.
   Search M.find M.empty.
   rewrite M.empty_spec in n0. crush.
   rewrite MF.in_find in H4. crush.
  }
  assert(He1: M.Equal (M.add p ct (M.remove p g)) 
  (disj_merge (M.remove p g) (M.add p ct M.empty) Hd)).
  {
    unfold M.Equal. intros.
    destruct (Nat.eq_dec p y).
    {
     subst.
     unfold disj_merge.
     rewrite MF.merge_spec1mn.
     rewrite M.add_spec1.
     rewrite M.remove_spec1.
     rewrite M.add_spec1.
     1-3:crush. 
    }
    
    destruct (M.find y g) eqn:H_yg1;
    rewrite M.add_spec2;
    try rewrite MF.remove_neq_o;
    unfold disj_merge;
    try rewrite MF.merge_spec1mn;
    try rewrite MF.remove_neq_o;
    try rewrite M.add_spec2;
    try rewrite M.empty_spec;
    crush.
  }
  assert (Hd2:MF.Disjoint (M.remove p g) (M.add p (ltt_recv q xs) M.empty)).
  {
   unfold MF.Disjoint.
   intros.
   destruct (Nat.eq_dec p k); crush. apply not_in_remove in H3; easy.
   destruct (M.find k (M.add p (ltt_recv q xs) M.empty)) eqn:Hy1.
   Search M.add M.find.
   apply MF.add_neq_o with (m:=M.empty) (e:=(ltt_recv q xs)) in n0.
   Search M.find M.empty.
   rewrite M.empty_spec in n0. crush.
   rewrite MF.in_find in H4. crush.
  }

  assert(He2: M.Equal g 
  (disj_merge (M.remove p g) (M.add p (ltt_recv q xs) M.empty) Hd2)).
  {
    Check singleton_merge.
    unfold M.Equal.
    intros.
    unfold disj_merge.
    destruct(Nat.eq_dec y p); rewrite MF.merge_spec1mn;crush.
    rewrite M.remove_spec1;
    rewrite M.add_spec1;crush.
    rewrite M.add_spec2; try rewrite M.empty_spec; try rewrite M.remove_spec2; crush.
    destruct (M.find y g) eqn:Hyg; crush.
  }
  
  unfold m_update.
  apply Rstruct with (g1:=g) 
  (g1':=(disj_merge (M.remove p g) (M.add p (ltt_recv q xs) M.empty) Hd2)) 
  (g2' := (disj_merge (M.remove p g) (M.add p ct M.empty) Hd)) 
  (g2:= M.add p ct (M.remove p g));crush.
  apply tctxR_weakening2. 
  assumption.
Qed.

Lemma context_red_simple_comm: forall k xq xp p q gamma' s s'' Tp_k Tq_k, 
    p <> q ->
    onth k xq = Some (s'', Tq_k) ->
    onth k xp = Some (s, Tp_k) ->
    M.find p gamma'= None ->
    M.find q gamma'=None ->
    subsort s s'' ->
    tctxR (M.add p (ltt_send q xp) (M.add q (ltt_recv p xq) gamma'))
    (lcomm p q k) (M.add p Tp_k (M.add q Tq_k gamma')).
Proof.
    intros.
    assert(Hd1: forall Ttp Ttq,
    MF.Disjoint (M.add p Ttp (M.add q Ttq M.empty) )
    gamma').
    {
     unfold MF.Disjoint in *. unfold not. intros.
     destruct(Nat.eq_dec p k0);destruct (Nat.eq_dec q k0);crush.
     rewrite  <- MF.not_in_find in H2; try easy.
     rewrite  <- MF.not_in_find in H3; try easy.
     rewrite MF.in_find in H6. apply opt_lem1 in H6. destr_hyps.
     Check M.add_spec2.
     rewrite M.add_spec2 in H5;try easy.
     rewrite M.add_spec2 in H5;try easy.
    }
    assert(H_eq: forall Ttp Ttq Hdd, M.Equal ((M.add p Ttp (M.add q Ttq
    gamma'))) (disj_merge (M.add p Ttp (M.add q Ttq
    M.empty)) gamma' Hdd)).
    {
     unfold M.Equal. intros.
     unfold disj_merge. rewrite MF.merge_spec1mn;crush.
     destruct (Nat.eq_dec p y); destruct (Nat.eq_dec q y);crush.
     + rewrite M.add_spec1. rewrite M.add_spec1. easy.
     + rewrite M.add_spec2. rewrite M.add_spec1. rewrite M.add_spec2.
     rewrite M.add_spec1. 1-3: try easy.
     + repeat rewrite M.add_spec2;try easy. rewrite M.empty_spec. 
     destruct (M.find y gamma') eqn:Hyg;crush.   
    }
    Ltac Hdeq t1 t2 H_eq Hd1:= setoid_rewrite (H_eq t1 t2 (Hd1 t1 t2)).
    Hdeq (ltt_send q xp) (ltt_recv p xq) H_eq Hd1.
    Hdeq Tp_k Tq_k H_eq Hd1.
    apply tctxR_weakening.
    assert(Heq1: forall Ttp Ttq Hdd, M.Equal (M.add p Ttp
    (M.add q Ttq M.empty)) (disj_merge (M.add p Ttp M.empty) (M.add q Ttq M.empty) Hdd)).
    {
     intros.
     unfold M.Equal; intros. unfold disj_merge. rewrite MF.merge_spec1mn;
     destruct (Nat.eq_dec p y);destruct (Nat.eq_dec q y);crush.
     + rewrite M.add_spec1. rewrite M.add_spec1. rewrite M.add_spec2. rewrite M.empty_spec.
     crush. easy.     
     + rewrite M.add_spec2. rewrite M.add_spec1. rewrite M.add_spec2. rewrite M.empty_spec.
     crush. easy. easy.
     + repeat rewrite M.add_spec2; try repeat rewrite M.empty_spec;try easy.     
    }
    assert(Hd2: forall (Ttp Ttq:ltt), MF.Disjoint (M.add p Ttp M.empty) (M.add q Ttq M.empty)).
    {
     unfold MF.Disjoint. unfold not. intros. destruct (Nat.eq_dec p k0);
     destruct (Nat.eq_dec q k0);try repeat rewrite MF.in_find in *;
     crush.
     + rewrite M.add_spec2 in H7;try easy.
     + rewrite M.add_spec2 in H6;try easy.
     + rewrite M.add_spec2 in H6;try easy.    
    }
    intros.
    Hdeq (ltt_send q xp) (ltt_recv p xq) Heq1 Hd2.
    Hdeq Tp_k Tq_k Heq1 Hd2.
    eapply Rcomm with (s:=s) (s':=s''); try easy.
    apply Rsend;try easy.
    apply Rrecv;try easy.
Qed.


Theorem simple_red_comm : forall p q g xp xq sp sq k Tp Tq,
  p <> q ->
  M.find p g= Some (ltt_send q xp) ->
  M.find q g = Some (ltt_recv p xq) ->
  onth k xp =Some (sp, Tp) ->
  onth k xq=Some (sq, Tq) ->
  subsort sp sq ->
  tctxR g (lcomm p q k) (M.add p Tp (M.add q Tq (M.remove p (M.remove q g)))).
Proof.
  intros.
  set (gamma_same := (M.add p (ltt_send q xp) (M.add q (ltt_recv p xq) (M.remove p (M.remove q g))))). 
  assert (M.Equal gamma_same g).
  {
    unfold M.Equal. intros.
    destruct (Nat.eq_dec y p); 
    destruct (Nat.eq_dec y q);unfold gamma_same;subst; 
    repeat (try rewrite M.add_spec1;try rewrite M.add_spec2;try rewrite M.remove_spec1;try rewrite M.remove_spec2);
    crush.
  }
  setoid_rewrite <- H5 at 1. unfold gamma_same.
  eapply context_red_simple_comm with (s:=sp) (s'':=sq);crush.
  rewrite M.remove_spec1. easy.
  rewrite M.remove_spec2;try rewrite M.remove_spec1;crush.
Qed.

Lemma lem_6_10 : forall r g l g' , tctxR g l g' ->
     ~ ispSubjl r l ->
     M.find r g = M.find r g'.
Proof.
  intros.
  induction H.
  1-2:(
    destruct (Nat.eq_dec p r) eqn:Hpr;simpl in H0;
    do 2 rewrite MF.add_o;crush
  ).
  unfold disj_merge; rewrite MF.merge_spec1mn.  
  destruct (Nat.eq_dec p r); destruct (Nat.eq_dec q r);simpl in H0;subst;crush;
  unfold disj_merge; rewrite MF.merge_spec1mn;
  crush.
  1-3:crush.
  destruct (Nat.eq_dec p r);subst;[do 2 rewrite M.add_spec1 | ]. easy.
  rewrite M.add_spec2. rewrite M.add_spec2.
  1-3:crush.
  apply  IHtctxR in H0.
  unfold M.Equal in *; crush.
Qed. 

Lemma transition_sort_some_send: forall g g' p q o n, tctxR g (lsend p q o n) g' ->
exists s, o=Some s.
Proof.
  intros.
  dependent induction H; try exists s;
  try eapply IHtctxR with (p:=p) (q:=q) (n:=n); crush.
Qed.

Lemma transition_sort_some_recv: 
forall g g' p q o n, tctxR g (lrecv p q o n) g' ->
exists s, o=Some s.
Proof.
  intros.
  dependent induction H; try exists s;
  try eapply IHtctxR with (p:=p) (q:=q) (n:=n); crush.
Qed.

Lemma lem_6_12_reduction_determinism: forall g l g' g'', tctxR g l g' -> tctxR g l g'' -> M.Equal g' g''.
Proof.
  intros.
  
  Ltac send_rec_solve H H0 p y invert :=
  destruct (Nat.eq_dec p y);[
  subst;
  apply invert in H0;
  apply invert in H; destr_hyps; 
  try rewrite M.add_spec1 in *; crush |

  apply lem_6_10 with (r:=y) in H0,H; try rewrite M.add_spec2 in H0; 
  try rewrite M.empty_spec in H;
  try rewrite M.add_spec2; try rewrite M.empty_spec; crush].
  
  destruct l;rename n into p, n0 into q, n1 into n;
  unfold M.Equal;subst;intros; try (destruct o).  
  send_rec_solve H H0 p y lem_6_11b_tctx_recv_invert.
  apply transition_sort_some_recv in H;crush.
  send_rec_solve H H0 p y lem_6_11a_tctx_send_invert.
  apply transition_sort_some_send in H;crush.
  destruct (Nat.eq_dec p y);destruct (Nat.eq_dec q y);subst.
  1-3: apply lem_6_11c_tctx_comm_invert in H,H0; crush.
  apply lem_6_10 with (r:=y) in H0,H;crush. 
Qed.