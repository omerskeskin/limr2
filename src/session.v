From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
Require Import Coq.Program.Equality.
From SST Require Import src.header src.assoc src.sim src.expr src.process src.local src.global src.balanced src.typecheck 
src.part src.gttreeh src.step src.merge src.projection src.lcontext src.wfltt. 

Inductive session: Type :=
  | s_ind : part   -> process -> session
  | s_par : session -> session -> session
  | s_zero : session.
  
Notation "p '<--' P"   :=  (s_ind p P) (at level 50, no associativity).
Notation "s1 '|||' s2" :=  (s_par s1 s2) (at level 50, no associativity).

Inductive ForallT (P : part -> process -> Prop) : session -> Prop := 
  | ForallT_mono : forall pt op, P pt op -> ForallT P (pt <-- op)
  | ForallT_par : forall (M1 M2 : session), ForallT P M1 -> ForallT P M2 -> ForallT P (M1 ||| M2)
  | ForallT_zero: ForallT P s_zero.

Fixpoint flattenT (M : session) : (list part) := 
  match M with 
    | p <-- _   => p :: nil
    | M1 ||| M2 => flattenT M1 ++ flattenT M2
    | s_zero => nil
  end.

Definition InT (pt : part) (M : session) : Prop :=
  In pt (flattenT M).

Definition in_not_end (pt:part) (gamma: tctx) := exists x, M.find pt gamma=Some x /\ x <> ltt_end.  

Inductive scong : session -> session -> Prop :=
    | scong_refl : forall M, scong M M
    | scong_par_com : forall M1 M1' , scong (M1 ||| M1') (M1' ||| M1)
    | scong_par_ass: forall M1 M2 M3 , 
    scong (M1 ||| (M2 ||| M3))
    ((M1 ||| M2)|||M3)
    | scong_zero: forall M, scong M (M ||| s_zero)
    | scong_sym: forall M M', scong M M' -> scong M' M
    | scong_cong: forall M M' M'', scong M M' -> scong (M|||M'') (M' ||| M'')
    | scong_trans: forall M M' M'', scong M M' -> scong M' M'' -> scong M M''.

Inductive unfoldB : relation session :=
  | pcb_tau   : forall p P Q M, tauP P Q -> unfoldB ((p <-- P) ||| M) ((p <-- Q) ||| M)
  | pcb_scong : forall M1 M2 , scong M1 M2 -> unfoldB M1 M2.

Definition unfoldBrtc := clos_refl_trans session unfoldB.

Inductive unfoldP : relation session := 
  | pc_tau   : forall p P Q M, tauP P Q -> unfoldP ((p <-- P) ||| M) ((p <-- Q) ||| M)
  | pc_refl  : forall M, unfoldP M M
  | pc_trans : forall M M' M'', unfoldP M M' -> unfoldP M' M'' -> unfoldP M M''
  | pc_par1  : forall M M', unfoldP (M ||| M') (M' ||| M)
  | pc_par2  : forall M M' M'', unfoldP ((M ||| M') ||| M'') (M ||| (M' ||| M''))
  | pc_par1m : forall M M' M'', unfoldP ((M ||| M') ||| M'') ((M' ||| M) ||| M'')
  | pc_par2m : forall M M' M'' M''', unfoldP (((M ||| M') ||| M'') ||| M''') ((M ||| (M' ||| M'')) ||| M''')
  | pc_zero_elim : forall M, unfoldP (M ||| s_zero) M
  | pc_zero_intro : forall M, unfoldP  M (M ||| s_zero).

Create HintDb brocs.
Hint Constructors unfoldB scong clos_refl_trans:brocs.

Create HintDb procs.
Hint Constructors unfoldP tauP betaPr :procs.

Definition unfoldP_to_unfoldB : forall M M', unfoldP M M' -> unfoldBrtc M M'.
Proof.
  intros. induction H;try solve [econstructor 1; eauto with brocs].
  econstructor 3;try exact IHunfoldP1;try easy.
Qed.

Definition sess_map := M.t process.

Definition noDupSess M := NoDup (flattenT M). 

Fixpoint sess_to_map (M:session):  sess_map :=
  match M with 
  | s_zero => M.empty
  | s_ind p P => M.add p P M.empty
  | s_par M M' => M.merge both (sess_to_map M) (sess_to_map M')
  end.

Create HintDb nodup.

Search NoDup app.

Hint Resolve nodup_swap NoDup_app_remove_r NoDup_app_remove_l nodup_swap2 :nodup.
Hint Rewrite app_nil_r app_assoc :nodup.
Hint Rewrite <- app_assoc :nodup.


Lemma NoDup_app_pairwise {A:Type}: forall (xs:list A) ys zs, NoDup (xs ++ ys) -> 
NoDup (ys ++ zs) -> NoDup (xs ++ zs) -> NoDup (xs++ys++zs).
Proof.
  induction xs;intros.
  rewrite app_nil_l. easy.
  simpl. econstructor.
  {
    simpl in H. simpl in H1.
    Search In "++".
    rewrite in_app_iff.
    rewrite in_app_iff.
    red;intros.
    destruct H2. inversion H;subst.
    rewrite in_app_iff in H5. tauto.
    destruct H2. inversion H;subst. rewrite in_app_iff in H5;tauto.
    inversion H1;subst. rewrite in_app_iff in H5;tauto.
  }
  {
    eapply IHxs;inversion H;inversion H1;subst;easy. 
  }
Qed. 

Lemma scong_preserves_noDup : forall M M', scong M M' -> forall M'', noDupSess (M|||M'') <-> 
noDupSess (M' |||M'').
Proof.
  intros * Hscong.  induction Hscong;try easy;unfold noDupSess in *;simpl in *.
  {
    split;intros;eauto with nodup.  
  }
  {
    split;intros;
    rewrite <- app_assoc; rewrite <- app_assoc; 
    rewrite <- app_assoc in H; rewrite <- app_assoc in H; easy.
  }
  {
    split;intros;eauto with nodup. rewrite app_nil_r in H. easy. 
  }
  {
    split;intros.
    {
      rewrite <- app_assoc. 
      eapply NoDup_app_pairwise. eapply IHHscong. eapply NoDup_app_remove_r;try exact H.
      
      rewrite <- app_assoc in H. eapply NoDup_app_remove_l;try exact H.
      eapply IHHscong. rewrite <- app_assoc in H. eapply nodup_swap2 in H.
      rewrite app_assoc in H. eapply NoDup_app_remove_r;try exact H.
    }
    {
       rewrite <- app_assoc. 
      eapply NoDup_app_pairwise. eapply IHHscong. eapply NoDup_app_remove_r;try exact H.
      
      rewrite <- app_assoc in H. eapply NoDup_app_remove_l;try exact H.
      eapply IHHscong. rewrite <- app_assoc in H. eapply nodup_swap2 in H.
      rewrite app_assoc in H. eapply NoDup_app_remove_r;try exact H.
    }
  }
  {
    split;intros.
    eapply IHHscong2. eapply IHHscong1. easy.
    
    eapply IHHscong1. eapply IHHscong2. easy. 
  }
Qed.


Lemma noDupSess_par : forall M1 M2, noDupSess (M1 ||| M2) -> noDupSess M1 /\ noDupSess M2.
Proof.
  intros. red in H;simpl in H. split; 
  [eapply NoDup_app_remove_r in H | eapply NoDup_app_remove_l in H];try easy.
Qed.

Lemma NoDup_2in_false : forall (p:nat) M1 M2, In p M1 -> In p M2 -> NoDup (M1 ++ M2) -> False.
Proof.
  intros *. revert p M2. Search app In.
  intros. eapply in_split in H. eapply in_split in H0.
  destr_hyps;subst.
  rewrite <- app_assoc in H1.
  eapply nodup_swap in H1. rewrite <- app_assoc in H1.
  simpl in H1. inversion H1;subst.
  eapply H2. eapply in_or_app. right.
  eapply in_or_app. left. eapply in_or_app. right. simpl. tauto.
Qed.

Lemma sess_map_inT_to_in : forall p M, noDupSess M -> InT p M <-> M.In p (sess_to_map M).
Proof.
  intros * Hnd. induction M.
  {
    split;intros. destruct (Nat.eq_dec p n);subst. eapply MF.add_in_iff;tauto.
    red in H;inversion H;subst;try easy.
    destruct (Nat.eq_dec p n);subst. red;simpl;tauto.
    simpl in H. rewrite MF.add_in_iff in H;destruct H;subst;try easy.
    rewrite MF.empty_in_iff in H;easy.
  }
  {
    split;intros.
    {
      red in H;simpl in H.
      eapply in_app_or in H.
      destruct H.
      {
        assert(Hinp: InT p M1) by (red;easy).
        rewrite IHM1 in Hinp.
        rewrite MF.in_find in Hinp. simpl.
        rewrite MF.in_find.
        rewrite MF.merge_spec1mn. eapply opt_lem1 in Hinp;destr_hyps.
        destruct (M.find p (sess_to_map M2)) eqn:Hs2;rewrite H0;simpl;try easy.
        assert(Hnd2: noDupSess M2). 
        {
           eapply noDupSess_par in Hnd;destr_hyps;easy.
        }
        specialize (IHM2 Hnd2).
        assert(Hmin : M.In p (sess_to_map M2)).
        {
          rewrite MF.in_find. eapply opt_lem2;try exact Hs2. 
        }
        rewrite <- IHM2 in Hmin.
        red in Hmin;red in Hnd;simpl in Hnd.
        
        eapply NoDup_2in_false in Hmin;try exact H;try easy.
        intros;simpl;easy.
        eapply noDupSess_par in Hnd;destr_hyps;easy. 
      }
      {
        assert(Hinp: InT p M2) by (red;easy).
      rewrite IHM2 in Hinp.
        rewrite MF.in_find in Hinp. simpl.
        rewrite MF.in_find.
        rewrite MF.merge_spec1mn. eapply opt_lem1 in Hinp;destr_hyps.
        destruct (M.find p (sess_to_map M1)) eqn:Hs2;rewrite H0;simpl;try easy.
        assert(Hnd2: noDupSess M1). 
        {
           eapply noDupSess_par in Hnd;destr_hyps;easy.
        }
        specialize (IHM1 Hnd2).
        assert(Hmin : M.In p (sess_to_map M1)).
        {
          rewrite MF.in_find. eapply opt_lem2;try exact Hs2. 
        }
        rewrite <- IHM1 in Hmin.
        red in Hmin;red in Hnd;simpl in Hnd.
        
        eapply NoDup_2in_false in Hmin;try exact H;try easy. eapply nodup_swap;easy.
        intros;simpl;easy.
        eapply noDupSess_par in Hnd;destr_hyps;easy. 
      }
    }
    {
      rewrite MF.in_find in H;eapply opt_lem1 in H;try easy. destr_hyps.
      simpl in H.
      rewrite MF.merge_spec1mn in H;try solve [intros;simpl;reflexivity].
       destruct (M.find p (sess_to_map M1)) eqn:Hg1;destruct (M.find p (sess_to_map M2)) eqn:Hg2;simpl in H;
       try easy;
       eapply noDupSess_par in Hnd;destr_hyps.

       specialize (IHM1 H0). red;simpl. eapply in_or_app.
       eapply opt_lem2 in Hg1. 
       rewrite <- MF.in_find in Hg1. rewrite <- IHM1 in Hg1. left. red;easy.


       specialize (IHM2 H1). red;simpl. eapply in_or_app.
       eapply opt_lem2 in Hg2. 
       rewrite <- MF.in_find in Hg2. rewrite <- IHM2 in Hg2. right. red;easy.

    }
  }
  split;intros. red in H;simpl in H;try easy. simpl in H. rewrite MF.empty_in_iff in H;easy.
Qed.

Lemma sess_to_map_noDup_to_disj : forall M M', noDupSess (M |||M') -> MF.Disjoint (sess_to_map M) (sess_to_map M').
Proof.
  intros. red;intros;red;intros;destr_hyps. rewrite <- sess_map_inT_to_in in H0.
  rewrite <- sess_map_inT_to_in in H1. red in H;simpl in H. red in H0;red in H1;
  eapply NoDup_2in_false;try exact H;try exact H0;try easy.
  1-2:eapply noDupSess_par in H;destr_hyps;easy.
Qed.

Lemma sess_to_map_disj_merge: forall M M', noDupSess (M ||| M') -> 
forall Hdisj, sess_to_map (M ||| M') = disj_merge  (sess_to_map M) (sess_to_map M') Hdisj.
Proof.
  intros.
  simpl. unfold disj_merge. easy.
Qed. 
  

Lemma noDupSess_zero : forall M,
noDupSess (M ||| s_zero) <-> noDupSess (M ).
Proof.
  intros;split;intros. red in H. simpl in H. rewrite app_nil_r in H. red;simpl;easy.
  red;simpl;rewrite app_nil_r;easy.
Qed.

Lemma scong_to_map : forall M M', noDupSess M -> scong M M' -> M.Equal (sess_to_map M) (sess_to_map M').
Proof.
  intros * Hnd Hscong.
  induction Hscong.
  eapply MF.Equal_equiv.
  {
    eapply sess_to_map_noDup_to_disj in Hnd as Hdisj. rewrite sess_to_map_disj_merge;try easy.
    Search MF.Disjoint "sym".
    set (Hdisj' := MF.Disjoint_sym (m1:=sess_to_map M1) (m2:=sess_to_map M1') Hdisj).

    rewrite sess_to_map_disj_merge;try easy.
    rewrite disj_merge_sym;unfold Hdisj';try easy. red;simpl.
    red in Hnd;simpl in Hnd. eapply nodup_swap in Hnd;try easy.
  }
  {
    red;intros;simpl.
    repeat rewrite MF.merge_spec1mn;try solve[intros;simpl;easy].
    destruct (M.find y (sess_to_map M1)) eqn:Hg1;destruct (M.find y (sess_to_map M2)) eqn:Hg2; 
    destruct (M.find y (sess_to_map M3)) eqn:Hg3;simpl;try easy.
    eapply noDupSess_par in Hnd;destr_hyps.
    eapply sess_to_map_noDup_to_disj in H0.
    red in H0. specialize (H0 y).
    eapply opt_lem2 in Hg2, Hg3.
    rewrite <- MF.in_find in Hg2, Hg3. tauto.
  }
  {
    simpl. red;intros. rewrite MF.merge_spec1mn;try solve[intros;simpl;easy].
    rewrite MF.empty_o. destruct (M.find y (sess_to_map M)) eqn:Hy1;simpl;try easy.
  }
  {
    eapply scong_preserves_noDup with (M'':= s_zero)in Hscong.
    rewrite <- noDupSess_zero in Hnd. rewrite <- Hscong in Hnd.
    rewrite noDupSess_zero in Hnd. symmetry. tauto.
  }
  {
    eapply noDupSess_par in Hnd;destr_hyps. specialize (IHHscong H).
    simpl. red;intros. red in IHHscong. specialize (IHHscong y).
    rewrite MF.merge_spec1mn. rewrite MF.merge_spec1mn. 2-3:intros;simpl;easy. 
    destruct (M.find y (sess_to_map M)) eqn:Hg1;
    destruct (M.find y (sess_to_map M'')) eqn:Hg2;try easy;simpl;
    try rewrite <- IHHscong;try easy.
    
  }
  {
    eapply scong_preserves_noDup with (M'':=s_zero) in Hscong1.
    do 2 (rewrite noDupSess_zero in Hscong1).
    pose proof Hnd as Hnd'.
    rewrite Hscong1 in Hnd.
    specialize (IHHscong1 Hnd').
    specialize (IHHscong2 Hnd).
    assert(Htr: Transitive (@ M.Equal process)).
    {
      eapply SetoidList.eqatrans. eapply MF.Equal_equiv. 
    }
    eapply Htr;try exact IHHscong1;try easy.
  }
Qed.


Lemma scong_p_unique : forall p P Q M M', noDupSess  ((p <-- P)|||M) -> 
scong ((p<--P)|||M) ((p<--Q)|||M') -> P=Q.
Proof.
  intros * Hn Hsc. 
  eapply scong_to_map in Hsc as Hmn;try easy. simpl in Hmn.
  red in Hmn. specialize (Hmn p).
  rewrite MF.merge_spec1mn in Hmn.
  rewrite MF.merge_spec1mn in Hmn.
  2-3:intros;simpl;easy.
  autorewrite with mmaps in Hmn.
  assert(M.In p (sess_to_map (p <-- P))).
  {
    simpl. eapply MF.add_in_iff;tauto. 
  }
  assert(M.In p (sess_to_map (p <-- Q))).
  {
    simpl. eapply MF.add_in_iff;tauto. 
  }
  assert(M.find p (sess_to_map M) = None).
  {
    eapply sess_to_map_noDup_to_disj in Hn.
    destruct (M.find p (sess_to_map M)) eqn:Hg1. red in Hn.
    specialize (Hn p). eapply opt_lem2 in Hg1.
    rewrite <- MF.in_find in Hg1. tauto. easy.   
  }
  assert(M.find p (sess_to_map M') = None).
  {
    eapply scong_preserves_noDup with (M'':=s_zero) in Hsc.
    do 2 rewrite noDupSess_zero in Hsc.
    rewrite Hsc in Hn.
    eapply sess_to_map_noDup_to_disj in Hn.
    destruct (M.find p (sess_to_map M')) eqn:Hg1. red in Hn.
    specialize (Hn p). eapply opt_lem2 in Hg1.
    rewrite <- MF.in_find in Hg1. tauto. easy.   
  }
  rewrite H1 in Hmn. rewrite H2 in Hmn. simpl in Hmn. inversion Hmn;subst;easy.
Qed.

(*Lemma scong_single : forall p P Q M M', NoDup (flattenT ((p <-- P)|||M)) ->
    proc_of_p p P M -> 
    scong M M' -> 
    proc_of_p p Q M' ->
    P=Q.
  Proof.
    intros * Hnd Hprocm Hsc Hprocq. revert Hprocm Hprocq Hnd. induction Hsc;intros.
    {

    }
  Proof.
    intros. dependent induction H;subst;try eauto with procs.
    symmetry. eapply IHscong.
    eapply IHscong.*)
Lemma pc_par5 : forall M M' M'', unfoldP (M ||| (M' ||| M'')) ((M ||| M') ||| M'').
Proof.
  intros.
  apply pc_trans with (M' := (M' ||| M'') ||| M). constructor.
  apply pc_trans with (M' := (M' ||| (M'' ||| M))). constructor.
  apply pc_trans with (M' := (M'' ||| M) ||| M'). constructor.
  apply pc_trans with (M' := M'' ||| (M ||| M')). constructor. constructor. 
Qed.
Hint Resolve pc_par5 :procs.

Lemma unf_cont_l : forall M1 M1' M2,
  unfoldP M1 M1' -> 
  unfoldP (M1 ||| M2) (M1' ||| M2).
Proof.
  intros. revert M2.
  induction H; intros;try solve [eauto with procs].
Qed.

Lemma unf_cont_r : forall M1 M2 M2', 
    unfoldP M2 M2' -> 
    unfoldP (M1 ||| M2) (M1 ||| M2').
Proof.
  intros.
  apply pc_trans with (M' := M2 ||| M1). constructor.
  apply pc_trans with (M' := M2' ||| M1). apply unf_cont_l. easy.
  constructor.
Qed.

Lemma unf_cont : forall M1 M1' M2 M2',
    unfoldP M1 M1' -> unfoldP M2 M2' -> 
    unfoldP (M1 ||| M2) (M1' ||| M2').
Proof.
  intros.
  apply pc_trans with (M' := (M1 ||| M2')). apply unf_cont_r. easy.
  apply unf_cont_l. easy.
Qed.

Hint Resolve unf_cont_l unf_cont_r unf_cont :procs.

Lemma scong_preserves_noDup_zero : forall M M', scong M M' -> noDupSess M <-> noDupSess M'.
Proof.
  intros. eapply scong_preserves_noDup with (M'':=s_zero) in H.
  do 2 (rewrite noDupSess_zero in H). easy.
Qed.

Lemma scong_to_unfoldP : forall M M', noDupSess M -> scong M M' -> (unfoldP M M' /\ unfoldP M' M).
Proof.
  intros  * Hnd Hc.  revert Hnd;induction Hc; subst;intros; try solve [eauto with procs].
  {
    eapply scong_preserves_noDup_zero in Hnd as Hnd';try exact Hc. specialize (IHHc Hnd').
    tauto.
  }
  {
    eapply noDupSess_par in Hnd;destr_hyps.
    specialize (IHHc H). destr_hyps.
    split; eauto with procs. 
  }
  pose proof Hnd as Hnd1.
  eapply scong_preserves_noDup_zero in Hc1 as Hc3;rewrite Hc3 in Hnd.
  specialize (IHHc1 Hnd1). specialize (IHHc2 Hnd). destr_hyps. eauto with procs.
Qed.

Lemma unfoldB_to_unfoldP_single : forall M M', noDupSess M -> unfoldB M M' -> unfoldP M M'.
Proof.
    intros.
    induction H0. econstructor 1. easy. eapply scong_to_unfoldP in H0;destr_hyps; easy.
Qed.

Lemma unfoldB_preserves_noDup_single : forall M M', unfoldB M M' -> (noDupSess M <-> noDupSess M'). 
Proof.
  intros.
  inversion H;subst.
  unfold noDupSess. simpl. easy.
  eapply scong_preserves_noDup_zero in H0.
  easy.
Qed.

Lemma unfoldB_preserves_noDup : forall M M', unfoldBrtc M M' -> (noDupSess M <-> noDupSess M').
Proof.
  intros.
  induction H. eapply unfoldB_preserves_noDup_single in H;try easy.
  easy.
  tauto.
Qed. 

Definition unfoldB_to_unfoldP : forall M M', noDupSess M -> unfoldBrtc M M' -> unfoldP M M'.
Proof.
  intros * Hnd H. induction H.
  
  eapply unfoldB_to_unfoldP_single;try easy.
  eauto with procs.
  eapply unfoldB_preserves_noDup in H, H0.
  specialize (IHclos_refl_trans1 Hnd).
  rewrite H in Hnd.
  specialize (IHclos_refl_trans2 Hnd).
  eauto with procs.
Qed.

Lemma unfoldB_p_unique_single : forall p P Q M M', noDupSess ((p <-- P)|||M) -> 
unfoldB ((p<--P)|||M) ((p<--Q)|||M') -> (tauP P Q) \/P=Q.
Proof.
  intros. dependent induction H0.
  left. easy.
  eapply scong_p_unique in H0;try easy. tauto.
Qed.

Search tauP.

Definition unfoldB_sess_map M M' := forall p x, M.find p M = Some x ->
  exists y, M.find p M' = Some y /\ (clos_refl_trans process tauP) x y.

Lemma sess_to_map_preserves_unfoldB_single: forall M M', noDupSess M -> unfoldB M M' ->
  unfoldB_sess_map (sess_to_map M) (sess_to_map M').
Proof.
  intros * Hnd Hunfb.
  revert Hnd. induction Hunfb.
  {
    intros. simpl.
    red;intros.
    assert(Hmpn : ~ InT p M).
    {
      red;intros. red in Hnd. simpl in Hnd.
      red in H1. inversion Hnd;easy.
    }
    rewrite sess_map_inT_to_in in Hmpn.
    assert(M.find p (sess_to_map M)=None) by 
    (rewrite MF.in_find in Hmpn; tauto).
    destruct (Nat.eq_dec p0 p);subst.
    {
      rewrite MF.merge_spec1mn in H0.
      rewrite H1 in H0. autorewrite with mmaps in H0. simpl in H0. inversion H0;subst.
      exists Q.
      split. rewrite MF.merge_spec1mn. rewrite H1. autorewrite with mmaps. easy.
      intros;simpl;easy.
      econstructor 1;easy.
      intros;simpl;easy.
    }
    {
      rewrite MF.merge_spec1mn in H0.
      autorewrite with mmaps in H0. 
      destruct (M.find p0 (sess_to_map M)) eqn:Hg1;simpl in *;inversion H0;subst.
      exists x. split. rewrite MF.merge_spec1mn. autorewrite with mmaps. rewrite Hg1. simpl. easy.
      intros;simpl;easy.
      econstructor 2.
      intros;simpl;easy.
    }
    eapply noDupSess_par in Hnd;tauto.
  }
  {
    intros.
    eapply scong_to_map in H as Hmp;try easy.
    red;intros.
    red in Hmp.
    specialize (Hmp p). exists x.
    split;try congruence. econstructor 2. 
  }
Qed.

Lemma sess_to_map_preserves_unfoldB: forall M M', noDupSess M -> unfoldBrtc M M' ->
  unfoldB_sess_map (sess_to_map M) (sess_to_map M').
Proof.
  intros * Hnodup Hunfb.
  induction Hunfb.
  eapply sess_to_map_preserves_unfoldB_single;try easy.
  red;intros;exists x0;split;try easy;try constructor 2.
  eapply unfoldB_preserves_noDup in Hunfb1;try exact Hnodup.
  specialize (IHHunfb1 Hnodup).
  rewrite Hunfb1 in Hnodup.
  specialize (IHHunfb2 Hnodup).
  red;intros.
  red in IHHunfb1, IHHunfb2.
  specialize (IHHunfb1 _ _ H).
  destr_hyps.
  specialize (IHHunfb2 _ _ H0).
  destr_hyps.
  exists x2. split;try easy. econstructor 3;try exact H1;try easy.
Qed.

Lemma unfoldB_p_unique : forall p P Q M M', noDupSess ((p <-- P)|||M) -> 
unfoldBrtc ((p<--P)|||M) ((p<--Q)|||M') -> (clos_refl_trans process tauP P Q).
Proof.
  intros. 
  eapply sess_to_map_preserves_unfoldB in H0 as Hump;try easy.
  red in H0.
  assert(Hmp: M.find p (sess_to_map ((p <-- P) |||M))=  Some P).
  {
    simpl.
    rewrite MF.merge_spec1mn.
    assert(M.find p (sess_to_map M)=None).
    {
      assert(~ InT p M). red in H;simpl in H. inversion H;subst;easy.
      rewrite sess_map_inT_to_in in H1. rewrite MF.in_find in H1. tauto.
      eapply noDupSess_par in H;try easy. 
    }
    rewrite H1. autorewrite with mmaps. simpl. easy.
    intros;simpl. easy.
  }
  specialize (Hump _ _ Hmp). destr_hyps.
  assert(M.find p (sess_to_map ((p <-- Q) ||| M')) = Some Q).
  {
    simpl.
    assert(M.find p (sess_to_map M')=None).
    
  eapply unfoldB_preserves_noDup in H0 as Hnd2;try exact H.
  pose proof H as H'. rewrite Hnd2 in H'.
 
    assert(~ InT p M'). red in H';simpl in H'. inversion H';subst;easy.
      rewrite sess_map_inT_to_in in H3. rewrite MF.in_find in H3. tauto.
      eapply noDupSess_par in H';try easy.
      rewrite MF.merge_spec1mn.
      rewrite H3. autorewrite with mmaps. simpl. easy.
      intros;simpl;easy. 
  }
  assert(Q=x) by congruence;subst. easy.
Qed.

Inductive typ_sess : session -> tctx -> Prop := 
  | t_sess : forall M gamma (Hassocable: exists g, wfgC g /\ assoc gamma g), tctx_wf gamma ->
                         (forall pt, in_not_end pt gamma -> InT pt M) ->
                         NoDup (flattenT M) ->
                         ForallT (fun u P => exists T, M.find u gamma = Some T /\
                        typ_proc nil nil P T /\ (forall n, exists m, guardP n m P)) M ->
                         typ_sess M gamma.

Inductive betaP_lbl:  session -> label -> session -> Prop :=
  | r_comm  : forall p q xs y l e v Q M, 
              onth l xs = Some y -> stepE e (e_val v) -> 
              betaP_lbl ((p <-- (p_recv q xs)) ||| (q <-- (p_send p l e Q)) ||| M) (lcomm q p l)
                    ((p <-- subst_expr_proc y (e_val v) 0 0) ||| (q <-- Q) ||| M) 
  | r_struct: forall M1 M1' M2 M2' l, unfoldP M1 M1' -> unfoldP M2' M2 -> betaP_lbl M1' l M2' -> betaP_lbl M1 l M2.

Definition betaP a b := exists l, betaP_lbl a l b.

Definition stuck (M : session) := ((exists M', unfoldP M M' /\ ForallT (fun _ P => P = p_inact) M') -> False) /\ ((exists M', betaP M M') -> False).

Definition stuckM (M : session) := exists M', multi betaP M M' /\ stuck M'.