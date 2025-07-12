(* From mathcomp Require Import ssreflect.seq all_ssreflect. *)
From Paco Require Import paco pacotac.
From SST Require Import src.expr src.header src.local CpdtTactics src.lcontext.
From SST Require Import src.global src.projection src.part  src.balanced src.merge src.wfltt src.gttreeh.
From SST Require Import lemma.projection lemma.projection_helper lemma.decidable lemma.soundness.
From SST Require Import src.step lemma.step src.assoc lemma.completeness src.ltth src.path_props.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Init.Logic.
From Equations Require Import Equations.


Import ListNotations.

Definition gttstepRel g g' := exists p q ell, gttstepC g g' p q ell.

Definition gttstepRtc := clos_refl_trans gtt gttstepRel.

Locate tctxRtc.

Lemma tctxR_invariance (P:tctx -> Prop): forall gamma gamma', 
    P gamma -> (forall a b , P a -> tctxRcomm a b -> P b) ->
    tctxRtc gamma gamma'-> P gamma'.
Proof.
    intros;induction H1;crush.
Qed.

Lemma tctx_wf_after_rtc : forall gamma gamma', 
tctx_wf gamma -> tctxRtc gamma gamma' -> tctx_wf gamma'.
Proof.
    intros.
    pattern gamma'. 
    eapply tctxR_invariance with (gamma:=gamma);try easy.
    intros. red in H2;destr_hyps;subst. Search tctx_wf tctxR.
    eapply tctx_wf_after_red_comm;[| exact H2];easy.
Qed.

Lemma tctxR_invariance_wf (P:tctx -> Prop): forall gamma gamma', 
    tctx_wf gamma ->
    P gamma -> (forall a b , tctx_wf a -> P a -> tctxRcomm a b -> P b) ->
    tctxRtc gamma gamma'-> P gamma'.
Proof.
    intros.  induction H2;crush.
    eapply IHclos_refl_trans2;try easy.
    fold tctxRtc in H2_.
    eapply tctx_wf_after_rtc with (gamma:=x);try easy.
Qed.

Lemma assoc_preservation_context: forall gamma gamma' g, tctx_wf gamma -> 
tctxRtc gamma gamma' ->
    wfgC g ->
    assoc gamma g -> exists g', assoc gamma' g' /\ wfgC g'.
Proof.
    intros.
    pattern gamma'.
    set (P:=(fun t : tctx => exists g' : gtt, assoc t g' /\ wfgC g')).

    specialize (tctxR_invariance_wf P) as Hinv.
    eapply Hinv with (gamma:=gamma);try easy. red. exists g;easy.
    
    intros. unfold P in *. red in H5;destr_hyps. 
    eapply assoc_completeness in H5;try easy.
    destr_hyps. exists x3. split;try easy.
    
    eapply wfgC_after_step in H7;try easy.
    eapply assoc_implies_projectable;easy.
Qed.

Check typ_p_gtth.
Check ishParts.

Inductive is_tree_prefix : gtth -> gtth -> Prop :=
    | tree_prefix_hole : forall n g, is_tree_prefix (gtth_hol n) g
    | tree_prefix_tree : forall p q xs ys,
    Forall2 (fun u v => (u=None /\ v=None)
                \/ exists s g1 g2, u=Some (s, g1) /\ v=Some (s,g2) /\
                is_tree_prefix g1 g2
            ) xs ys ->
    is_tree_prefix (gtth_send p q xs) (gtth_send p q ys).
  

Section tree_prefix_ind_ref.
  Variable P : gtth -> gtth -> Prop.
  Hypothesis P_hol : forall n g, P  (gtth_hol n ) g.
  Hypothesis P_send : forall p q xs ys, List.Forall2 (fun u v => (u = None /\ v = None) \/ 
                                                 (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ P g g')) xs ys -> 
                                                 P (gtth_send p q xs) (gtth_send p q ys).
  
  Fixpoint tree_prefix_ind_ref G G' (a : is_tree_prefix G G') {struct a} : P  G G'.
  Proof.
    destruct a.
    {
        apply P_hol.   
    }
    apply P_send.
    eapply Forall2_mono in H as Hm. exact Hm.
    intros.
    simpl.
    destruct H0;[crush|].
    destr_hyps;subst.
    right. exists x0, x1, x2.
    crush.
  Qed.
End tree_prefix_ind_ref.


Lemma prefix_height_helper: forall p q s t xs ys, 
(*wfgtth (gtth_send p q xs) -> wfgtth (gtth_send s t ys) ->*)
Forall2 (fun u v => (u=None /\ v=None) \/ exists s g g', u=Some (s,g) /\ v=Some (s,g') /\ gtth_height g <= gtth_height g') xs ys ->
gtth_height (gtth_send p q xs) <= gtth_height (gtth_send s t ys).
Proof.
    intros.
    generalize dependent ys.
    generalize dependent xs.
    induction xs.
    {
        intros. crush.   
    }
    {
        intros.
        destruct ys. inversion H.

        inversion H;subst.
        destruct a.
        {
            destruct H3;try easy.
            destr_hyps;subst.
            inversion H0;subst.
            simpl.
            eapply Arith_base.add_le_mono_r_proj_l2r.
            eapply Nat.max_le_compat. easy.
            assert (gtth_height (gtth_send p q xs) <= gtth_height (gtth_send s t ys)).
            {
                eapply IHxs;try easy.   
            }
            crush.
        }
        {
            destruct H3;destr_hyps;try easy;subst. simpl.   
            assert (gtth_height (gtth_send p q xs) <= gtth_height (gtth_send s t ys)).
            {
                eapply IHxs;try easy.   
            }
            crush.
        }
    }
Qed.

Lemma prefix_height_le : forall gc gp, wfgtth gc -> wfgtth gp -> is_tree_prefix gc gp -> gtth_height gc <= gtth_height gp.
Proof.
    intros * Hwfg1 Hwfg2 Hpref.
    induction  Hpref using tree_prefix_ind_ref.
    {
        simpl;intros;
        apply gtth_height_ge_0;easy.      
    }
    {
        Search Forall2.
        eapply prefix_height_helper.
        eapply Forall2_forall.
        eapply Forall2_length. exact H.
        intros.
        destruct (onth k xs) eqn:Hyg.
        {
            right.
            eapply Forall2_prop_r in H; [ | exact Hyg].
            destr_hyps.
            destruct H0;try easy.
            destr_hyps;subst. inversion H0;subst. exists x0, x1, x2.
            crush.
            inversion Hwfg1;subst. eapply Forall_prop in H6; [| exact Hyg].
            destruct H6;try easy.
            destr_hyps.
            inversion H;subst.
            inversion Hwfg2;subst; eapply Forall_prop in H9; [ | exact H1].
            destruct H9;try easy;destr_hyps. inversion H5;subst. apply H2;easy.
        }
        {
            left.
            destruct (onth k ys) eqn:Hyg1;crush.
            eapply Forall2_prop_l in H;[| exact Hyg1]. destr_hyps. destruct H0;try easy.
            destr_hyps. crush.
        } 
    }
Qed.

Inductive is_tree_proper_prefix : gtth -> gtth -> Prop :=
    | tree_proper_prefix_hole : forall n p q xs, is_tree_proper_prefix (gtth_hol n) (gtth_send p q xs)
    | tree_proper_prefix_tree : forall p q xs ys,
    Forall2 (fun u v => (u=None /\ v=None)
                \/ exists s g1 g2, u=Some (s, g1) /\ v=Some (s,g2) /\
                is_tree_proper_prefix g1 g2
            ) xs ys ->
    is_tree_proper_prefix (gtth_send p q xs) (gtth_send p q ys).


Section tree_proper_prefix_ind_ref.
  Variable P : gtth -> gtth -> Prop.
  Hypothesis P_hol : forall n p q xs, P (gtth_hol n ) (gtth_send p q xs).
  Hypothesis P_send : forall p q xs ys, List.Forall2 (fun u v => (u = None /\ v = None) \/ 
                                                 (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ P g g')) xs ys -> 
                                                 P (gtth_send p q xs) (gtth_send p q ys).
  
  Fixpoint tree_proper_prefix_ind_ref G G' (a : is_tree_proper_prefix G G') {struct a} : P  G G'.
  Proof.
    destruct a.
    {
        apply P_hol.   
    }
    apply P_send.
    eapply Forall2_mono in H as Hm. exact Hm.
    intros.
    simpl.
    destruct H0;[crush|].
    destr_hyps;subst.
    right. exists x0, x1, x2.
    crush.
  Qed.
End tree_proper_prefix_ind_ref.

Print projection.




Lemma empty_not_wfgtth: forall p q, wfgtth (gtth_send p q []) -> False.
Proof. intros. inversion H. crush. Qed.
Lemma max_lt_compat: forall n m p q, n < m -> p< q -> Nat.max n p  < Nat.max m q.
Proof. crush. Qed.

Lemma gtth_height_unfold_once_some : forall p q xs a b, gtth_height (gtth_send p q (Some (a,b)::xs)) =
Init.Nat.max (gtth_height b +1) (gtth_height (gtth_send p q xs)).
Proof.
    intros.
    crush.
Qed.

Lemma gtth_height_unfold_once_none : forall p q xs, gtth_height (gtth_send p q (None::xs)) =
Init.Nat.max (0) (gtth_height (gtth_send p q xs)).
Proof.
    intros.
    crush.
Qed.

Lemma SList_by_Forall2 {A:Type}: forall (xs ys: list (option A)), Forall2 (fun u v => u=None /\ v=None \/ exists x1 x2, u=Some x1 /\ v=Some x2) xs ys->
SList xs -> SList ys.
Proof.
    intros. destruct xs. inversion H0.
    generalize dependent ys. 
    generalize dependent o. induction xs.
    {
        intros;
        inversion H;subst; destruct o; destruct H3;try easy;
        destr_hyps; inversion H1;subst;
        inversion H5;subst;easy.        
    }
    {
        intros.
        destruct ys;
        inversion H;subst.
        
        destruct o;destruct H4;destr_hyps;subst;try easy;
        (assert (Hnys: SList ys) by (eapply IHxs with (o:=a);try easy));
        [inversion H1;subst;simpl;destruct ys|];try easy.
    }
Qed.
Lemma proper_prefix_height_helper: forall p q s t xs ys, 
wfgtth (gtth_send p q xs) -> wfgtth (gtth_send s t ys) ->
Forall2 (fun u v => (u=None /\ v=None) \/ exists s g g', u=Some (s,g) /\ v=Some (s,g') /\ gtth_height g < gtth_height g') xs ys ->
gtth_height (gtth_send p q xs) < gtth_height (gtth_send s t ys).
Proof.
    intros * Hwfg1 Hwfg2.
    (*
    destruct xs;destruct ys; try (apply empty_not_wfgtth in H);try (apply empty_not_wfgtth in H1);try easy.
    *)
    generalize dependent ys.
    generalize dependent xs.
    destruct xs.
    intros. inversion Hwfg1;subst;inversion H2.
    revert o.
    induction xs.
    {
        intros.
        destruct o.
        {
            inversion H;subst.
            destruct H2;try easy. destr_hyps.
            inversion H0;subst.
            destruct l';[|inversion H4];crush.
        }
        inversion Hwfg1. inversion H2.   
    }
    {
        intros.
        destruct ys. inversion H.

        inversion H;subst.
        destruct o.
        {
            destruct H3;try easy. destr_hyps. inversion H0;subst.
            do 2 rewrite gtth_height_unfold_once_some.
            eapply max_lt_compat. crush.
            eapply IHxs;try easy.
            assert(SList (a::xs)) by (inversion Hwfg1;subst;try easy).
            constructor;[| inversion Hwfg1;subst;inversion H8];easy.
            assert (SList ys).
            {
                inversion Hwfg2;subst;simpl in H4.
                destruct ys;try easy.   
            }
            constructor;inversion Hwfg2;inversion H8;try easy.
        }
        {
            destruct H3;destr_hyps;try easy;subst.    
            do 2 rewrite gtth_height_unfold_once_none.
            do 2 rewrite (Nat.max_0_l).
            eapply IHxs;try easy.
            assert(SList (a::xs)) by (inversion Hwfg1;subst;try easy).
            constructor;[| inversion Hwfg1;subst;inversion H7];easy.
            assert (SList ys).
            {
                inversion Hwfg2;subst. simpl in H3.
                destruct ys;try easy.   
            }
            constructor;inversion Hwfg2;inversion H7;try easy.
        }
    }
Qed.

Lemma gtth_height_gt_0 : forall p q xs, wfgtth ((gtth_send p q xs)) -> gtth_height (gtth_send p q xs) > 0.
Proof.
    intros;
    destruct (gtth_height (gtth_send p q xs)) eqn:Hyg;
    [
        apply gtth_height_0_means_hol in Hyg|];crush.
Qed.

Lemma proper_prefix_height_le : forall gc gp, wfgtth gc -> wfgtth gp -> 
    is_tree_proper_prefix gc gp -> 
    gtth_height gc < gtth_height gp.
Proof.
    destruct gc;destruct gp;try easy;intros.
    simpl gtth_height at 1.
    specialize (gtth_height_gt_0 n0 n1 l) as Hgt.
    apply Hgt in H0. crush.

    rename l into xs, l0 into ys.
    induction H1 using tree_proper_prefix_ind_ref.
    {
        simpl gtth_height at 1.  specialize (gtth_height_gt_0 p q xs0) as Hgt. crush.    
    }
    {
        eapply proper_prefix_height_helper;try easy.
        eapply Forall2_forall;
        [eapply Forall2_length; exact H1|].
        intros.
        destruct (onth k xs0) eqn:Hyg.
        {
            right.
            eapply Forall2_prop_r in H1;[ | exact Hyg].
            destr_hyps.
            destruct H2;try easy.
            destr_hyps;subst. inversion H2;subst. exists x0, x1, x2.
            crush.
            inversion H;subst. eapply Forall_prop in H8; [| exact Hyg].
            destruct H8;try easy.
            destr_hyps.
            inversion H1;subst.
            inversion H0;subst; eapply Forall_prop in H11; [ | exact H3].
            destruct H11;try easy;destr_hyps. inversion H7;subst. apply H4;easy.
        }
        {
            left.
            destruct (onth k ys0) eqn:Hyg1;crush.
            eapply Forall2_prop_l in H1;[| exact Hyg1]. destr_hyps. destruct H2;try easy.
            destr_hyps. crush.
        }    
    }
Qed.

Definition path_starts_with (gamma:tctx) (pt:Path):=
  match pt with 
  | cocons (a,b) _ => a=gamma
  | _ => False
  end.


Lemma assoc_implies_part: forall p Tp gamma g, tctx_wf gamma  -> wfgC g -> assoc gamma g ->
M.find p gamma = Some Tp -> Tp <> ltt_end -> isgPartsC p g.
Proof.
    intros.
    destruct (decidable_isgPartsC g p);try easy.
    tac_use_assoc H1 p H4.
    specialize (Hassoc_u _ H2). easy. 
Qed.

Check balanced_to_tree.
Print typ_p_gtth.

Print projection.
(*

Inductive used_in_gtth : nat -> gtth -> Prop := 
    | used_hol_gtth : forall n, used_in_gtth n (gtth_hol n)
    | used_send_gtth : forall n xs p q k s ll, onth k xs = Some (s, ll) -> used_in_gtth n ll -> 
    used_in_gtth n (gtth_send p q xs).

Definition fills_holes_gtth (ls :list (option gtt)) (l : gtth) :=
    forall n, used_in_gtth n l -> exists s, onth n ls = Some s.


Definition Forall_used ctx (P:nat -> Prop) := forall n , used_in_gtth n ctx -> 
    P n.

Inductive projectionH : list (option gtt) -> gtth -> part -> ltt -> Prop :=
    | projectionH_hol : forall gs p t n, 
    fills_holes_gtth gs (gtth_hol n) ->
    Forall_used  (gtth_hol n) (fun u=> exists g, onth u gs =Some g /\ projectionC g p t)->
    projectionH gs (gtth_hol n) p t
    | projectionH_send : forall gs  r p q t ghs ys,
    fills_holes_gtth gs (gtth_send p q ghs) ->
    (ishParts r (gtth_send p q ghs) -> False) ->
    Forall2 (fun u v => u=None /\ v=None 
    \/ exists s g t', u=Some (s,g) /\ v=Some t' /\ projectionH gs g r t') ghs ys  ->
    isMerge t ys -> projectionH gs (gtth_send p q ghs) r t.

Lemma fills_holes_cont: forall gs p q k xs s g', fills_holes_gtth gs (gtth_send p q xs) -> onth k xs = Some (s,g') ->
fills_holes_gtth gs g'.
Proof.
    intros.
    red in H. red. intros.
    assert(used_in_gtth n (gtth_send p q xs)).
    {
        econstructor;[exact H0 | exact H1].   
    }
    specialize (H n H2). exact H.
Qed.

Lemma projectionH_corr_projectionC : forall gs ctx p Tp g, 
wfgC g -> fills_holes_gtth gs ctx -> typ_p_gtth gs ctx p g ->
 projectionH gs ctx p Tp -> projectionC g p Tp.
Proof. 
    intros * Hwfg  Hfills Htyp_p Hprojh.
    red in Htyp_p.
    induction ctx using gtth_ind_ref.
    {
        destr_hyps.
        destruct g.
        {
            constructor;try easy.
            eapply Forall_forall. intros.
            destruct x. right. exists g.
            eapply in_some_implies_onth in H2. destr_hyps.
            eapply Forall_prop in H1;[| exact H2]. destruct H1;try easy. destr_hyps.   
        }   
    }
*)
Search isMergeCtx Forall.
Print isMergeCtx.

Definition triple_opt_sum:= (fun u v w : option gtt =>
u = None /\ v = None /\ w = None \/
(exists t0 : gtt, u = None /\ v = Some t0 /\ w = Some
t0) \/
(exists t0 : gtt, u = Some t0 /\ v = None /\ w = Some
t0) \/
(exists t0 : gtt, u = Some t0 /\ v = Some t0 /\
w = Some t0)).

Lemma Forall3S_samesize {A:Type}: forall P (xs ys zs:list A), Forall3S P xs ys zs -> 
Datatypes.length xs= Datatypes.length zs \/ Datatypes.length ys = Datatypes.length zs.
Proof.
    intros;induction H;crush.
Qed.

Lemma Forall2R_to_Forall2 {A:Type}: 
forall (xs ys:list A) P,
Forall2R P xs ys -> Datatypes.length xs = Datatypes.length ys ->
Forall2 P xs ys.
Proof.
    intros.
    induction H.
    {
        destruct ys;crush.   
    }
    {
        constructor;try easy.
        eapply IHForall2R.
        simpl in H0. crush.   
    }
Qed.
Search Forall2R Datatypes.length.
Search Forall3S.

Lemma triple_sum_trilemma: forall xs ys zs x n, Forall3S triple_opt_sum xs ys zs ->
onth n zs = Some x -> onth n xs = Some x \/ onth n ys= Some x.
Proof.
    intros.
    generalize dependent ys.
    generalize dependent xs.
    generalize dependent n.
    induction zs.
    {
        intros.
        rewrite onth_nil in H0. easy.
    }
    {
        intros.
        destruct xs;destruct ys;intros;inversion H;[crush | crush |];subst.
        destruct n.
        {
            simpl in H0;subst.
            red in H5.
            destruct H5;crush.
        }
        {
            simpl in H0.
            simpl.
            eapply IHzs;try easy.
        }   
    }
Qed.


Lemma Forall_merge_gs P: forall gs gss,
P None -> isMergeCtx gs gss -> Forall (fun u=> u=None \/ exists g, u=Some g /\ Forall P g) gss ->
Forall P gs.
Proof.
    intros * Hpn.
    intros.
    induction H.
    {
        intros.
        eapply Forall_prop with (l:=0) in H0.
        destruct H0;try easy. destr_hyps.
        inversion H;subst.
        2:simpl;reflexivity. easy. 
    }
    {
        eapply IHisMergeCtx. inversion H0;try easy.   
    }
    {
        eapply Forall_forall.
        intros.
        destruct x;try easy.
        {
            Search Forall3S.
            Search isMergeCtx Forall.
            eapply in_some_implies_onth in H2 as Hsome. destr_hyps. rename x into n.
            eapply triple_sum_trilemma in H;[|exact H3].
            inversion H0;subst.
            destruct H.
            {
                specialize (IHisMergeCtx H7).
                eapply Forall_prop in H;[|exact IHisMergeCtx];easy.
            }
            {
                destruct H6;try easy;destr_hyps;subst.
                inversion H4;subst.
                eapply Forall_prop in H5;[|exact H];easy.
            }
        }
    }
Qed.

Lemma triple_sum_or_prop_l :  forall xs ys zs x n, Forall3S triple_opt_sum xs ys zs ->
onth n xs = Some x -> onth n zs = Some x.
Proof.
    intros * Hsum Honth.
    unfold triple_opt_sum in Hsum.
    Print Forall3S.
    generalize dependent xs.
    generalize dependent ys.
    revert n.
    induction zs.
    {
        intros.
        inversion Hsum;subst; rewrite onth_nil in Honth;easy.   
    }
    {
        intros.
        destruct xs;destruct ys;intros; inversion Hsum;[crush | crush |];subst.
        rewrite onth_nil in Honth;easy.
        destruct n.
        {
            simpl.
            simpl in Honth;subst.
            destruct H3;crush.   
        }
        {
            simpl in Honth.
            simpl.
            eapply IHzs;[exact H7|exact Honth].   
        }
    }
Qed.

Lemma triple_sum_or_prop_r :  forall xs ys zs x n, Forall3S triple_opt_sum xs ys zs ->
onth n ys = Some x -> onth n zs = Some x.
Proof.
    intros * Hsum Honth.
    unfold triple_opt_sum in Hsum.
    Print Forall3S.
    generalize dependent xs.
    generalize dependent ys.
    revert n.
    induction zs.
    {
        intros.
        inversion Hsum;subst; rewrite onth_nil in Honth;easy.   
    }
    {
        intros.
        destruct xs;destruct ys;intros; inversion Hsum;[crush | crush |];subst.
        rewrite onth_nil in Honth;easy.
        destruct n.
        {
            simpl.
            simpl in Honth;subst.
            destruct H3;crush.   
        }
        {
            simpl in Honth.
            simpl.
            eapply IHzs;[exact Honth|exact H7].   
        }
    }
Qed.

Lemma Forall2R_length {A:Type} {B:Type}: forall (P:A -> B-> Prop) xs ys, Forall2R P xs ys -> Datatypes.length xs <= Datatypes.length ys.
Proof.
    intros;
    induction H;crush.
Qed.
Lemma Forall2R_subset_trans {A:Type}: forall (xs ys zs: list (option A)),
Forall2R (fun u v=> u=None \/ u=v) xs ys ->
Forall2R (fun u v=> u=None \/ u=v) ys zs ->
Forall2R (fun u v=> u=None \/ u=v) xs zs.
Proof.
    intros.
    eapply Forall2_Forall.
    {
        eapply Forall2R_length in H, H0. crush.
    }
    {
        intros.
        destruct (onth k xs) eqn:Hyg.
        {
            eapply Forall2R_prop in H;[|exact Hyg].
            destr_hyps;subst.
            destruct H2;try easy.   
            symmetry in H.
            eapply Forall2R_prop in H0;[|exact H]. 
            destr_hyps.
            destruct H2;try easy;subst. right;easy.
        }
        left;easy.
    }
Qed.

Lemma mergeCtx_onth_subset: 
forall gs gs' gss n,
isMergeCtx gs gss ->
onth n gss = Some gs' ->
Forall2R (fun u v : option gtt => u = None \/ u = v) gs' gs.
Proof.
    intros * Hmerge Honth.
    generalize dependent n.
    induction Hmerge.
    {
        intros.
        destruct n. simpl in Honth. inversion Honth;subst.
        Search Forall2R.
        eapply Forall2_Forall;crush.
        
        simpl in Honth. rewrite onth_nil in Honth;easy.
    }
    {
        intros.
        destruct n; simpl in Honth;try easy.
        eapply IHHmerge;exact Honth.
    }
    {
        intros.
        destruct n.
        {
            simpl in Honth;inversion Honth;subst.
            Search Forall3S.
            eapply Forall3S_to_Forall2_r;exact H.   
        }
        {
            simpl in Honth.
            specialize (IHHmerge _ Honth).
            eapply Forall3S_to_Forall2_l in H.
            eapply Forall2R_subset_trans;[exact IHHmerge|];easy.
        }
    }
Qed.

Lemma Forall_subset {A:Type}: forall gs gs' (P: option A -> Prop), Forall2R (fun u v  => u = None \/ u = v) gs' gs -> P None -> 
Forall P gs -> Forall P gs'.
Proof.
    intros.
    eapply Forall_forall.
    intros.
    destruct x;try easy.
    eapply in_some_implies_onth in H2 as Hsome.
    destr_hyps.
    eapply Forall2R_prop in H;[|exact H3].
    destr_hyps.
    destruct H4;crush.
    symmetry in H4.
    eapply Forall_prop in H1;[|exact H4].
    crush.
Qed.

Lemma restricted_grafting_send : forall gs ctx p q g xs, 
wfgC g -> projectableA g -> typ_gtth gs ctx g -> 
(ishParts p ctx -> False) ->
usedCtx gs ctx ->
projectionC g p (ltt_send q xs) -> 
Forall
(fun u : option gtt =>
u = None \/
(exists (q : opt_lbl) (lsg : list (option (sort * gtt))),
u = Some (gtt_send p q lsg) \/
u = Some (gtt_send q p lsg) \/ u = Some gtt_end))
gs -> 
Forall (fun u=> u=None\/ exists ys, u=Some (gtt_send p q ys
)) gs.
Proof.
    intros * Hwfg  Hprojable Hgraft Hishparts Hused Hprojp Hgraftcond.
    
    generalize dependent g.
    generalize dependent gs.
    generalize dependent ctx.
    induction ctx using gtth_ind_ref.
    {
        intros.
        destruct g;[pinversion Hprojp;apply proj_mon|].
        eapply typ_gtth_hole_inv in Hgraft;try easy. destr_hyps;subst.
        eapply extendLis_forall. split;[|left;easy].
        
        right. exists x. eapply Forall_prop in Hgraftcond;[|rewrite extendExtract;easy].
        destruct Hgraftcond; try easy. destr_hyps.
        destruct H;[|destruct H];inversion H;subst;pinversion Hprojp;crush;apply proj_mon.   
    }
    {
        intros.
        destruct g;[pinversion Hprojp;apply proj_mon|].
        inversion Hgraft;subst.
        rename n into s, n0 into t, xs0 into ghs, l into gcs.
        inversion Hused;subst.
        (*
        eapply slist_implies_some in H3 as Hsome. destr_hyps;subst.
        eapply Forall_prop in H;[|exact H0]. destruct H;try easy. destr_hyps.
        
        inversion H;subst. clear H.
       *)
       eapply Forall_merge_gs;[|exact H4 | ].
        left. easy.

        eapply Forall_forall.
        intros.
        destruct x;[|crush].
        right. eapply in_some_implies_onth in H0 as Hsome.
        destr_hyps.
        exists l.
        split;try easy.
        eapply Forall2_prop_r in H6;[|exact H1].
        destr_hyps.
        destruct H5;try easy.
        destr_hyps.
        inversion H5;subst.
        rename x1 into ctx1,x2 into s1, x3 into ghs1.
        eapply Forall_prop in H as IH;[|exact H6].
        destruct IH;try easy;destr_hyps;inversion H2;subst.
        eapply Forall2_prop_r in H8 as Hgraftn;try exact H6.
        destr_hyps. 
        destruct H11;subst;try easy.
        destr_hyps. inversion H10;subst.
        rename x4 into g', x3 into ctx'.
        eapply mergeCtx_onth_subset with (gs:=gs) in H1 as Hsubs;try easy.
        assert (Hsp_noteq: s <> p).
        {
            red.
            intros;subst. apply Hishparts.
            apply ha_sendp.   
        }
        assert (Htp_noteq: t <> p).
        {
            red.
            intros;subst. apply Hishparts.
            apply ha_sendq.   
        }
        eapply H9 with (g:=g');try easy.
        {
            intros.
            eapply Hishparts. econstructor;try exact H13;try easy;exact H6.
        }
        {
            eapply Forall_subset with (gs:=gs);crush.   
        }
        {
            eapply continuation_wfgC;[exact Hwfg|exact H11].   
        }
        {
            Search projectableA gttstepC.
            eapply projectable_after_step with (g:=(gtt_send s t gcs));try easy.
            pfold.
            econstructor.
            2:symmetry in H11;exact H11.
            Search wfgC (_ <> _).
            eapply wfgC_triv in Hwfg as Hw. easy.
        }
        {
            Search typ_gtth usedCtx.
            eapply decidable_helper.typh_with_less;try exact Hsubs;easy.   
        }
        {
            pinversion Hprojp;try apply proj_mon;crush.
            eapply Forall2_prop_r in H22;[|exact H11].
            destr_hyps.
            destruct H14;try easy. destr_hyps;subst.
            inversion H14;subst.
            destruct H20;try easy.
            Search isMerge onth.
            eapply merge_inv_ss in H23;[|exact H15];subst.
            easy.  
        }  
    }
Qed. 

Print projection.

Lemma inequality_by_not_ishparts: forall p0 p q xs, (ishParts p0 (gtth_send p q xs) -> False) ->
                            p0 <> p /\ p0 <> q.
                            Proof.
                                intros;split;red;intros;exfalso;apply H;subst;constructor.
                            Qed.

Inductive projectionH : gtth -> (list (option gtt)) -> part -> ltth ->
(list (option ltt)) -> Prop :=
    | projectionH_hol : forall n m r g t gs ls,
    onth n gs= Some g -> onth m ls =Some t ->
    projectionC g r t -> 
    projectionH (gtth_hol n) gs r (ltth_hol m) ls
    | projectionH_recv: forall p r gs ls xs ys, p <> r ->
    Forall2
    (fun (u : option (sort * gtth))
    (v : option (sort * ltth)) =>
    u = None /\ v = None \/
    (exists (s : sort) (g : gtth) (t : ltth),
    u = Some (s, g) /\ v = Some (s,t) /\ projectionH g gs r t ls))
    xs ys -> projectionH (gtth_send p r xs) gs r (ltth_recv p ys) ls
    | projectionH_send: forall p r gs ls xs ys, p <> r ->
    Forall2
    (fun (u : option (sort * gtth))
    (v : option (sort * ltth)) =>
    u = None /\ v = None \/
    (exists (s : sort) (g : gtth) (t : ltth),
    u = Some (s, g) /\ v = Some (s,t) /\ projectionH g gs r t ls))
    xs ys -> projectionH (gtth_send r p xs) gs r (ltth_send p ys) ls
    | projectionH_cont: forall p q r t twt k xs ys gs ls, p <> q ->
        q <> r ->
        p <> r ->
        Forall2
        (fun (u : option (sort * gtth)) (v : option ltth) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : gtth) (t0 : ltth),
        u = Some (s,g) /\ v=Some t0 /\ projectionH g gs r t0 ls)) xs
        ys -> onth k  ys=Some t-> Forall (fun u=> u=None \/  exists th, u=Some th /\
        typ_ltth th ls twt) ys ->
         projectionH (gtth_send p q xs) gs
        r t ls
    .

Ltac tac_forall_to_length := repeat (match goal with [H: Forall2 _ ?a ?b|- _] =>
                apply Forall2_length in H |
                [H: Forall2R _ ?a ?b|- _] =>
                apply Forall2R_length in H
                end);crush.

Ltac tac_clear_id:= repeat match goal with [ H : ?a = ?a |- _ ] => clear H end.

Ltac tac_use_forall2 Hforall2 Honth :=
                    match Hforall2 with 
                    (Forall2 _ ?a ?b) => match Honth with 
                        (onth ?k ?a = Some ?p) => 
                        eapply Forall2_prop_r in Hforall2;try exact Honth
                        |
                        (onth ?k ?b = Some ?p) => 
                        eapply Forall2_prop_l in Hforall2;try exact Honth
                        end     
                    end. 
                    Ltac tac_remove_dilemma :=
                    match goal with 
                    [ H: ?a \/ ?b |- _] => destruct H;try easy end.
                    Ltac tac_inv_some := match goal with 
                    [H: Some ?a = Some ?b |- _] => inversion H;subst end.
                    Ltac tac_sanitize := destr_hyps;tac_remove_dilemma;destr_hyps;tac_inv_some;tac_clear_id.

Lemma projectionH_consistent: forall gs gx ls lx p r g Tr, 
wfgC g ->
wfgtth gx ->
typ_p_gtth gs gx p g ->
projectionC g r Tr ->
projectionH gx gs r lx ls -> typ_ltth lx ls Tr.
Proof.
    intros * Hwfg Hwfgth Htyp Hprojp Hprojhp.
    generalize dependent gs.
    generalize dependent g.
    revert ls lx Tr.
    generalize dependent gx.
    induction gx using gtth_ind_ref.
    {
        intros.
        inversion Hprojhp;subst.
        constructor.
        red in Htyp. destr_hyps.
        inversion H;subst.
        rewrite H0 in H7. inversion H7;subst.
        eapply proj_inj in Hprojp;try exact H2;subst;try easy.
    }
    {
        intros.
        rename H into IH.
        destruct (Nat.eq_dec p0 r);   
        destruct (Nat.eq_dec q r);subst;try easy.
        {
            red in Htyp;destr_hyps. inversion H;subst. apply wfgC_triv in Hwfg;try easy.         
        }
        {
            red in Htyp;destr_hyps.
            inversion H;subst.
            pinversion Hprojp;subst;try easy;try apply proj_mon.
            {
                exfalso. apply H2. apply decidable_helper.triv_pt_p;easy.   
            }
            inversion Hprojhp;subst;try easy.
            {
                eapply typ_ltth_send.
                eapply Forall2_forall;[tac_forall_to_length;crush |].
                rename xs into ghs, ys into gcs, ys0 into lcs, ys1 into lhs.
                intros.
                destruct (onth k lhs) eqn:Hyg.
                {
                    right.
                    eapply Forall2_prop_l in H16;try exact Hyg.

                    tac_sanitize.
                    exists x0, x2. 
                    eapply Forall2_prop_r in H8;try exact H3;tac_sanitize.
                    eapply Forall2_prop_r in H11;try exact H6;tac_sanitize.
                    eapply Forall_prop in IH;try exact H3;tac_sanitize.
                    exists x6.
                    (repeat split);try easy.
                    eapply H4 with (gs:=gs) (g:=x1);try easy.
                    {
                        inversion Hwfgth;subst.
                        eapply Forall_prop in H17;try exact H3. 
                        tac_sanitize;easy. 
                    }
                    {
                        eapply continuation_wfgC;try exact H6;try exact Hwfg.   
                    }
                    {
                        destruct H12;try easy.   
                    }
                    {
                        red.
                        (repeat split);try easy.
                        intros.
                        eapply H0. eapply ha_sendr;try exact H3;try exact H16;try easy.
                        1-2:red;intros;exfalso;subst;apply H0; constructor.   
                    }         
                }
                {
                    left;split;try easy.
                    destruct (onth k lcs) eqn:Hyg1;try easy.
                    eapply Forall2_prop_l in H11;try exact Hyg1;tac_sanitize.
                    eapply Forall2_prop_l in H8;try exact H3;tac_sanitize.
                    eapply Forall2_prop_r in H16;try exact H4;tac_sanitize.
                    rewrite Hyg in H11;easy.
                }
            }   
        }
        {
            red in Htyp;destr_hyps.
            inversion H;subst.
            pinversion Hprojp;subst;try easy;try apply proj_mon.
            {
                exfalso. apply H2. apply decidable_helper.triv_pt_q;easy.   
            }
            inversion Hprojhp;subst;try easy.
            {
                eapply typ_ltth_recv.
                eapply Forall2_forall;[tac_forall_to_length;crush |].
                rename xs into ghs, ys into gcs, ys0 into lcs, ys1 into lhs.
                intros.
                destruct (onth k lhs) eqn:Hyg.
                {
                    right.
                    eapply Forall2_prop_l in H16;try exact Hyg.

                    tac_sanitize.
                    exists x0, x2. 
                    eapply Forall2_prop_r in H8;try exact H3;tac_sanitize.
                    eapply Forall2_prop_r in H11;try exact H6;tac_sanitize.
                    eapply Forall_prop in IH;try exact H3;tac_sanitize.
                    exists x6.
                    (repeat split);try easy.
                    eapply H4 with (gs:=gs) (g:=x1);try easy.
                    {
                        inversion Hwfgth;subst.
                        eapply Forall_prop in H17;try exact H3. 
                        tac_sanitize;easy. 
                    }
                    {
                        eapply continuation_wfgC;try exact H6;try exact Hwfg.   
                    }
                    {
                        destruct H12;try easy.   
                    }
                    {
                        red.
                        (repeat split);try easy.
                        intros.
                        eapply H0. eapply ha_sendr;try exact H3;try exact H16;try easy.
                        1-2:red;intros;exfalso;subst;apply H0; constructor.   
                    }         
                }
                {
                    left;split;try easy.
                    destruct (onth k lcs) eqn:Hyg1;try easy.
                    eapply Forall2_prop_l in H11;try exact Hyg1;tac_sanitize.
                    eapply Forall2_prop_l in H8;try exact H3;tac_sanitize.
                    eapply Forall2_prop_r in H16;try exact H4;tac_sanitize.
                    rewrite Hyg in H11;easy.
                }
            }   
        }
        {
            red in Htyp;destr_hyps.
            inversion H;subst.
            pinversion Hprojp;subst;try easy;try apply proj_mon.
            {

                inversion Hprojhp;subst;[
                exfalso;apply H2; apply decidable_helper.triv_pt_q;easy
                |exfalso;apply H2; apply decidable_helper.triv_pt_p;easy |]
                .
                eapply Forall_prop in H17;try exact H16.
                tac_sanitize.
                eapply Forall2_prop_l in H11;try exact H16.
                tac_sanitize.
                eapply Forall2_prop_r in H8;try exact H5;tac_sanitize.
                eapply Forall_prop in IH;try exact H5.
                tac_sanitize.
                eapply H8 with (gs:=gs) (g:=x5);try easy.

                inversion Hwfgth;subst; eapply Forall_prop in H18;try exact H5; tac_sanitize;easy.

                eapply continuation_wfgC;try exact Hwfg;try exact H11.
                pfold. 

                constructor. intros;apply H2.
                Search isgPartsC onth. eapply part_parent;try exact H11;try easy.
                red. (repeat split);try easy.
                intros.
                eapply H0. 
                eapply ha_sendr;try exact H5;try easy.
                1-2:red;intros;exfalso;subst;apply H0; constructor.
            }
            {
                inversion Hprojhp;subst;try easy.
                eapply Forall_prop in H22;try exact H21;tac_sanitize.
                eapply Forall2_prop_l in H16;try exact H21;tac_sanitize.
                eapply Forall2_prop_r in H8;try exact H4;tac_sanitize.
                eapply Forall_prop in IH;try exact H4;tac_sanitize.
                eapply H8 with (g:=x5) (gs:=gs);try easy.   
                {
                 inversion Hwfgth;subst.
                        eapply Forall_prop in H23;try exact H4. 
                        tac_sanitize;easy.    
                }
                {
                    eapply continuation_wfgC;try exact H16;try exact Hwfg.   
                }
                {
                      eapply Forall2_prop_r in H13; try exact H16;tac_sanitize.
                  
                    eapply merge_inv_ss in H19;try exact H14;subst.
                    destruct H20;try easy.
                }
                {
                    red.
                    (repeat split);try easy. intros.
                    apply H0. econstructor;try exact H4;try easy.   
                    1-2:red;intros;exfalso;subst;apply H0; constructor.   
                }
            }
        }
    }
Qed.

Print typ_p_recv_ltth.

Lemma extendLis_length {A:Type}: forall (a b: option A) n, Datatypes.length (extendLis n a)=
Datatypes.length (extendLis n b).
Proof.
    induction n;crush.
Qed.

Definition forall_projable gs :=Forall (fun u=>u=None \/ exists g, u=Some g /\ projectableA g) gs.
Definition forall_wfg gs :=Forall (fun u=>u=None \/ exists g, u=Some g /\ wfgC g) gs.

Lemma project_list: forall gs p q, Forall (fun u=> u=None\/ exists ys, u=Some (gtt_send p q ys)) gs ->
forall_projable gs->
forall_wfg gs ->
exists ls, Forall2 (fun u v => u=None /\ v=None \/ exists g t, u=Some g /\ v=Some t /\ projectionC g q t) gs ls
/\ Forall (fun u=> u=None \/ exists ys, u=Some (ltt_recv p ys)) ls.
Proof.
    intros * Hgs Hproj Hwfg.
    induction gs.
    {
        exists []. split;constructor.   
    }
    {
        inversion Hgs.
        inversion Hproj.
        inversion Hwfg.
        destruct a;subst.
        {
            tac_sanitize.
            specialize (IHgs H2 H6 H10);destr_hyps.
            repeat tac_sanitize.
            specialize (H5 q);destr_hyps.
            pinversion H1;subst;try apply proj_mon;try easy;
            [exfalso;apply H4;apply decidable_helper.triv_pt_q|];try easy.
            exists (Some (ltt_recv p ys) :: x0).
            split;constructor;try easy.
            {
                right. exists (gtt_send p q x) , (ltt_recv p ys);crush.
                pfold;easy.   
            }
            {
                right. exists ys. easy.   
            }
        }
        {
            specialize (IHgs H2 H6 H10);destr_hyps.
            exists (None::x).
            split;constructor;crush.   
        }   
    }
Qed.

Definition gttstepC_any g g':= exists p q ell, gttstepC g g' p q ell. 
Definition gttstepC_RT := clos_refl_trans gtt gttstepC_any.

Lemma extend_onth_inv {A:Type}: forall n (a:A) b n', onth n (extendLis n' (Some a))=Some b ->
n=n'.
Proof.
    intros.
    generalize dependent n.
    induction n'.
    {
        simpl.
        destruct n;crush.
        rewrite onth_nil in H;easy.   
    }
    {
        destruct n.
        {
            simpl;intros;try easy.   
        }
        {
            intros.
            simpl in H.
            eapply IHn' in H.
            f_equal;easy.
        }   
    }
Qed.

Lemma isMergeCtx_onth_inv : forall gss n  gs x, isMergeCtx gs gss -> 
onth n gs= Some x -> exists k a, onth k gss=Some a /\
onth n a = Some x.
Proof.
    induction gss.
    {
        intros.
        inversion H.   
    }
    {
        intros * Hmerge Honth.
        inversion Hmerge;subst;
        [exists 0, gs;crush |
        
        eapply IHgss in Honth;try easy;
        destr_hyps;
        exists (S x0), (x1);crush|].
        eapply triple_sum_trilemma in H2;try exact Honth.
        destruct H2.
        {
            eapply IHgss in H3;try exact H. destr_hyps.
            exists (S x0), x1. crush.
        }
        {
            exists 0. exists t';crush.
        }
    }
Qed. 


Lemma grafting_means_path : forall gx gs g g' n, 
typ_gtth gs gx g ->
usedCtx gs gx ->
wfgC g ->
onth n gs= Some g' ->
    gttstepC_RT g g'.
Proof.
    induction gx using gtth_ind_ref.
    {
        intros * Hgraft Hused Hwfg Honth.
        inversion Hgraft;inversion Hused;subst.
        destruct (Nat.eq_dec n0 n);subst.
         
        try rewrite extendExtract in *. inversion Honth;inversion H1;subst.
        eapply rt_refl.

        eapply extend_onth_inv in Honth;subst;try easy.
    }
    {
        
        intros * Hgraft Hused Hwfg Honth.
        
        inversion Hused;subst.
        inversion Hgraft;subst.
        eapply isMergeCtx_onth_inv in H3 as Hmerge_onth;try exact Honth;destr_hyps.
        rename x0 into gs'.
        eapply Forall2_prop_r in H5;try exact H0.
        tac_sanitize.
        eapply Forall2_prop_r in H8;try exact H5;tac_sanitize.
        rename x1 into gs', x4 into s, x5 into gh, x6 into gc.
        eapply Forall_prop in H;try exact H5;tac_sanitize.
        assert(Hstep: gttstepC (gtt_send p q ys) gc p q x).
        {
            pfold;econstructor.
            apply wfgC_triv in Hwfg;try easy.
            symmetry;exact H8.   
        }
        assert(Hrest: gttstepC_RT gc g').
        {
            eapply H2 with (gs:=gs') (n:=n);try easy.
            eapply decidable_helper.typh_with_less;try exact H9;try easy.
            eapply mergeCtx_onth_subset;try exact H3;try exact H0.
            eapply continuation_wfgC;try exact H8;try exact Hwfg.
        }
        eapply rt_trans;try exact Hrest.
        eapply rt_step;red;exists p, q, x;easy.
    }
Qed.   

Lemma gttstep_preserves_wfg: forall g g', wfgC g -> projectableA g -> 
gttstepC_RT g g' -> wfgC g' /\ projectableA g'.
Proof.
    intros.
    induction H1. red in H1. destr_hyps.
    split;[eapply wfgC_after_step| eapply projectable_after_step];try exact H1;try easy.
    all:crush.
Qed.
Lemma wfg_list_by_grafting: forall gs gx g,typ_gtth gs gx g ->
wfgC g -> projectableA g -> usedCtx gs gx ->
forall_projable gs /\ forall_wfg gs.
Proof. 
    intros.
    split;eapply Forall_forall;
    intros;destruct x;crush;eapply in_some_implies_onth in H3;destr_hyps;
    right;eapply grafting_means_path in H3;try exact H;try easy;exists g0;crush;
    try apply gttstep_preserves_wfg in H3;try easy.
Qed.

Lemma gttstep_reflects_part : forall g g' r, wfgC g -> projectableA g -> isgPartsC r g' -> gttstepC_RT g g'->
isgPartsC r g.
Proof.
    intros * Hwfg Hproj Hisparts Hstep.
    induction Hstep;crush;
    [red in H;destr_hyps;
    eapply part_after_step_redux;try exact H|];crush.
    eapply H0;eapply IHHstep2;try easy;eapply gttstep_preserves_wfg; try exact Hstep1;try easy.
Qed.

Lemma projectable_onth: forall xs p q k s a, wfgC (gtt_send p q xs) -> projectableA (gtt_send p q xs) ->
onth k xs =Some (s,a) -> projectableA a.
Proof.
    intros.
    eapply projectable_after_step with (g:=(gtt_send p q xs)) (p:=p) (q:=q) (ell:=k);try easy.
    pfold. econstructor;[apply wfgC_triv in H;easy|symmetry;exact H1].
Qed.

Lemma Forall_onth_generic {A:Type}: forall (gcs1:list (option A)), 
Forall (fun u=> u=None \/ exists k, onth k gcs1=u) gcs1.
Proof.
    induction gcs1;constructor.
    destruct a; [right; exists  0 | left ];crush.
    set (P:=(fun u  =>
u = None \/ (exists k : opt_lbl, onth k gcs1 = u))).
    eapply Forall_impl with (P:=P); unfold P in *;crush.
    destruct (onth x gcs1) eqn:Hyg;[
    eapply Forall_prop with (l:=x) (p:=a0) in IHgcs1|];crush.
    right; exists (S x0); crush.
Qed.


Definition opt_list_subset {A:Type} (gs' gs :list (option A)) := 
Forall2R  (fun u v : option A => u = None \/ u = v) gs' gs.

Lemma projectionH_with_more_gs : forall gx gs' gs  p ls lx, 
projectionH  gx gs' p lx ls -> opt_list_subset gs' gs -> projectionH gx gs p lx ls.
Proof.
    induction gx using gtth_ind_ref.
    {
        intros.
        inversion H;subst.
        red in H0;eapply Forall2R_prop in H0;try exact H2;destr_hyps.
        destruct H1;try easy;subst.
        
        econstructor;try exact H4;crush.
    }
    {
        intros. inversion H0;subst.
        {
            econstructor;try easy.
            eapply Forall2_forall.
            tac_forall_to_length;crush.
            intros.
            destruct (onth k xs) eqn:Hyg.
            {
                right.
                eapply Forall_prop in H as IH;try exact Hyg;tac_sanitize.
                
                eapply Forall2_prop_r in H10 as Heqpr;try exact Hyg;tac_sanitize.
                exists x2,x3,x4.
                repeat split;try easy.
                eapply H3;try easy H6;try exact H1;easy.
            }   
            {
                destruct (onth k ys) eqn:Hyg'.
                eapply Forall2_prop_l in H10 as Heqpr;try exact Hyg'; tac_sanitize;crush.
                left. tauto.
            }
        }
        {
            econstructor;try easy.
            eapply Forall2_forall.
            tac_forall_to_length;crush.
            intros.
            destruct (onth k xs) eqn:Hyg.
            {
                right.
                eapply Forall_prop in H as IH;try exact Hyg;tac_sanitize.
                
                eapply Forall2_prop_r in H10 as Heqpr;try exact Hyg;tac_sanitize.
                exists x2,x3,x4.
                repeat split;try easy.
                eapply H3;try easy H6;try exact H1;easy.
            }   
            {
                destruct (onth k ys) eqn:Hyg'.
                eapply Forall2_prop_l in H10 as Heqpr;try exact Hyg'; tac_sanitize;crush.
                left. tauto.
            }
        }
        {
            eapply projectionH_cont with (ys:=ys) (k:=k) (twt:=twt);try easy.
            eapply Forall2_forall .
            
            tac_forall_to_length;crush.
            rename k into ksl.
            intros.
            destruct (onth k xs) eqn:Hyg.
            {
                right.
                eapply Forall_prop in H as IH;try exact Hyg;tac_sanitize.
                
                eapply Forall2_prop_r in H8 as Heqpr;try exact Hyg;tac_sanitize.
                eapply Forall_prop in H14;try exact H9;tac_sanitize.
                
                exists x2,x3,x.
                repeat split;try easy.
                eapply H3;try easy H6;try exact H1;easy.
            }   
            {
                destruct (onth k ys) eqn:Hyg'.
                eapply Forall2_prop_l in H8 as Heqpr;try exact Hyg'; tac_sanitize;crush.
                left. tauto.
            }
        }
        
    }
Qed.
 

(*ls is a superset of projlist gs*)
Definition is_proj_list_subset gs q ls := Forall2R (fun u v => u=None  \/ exists g t, u=Some g /\ v=Some t /\ projectionC g q t) gs ls.
 
Ltac subtac_wfgth_by_onth := match goal with 
                            [ Hwfgth : wfgtth (gtth_send ?p ?q ?xs),
                            Honthkxs : onth ?k ?xs = Some (_,?x)
                            |- wfgtth ?x] => inversion Hwfgth;subst;
                            match goal with [Hfa: Forall _ ?xs |- _] =>
                            eapply Forall_prop in Hfa;try exact Honthkxs;tac_sanitize;easy end
                            end.
            
            

        Ltac subtac_projable_by_onth := match goal with 
            [ Hprojable : projectableA (gtt_send ?p ?q ?xs),
            Honthys : onth ?k ?xs = Some (?s, ?g1)
            |- projectableA ?g1] => 
            eapply projectable_onth;try exact Hprojable;try exact Honthys;easy end.                            
        
         Ltac subtac_typh_with_less := match goal with 
                [Hgraft_g': typ_gtth ?gs ?gh ?g',
                Hmergesubs : Forall2R (fun u v : option gtt => u = None \/ u = v) ?gs' ?gs,
                Hused: usedCtx ?gs' ?gh
                |- typ_gtth ?gs' ?gh ?g'] => eapply decidable_helper.typh_with_less;
                try exact Hgraft_g';try easy end.

        Ltac subtac_wfg_by_onth :=match goal with [Hwfg : wfgC (gtt_send ?p ?q ?xs),
            Honthys : onth ?k ?xs = Some (?s, ?g1)
            |- wfgC ?g1] => 
            eapply continuation_wfgC;try exact Hwfg;try exact Honthys;easy end.

        Ltac subtac_ishparts_by_onth := match goal with 
        [ Honthkxs : onth ?k ?xs = Some (?s, ?gh),
        Hishparts: ishParts ?p0 (gtth_send ?p ?q ?xs) -> False
        |- ishParts ?p0 ?gh -> False] => 
        intros;apply inequality_by_not_ishparts in Hishparts as Hpp; apply Hishparts;eapply ha_sendr;try exact Honthkxs;try easy
        end.


Lemma typ_gtth_means_slist_gs : forall gx gs g, 
wfgtth gx ->
typ_gtth gs gx g -> exists k a, onth k gs = Some a.
Proof.
    induction gx using gtth_ind_ref.
    {
        intros * Hwfg Htyp.
    
        inversion Htyp;subst;exists n, g;easy.
    }
    {
        intros * Hwfg Htyp.
    
        inversion Hwfg;subst;eapply slist_implies_some in H2;destr_hyps.
        inversion Htyp;subst. eapply Forall2_prop_r in H8;try exact H0;tac_sanitize. 
        
        eapply Forall_prop in H;try exact H5;try exact H0;tac_sanitize;
        eapply H1;try subtac_wfgth_by_onth;try exact H5.
    }
Qed.
Lemma local_graft_send : forall gx gs p q g ls,
typ_gtth gs gx g -> wfgC g -> wfgtth gx ->
projectableA g ->
(ishParts p gx -> False) ->
Forall (fun u=> u=None\/ exists ys, u=Some (gtt_send p q ys
)) gs -> usedCtx gs gx -> 
is_proj_list_subset gs q ls -> 
exists lx , projectionH gx gs q lx ls.
Proof.
    induction gx using gtth_ind_ref.
    {
        intros * Htyp Hwfg Hwfgth Hprojable  Hishparts Hresgraft Hused Hprojlist.
        specialize (Hprojable q) as Hprojq. destr_hyps. rename x into Tq.
        exists (ltth_hol n).
        
        inversion Hused;subst.
        eapply Forall_prop in Hresgraft;[| rewrite extendExtract;reflexivity].
        tac_sanitize.
        inversion Htyp;subst. rewrite extendExtract in H2;inversion H2;subst.
        pinversion H;try apply proj_mon;subst;try easy.
        {
            exfalso;apply H0;apply decidable_helper.triv_pt_q;try easy.   
        }
        eapply Forall2R_prop in Hprojlist;try (rewrite extendExtract;reflexivity).
        tac_sanitize.
        econstructor;try exact H3;try exact H6.
        rewrite extendExtract;easy.
    }
    {
         
        intros * Htyp Hwfg Hwfgth Hprojable  Hishparts Hresgraft Hused Hprojlist.
        red in Hprojlist.
        inversion Htyp;subst;rename H5 into Hslist_xs;rename H6 into Hgraft_fa2.
        specialize (Hprojable q0) as Hprojq0. destr_hyps. rename x into Tq, H0 into Hprojq0.
        pinversion Hprojq0;try apply proj_mon;subst.
        {
            exfalso;apply H0.   
            assert(exists k u, onth k gs = Some u) by 
            (eapply typ_gtth_means_slist_gs;try exact Htyp;try easy).
            destr_hyps.
            eapply Forall_prop in Hresgraft;try exact H1;
            tac_sanitize.
            
            eapply gttstep_reflects_part with (g':=(gtt_send p0 q0 x1));try easy.
            apply decidable_helper.triv_pt_q;try easy.
            eapply wfg_list_by_grafting in Hused as Hforalls;try exact Hwfg;try easy.
            destr_hyps. eapply Forall_prop in H3;try exact H1;tac_sanitize;easy.
            eapply grafting_means_path;try exact H1;try exact Htyp;try easy.
        }
         1-2:   assert(create_lx: forall xs1
        (Hsubset: Forall (fun u=> u=None \/ exists k, onth k xs=u) xs1),
        exists lx,
            Forall2
(fun (u : option (sort * gtth)) (v : option (sort * ltth)) =>
u = None /\ v = None \/
(exists (s : sort) (g0 : gtth) (t : ltth),
u = Some (s, g0) /\ v = Some (s, t) /\ projectionH g0 gs q0 t ls)) xs1 lx
            ) by
                (
                induction xs1;[intros;exists [];constructor|];
                    intros;
                    inversion Hsubset;subst;rename H2 into Hdil_a, 
                    H4 into Hsubset_ind;
                    destruct a; [|
                        specialize (IHxs1 Hsubset_ind);
                        destr_hyps;
                        exists (None::x);
                        constructor;crush];
                    
                        destruct Hdil_a;try easy;destr_hyps;
                        rename x into k,  H0 into Honthkxs;
                        eapply Forall_prop in H;try exact Honthkxs;
                        tac_sanitize;
                        rename H0 into IH1;
                        eapply Forall2_prop_r in Hgraft_fa2;try exact Honthkxs;tac_sanitize;
                        rename H1 into Honthys, H2 into Hgraft_g', x2 into s, x4 into g';
                        inversion Hused;subst;
                        eapply Forall2_prop_l in H5;try exact Honthkxs;tac_sanitize;
                        
                        eapply mergeCtx_onth_subset with (gs:=gs) in H0 as Hmergesubs;try easy;
                        assert(Hwfg2: wfgC g') by subtac_wfg_by_onth;
                        eapply IH1 with (p :=p0) (q:=q0) (gs:=x0)  in Hwfg2 as IH;try easy;
                        rename x0 into gs', x1 into s,x2 into gh;
                        try solve [subtac_projable_by_onth | subtac_wfgth_by_onth | 
                        subtac_typh_with_less | subtac_ishparts_by_onth | 
                            eapply Forall_subset with (gs:= gs);crush |
                            destr_hyps;
                            specialize (IHxs1 Hsubset_ind) as IHxs';
                            destr_hyps;
                            exists (Some (s,x)::x0);
                            constructor;try easy;
                            right; exists s, gh,x;
                            repeat split;try easy;
                            eapply projectionH_with_more_gs with (gs':=gs');
                            try exact H;try easy
                        |
                            red;
                            eapply Forall2_Forall;[tac_forall_to_length | ];
                            intros;
                            destruct (onth k0 gs') eqn:Hyg1;[right |left;easy];
                            eapply Forall2R_prop in Hmergesubs;try exact Hyg1;destr_hyps;
                            destruct H5;try easy;subst;symmetry in H5;
                            eapply Forall2R_prop in Hprojlist;try exact H5;tac_sanitize;
                            exists x0, x1; crush   
                        ]                    
                );
            specialize (create_lx xs (Forall_onth_generic xs)) as lx_gen;
            destruct lx_gen as [lx lxprop].
            exists (ltth_recv p lx); 
                constructor;try easy.
            exists (ltth_send q lx); 
                constructor;try easy.

        assert (create_lx: forall xs1
        (Hsubset: Forall (fun u=> u=None \/ exists k, onth k xs=u) xs1),
        exists lxs,
            Forall2
(fun (u : option (sort * gtth)) (v : option ltth) =>
u = None /\ v = None \/
(exists (s : sort) (g : gtth) (t0 : ltth),
u = Some (s, g) /\ v = Some t0 /\ projectionH g gs q0 t0
ls)) xs1 lxs /\
        Forall
        (fun u : option ltth =>
        u = None \/ (exists th : ltth, u = Some th /\
        typ_ltth th ls Tq)) lxs
            ).
            {
                induction xs1;[intros;exists [];split;constructor|].
                intros. inversion Hsubset;subst;rename H7 into Hsubsrest.
                destruct a.
                {
                    destruct H2;try easy; destruct H0 as [k Honthkxs].
                    eapply Forall2_prop_r in Hgraft_fa2;try exact Honthkxs;tac_sanitize.
                    eapply Forall2_prop_r in H9;try exact H2;tac_sanitize.
                    eapply Forall_prop in H;try exact Honthkxs;
                    tac_sanitize.
                    rename x0 into gh', x into s, x4 into g', x5 into twt.
                    inversion Hused;subst.
                    eapply Forall2_prop_l in H14;try exact Honthkxs;tac_sanitize.
                    rename x2 into gh', x0 into gs',x1 into s.
                    eapply mergeCtx_onth_subset in H1;try exact H12;try easy.
                    Check mergeCtx_onth_subset.
                    assert(Hwfg2: wfgC g') by subtac_wfg_by_onth.
                    eapply H0 with (gs:=gs') (q:=q0) (ls:=ls) (p:=p0) in Hwfg2;try easy;
                    try solve [subtac_ishparts_by_onth | subtac_projable_by_onth | subtac_wfgth_by_onth 
                    | subtac_typh_with_less | 
                        eapply Forall_subset in Hresgraft;try exact H1;try auto].
                    {
                        destruct Hwfg2 as [lxh Hlxh].
                        specialize (IHxs1 Hsubsrest) as Hst;destruct Hst as [lxrest [Hrest1 Hrest2]].
                        exists  (Some lxh::lxrest).
                        split;constructor;try easy.
                        right. exists s, gh', lxh;repeat split;try easy.
                        eapply projectionH_with_more_gs;try exact Hlxh;red;easy.
                        right. exists lxh;split;try easy.
                        assert(Tq=twt) by (eapply merge_inv_ss in H10;try exact H8;easy);subst. 
                        eapply projectionH_consistent with (g:=g') (p:=p0);try exact Hlxh;try easy;
                        try solve [subtac_wfg_by_onth | subtac_wfgth_by_onth | destruct H9;easy].
                        red;repeat split;try easy;try solve 
                        [subtac_typh_with_less | subtac_ishparts_by_onth].
                        eapply Forall_subset in Hresgraft;try exact H1;try auto.
                        eapply Forall_impl;try exact Hresgraft;intros;simpl in H; destruct H;subst;
                        try tauto;
                        destr_hyps;subst;right;exists q0, x;tauto.
                    }
                    {
                            red;
                            eapply Forall2_Forall;[tac_forall_to_length | ];
                            intros;
                            destruct (onth k0 gs') eqn:Hyg1;[right |left;easy].
                            eapply Forall2R_prop in H1;try exact Hyg1;destr_hyps.
                            destruct H11;try easy;subst; symmetry in H11;
                            eapply Forall2R_prop in Hprojlist;try exact H11;tac_sanitize;
                            exists x0, x1; crush.   
                    }
                }
                {
                    specialize (IHxs1 Hsubsrest);
                        destr_hyps;
                        exists (None::x);
                        constructor;crush.
                }
            }
            specialize (create_lx xs (Forall_onth_generic xs)) as lx_gen.
            destruct lx_gen as [lx [lx_prop1 lx_prop2]].
            assert(Hxssome: SList xs) by (inversion Hwfgth;easy).
            eapply slist_implies_some in Hxssome;destr_hyps.
            eapply Forall2_prop_r in lx_prop1 as Hf2;try exact H0;
            tac_sanitize.
            exists x4. eapply projectionH_cont with (twt:=Tq);try exact H7;try easy.
        
    }
Qed.

Lemma typ_gtth_means_wfgtth : forall gx gs g, typ_gtth gs gx g -> wfgtth gx.
Proof.
    induction gx using gtth_ind_ref.
    {
        intros; constructor.
    }
    {
        intros;constructor;[inversion H0;try easy |].
        
        eapply Forall_forall;intros;destruct x;try tauto; right;eapply in_some_implies_onth in H1;destr_hyps.
        inversion H0;subst. eapply Forall2_prop_r in H8;try exact H1;tac_sanitize.
        eapply Forall_prop in H;try exact H1;tac_sanitize; exists x0, x4;split;try easy;eapply H2;try exact H5.   
    } 
Qed.

Lemma local_types_corr_send : forall p q xs Tq g, 
wfgC g ->  projectionC g p (ltt_send q xs) ->
projectableA g ->
projectionC g q Tq -> exists ls ctx, typ_ltth ls ctx Tq.
Proof.
    intros * Hwfg Hprojp Hprojable Hprojq.
    assert(Hisparts:isgPartsC p g). {
        eapply projection_implies_part_send;try exact Hprojp.
    }
    eapply balanced_to_tree in Hisparts as Hgraft;try easy.
    destr_hyps.
    assert (Htypp: typ_p_gtth x0 x p g) by (red;crush).
    eapply typ_gtth_means_wfgtth in H as Hwfgth.
    eapply wfg_list_by_grafting in H as Hlist_wfg;try easy.
    eapply restricted_grafting_send with (ctx:=x) in H1;try exact Hprojp;try easy.
    eapply project_list in H1 as Hprojs;try easy.
    destruct Hprojs as [ls [?Hls ?Hls]].
    eapply local_graft_send with (ls:=ls) (p:=p) (q:=q) in H as Hgetlx;try easy;destr_hyps.
    eapply projectionH_consistent with (p:=p) in H3 as Hprojcons;try exact Hprojq;try easy.
    exists x1, ls;easy.
    
    red;eapply Forall2_Forall;[tac_forall_to_length|];intros;
    destruct (onth k x0) eqn:Hyg;try tauto;right.
    eapply Forall2_prop_r in Hls;try exact Hyg;tac_sanitize;exists x2, x3;auto.
Qed.

Lemma multigraft_proper_pref : forall p q g xs,
wfgC g -> projectableA g -> projectionC g p (ltt_send q xs) ->
(forall ys, ~ projectionC g q (ltt_recv p ys)) ->
exists gs_p ctx_p gs_q ctx_q,
typ_p_gtth gs_p ctx_p p g /\ typ_p_gtth gs_q ctx_q q g /\
is_tree_proper_prefix ctx_q ctx_p.
Proof.
    intros * Hwfg Hprojable Hprojp Hnprojq.
    assert(Hispartsp: isgPartsC p g) by admit.
    assert(Hispartsq: isgPartsC q g) by admit.
    eapply balanced_to_tree in Hispartsp as Hgraft;try easy.
    destr_hyps.
    rename x0 into gs_p, x into ctx_p.
    eapply restricted_grafting_send with (ctx:=ctx_p) (q:=q)  (g:=g) (xs:=xs) in H1 as Hrg; try easy.
    clear H1.
    rename H into Hgraftp, H2 into Husedctxp, H0 into Hishpartsp.
    eapply balanced_to_tree in Hispartsq as Hgraft;try easy.
    destr_hyps.
    rename x0 into gs_q, x into ctx_q, H into Hgraftq, H1 into Htri_q, H2 into Husedctxq, H0 into Hishpartsq. 
    exists gs_p, ctx_p, gs_q, ctx_q.
Admitted.


Section assoc_live_path_helpers.
Variables (gamma: tctx) (g: gtt).
Hypotheses (Hwfg: wfgC g) (Hwfltt: tctx_wf gamma) (Hassoc: assoc gamma g).
Variables (pth:Path).
Hypotheses (Hvalid_pth: valid_pathC pth) (Hfair: fair_path pth) (Hpath_start: path_starts_with gamma pth).
Check eventually.

Check typ_p_gtth.



End assoc_live_path_helpers.

Check local_types_corr_send.

Lemma multigrafting_lemma_send :
forall gamma',
tctxR gamma (lsend p q (Some s) ell) gamma' ->
exists gsp gsq ctx_p ctx_q, typ_p_gtth gsp ctx_p p g /\
typ_p_gtth gsq ctx_q q g /\ typ_p_ltth ls lctx q 



Lemma assoc_live_path_send : forall p q xsp, M.find p gamma= Some (ltt_send q xsp) ->
eventually (enabled (fun u=> exists xsq, M.find q u = Some (ltt_recv p xsq))) pth. 
Proof.
    intros * Hfindp.
    Search assoc M.find.
    constructor.
Admitted.

End assoc_live_path_helpers.
Lemma assoc_live_path:  forall gamma g, tctx_wf gamma -> wfgC g ->
assoc gamma g -> liveCtx gamma.
Proof.
    red;intros. red;intros. red;intros.
    pcofix CIH.
    pfold. constructor.
    red;intros.
    split.
    {
        intros.
        simpl in H5. inversion H5.
        Search "lem" "inv".   
        eapply lem_6_11a_tctx_send_invert in H6. destr_hyps.
        eapply assoc_live_path_send with (g:=g)  (pth:=(cocons (g', l) xs)) in H6;try easy.
        4:red.
    }
    
