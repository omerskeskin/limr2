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

Lemma SList_induction_principle {A:Type}: forall P : list (option A) -> Prop, (forall x, P [Some x]) -> 
(forall x xs, P xs -> P (x::xs)) -> (forall xs, SList xs -> P xs).
Proof.

    intros.
    induction xs.
    inversion H1.

    destruct a.
    {
        simpl in H1.
        destruct xs. eapply H.
        eapply H0;try easy.
        eapply IHxs;easy.
    }
    {
        eapply H0.
        simpl in H1. crush.
    }
Qed.

Lemma wfgtth_ind_ref_by_xs : forall P : part -> part -> list (option (sort*gtth)) -> Prop,
(forall p q xs, P p q [Some xs]) -> 
(forall p q x xs, P p q xs -> P  p q (x::xs)) ->
(forall p q xs, wfgtth (gtth_send p q xs) -> P p q xs).
Proof.
    intros.
    induction xs.
    inversion H1;subst. inversion H4.
    inversion H1;subst.
    destruct a;
    simpl in H4;destruct xs;
    solve [eapply H | inversion H4 |eapply H0;
        eapply IHxs;
        constructor;try easy;
        inversion H6;subst; easy].
Qed.


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
Section assoc_live_path_helpers.
Variables (gamma: tctx) (g: gtt).
Hypotheses (Hwfg: wfgC g) (Hwfltt: tctx_wf gamma) (Hassoc: assoc gamma g).
Variables (pth:Path).
Hypotheses (Hvalid_pth: valid_pathC pth) (Hfair: fair_path pth) (Hpath_start: path_starts_with gamma pth).
Check eventually.

Check typ_p_gtth.


Lemma local_types_corr_send : forall p q xs, M.find p gamma = Some (ltt_send q xs) ->
exists Tq, M.find q gamma =Some Tq /\ exists ls ctx, typ_p_recv_ltth ls ctx p Tq.
Proof.
    intros * Hfindp.
    assert (Hisparts: isgPartsC p g). (apply assoc_implies_part with (Tp:=ltt_send q xs) (gamma:=gamma));easy.
    
    eapply balanced_to_tree with (p:=p) in Hwfg as Hgraft;try easy.
    destr_hyps. rename x0 into gs, x into ctx.
    generalize dependent gamma.
    generalize dependent g.
    generalize dependent ctx.


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
    
