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

(*
Lemma max_lt_compat: forall n m p q, n < m -> p< q -> Nat.max n p  < Nat.max m q.
Proof. crush. Qed.
Lemma proper_prefix_height_helper: forall p q s t xs ys, 
wfgtth (gtth_send p q xs) -> wfgtth (gtth_send s t ys) ->
Forall2 (fun u v => (u=None /\ v=None) \/ exists s g g', u=Some (s,g) /\ v=Some (s,g') /\ gtth_height g < gtth_height g') xs ys ->
gtth_height (gtth_send p q xs) < gtth_height (gtth_send s t ys).
Proof.
    intros.
    generalize dependent ys.
    generalize dependent xs.
    induction xs.
    {
        intros. inversion H;crush.   
    }
    {
        intros.
        destruct ys. inversion H1.

        inversion H1;subst.
        destruct a.
        {
            destruct H5;try easy.
            destr_hyps;subst. inversion H2;subst.
            simpl.
            eapply Arith_base.add_lt_mono_r_proj_l2r.
            eapply max_lt_compat. easy.
            assert (gtth_height (gtth_send p q xs) < gtth_height (gtth_send s t ys)).
            {
                eapply IHxs;try easy.   
            }
            crush.
        }
        {
            inversion H0;crush.
        }
    }
Qed.
*)
Lemma proper_prefix_height_le : forall gc gp, wfgtth gc -> wfgtth gp -> 
    is_tree_proper_prefix gc gp -> 
    gtth_height gc < gtth_height gp.
Proof.
    
Admitted.

Definition path_starts_with (gamma:tctx) (pt:Path):=
  match pt with 
  | cocons (a,b) _ => a=gamma
  | _ => False
  end.

Section assoc_live_path_helpers.
Variables (gamma: tctx) (g: gtt).
Hypotheses (Hwfg: wfgC g) (Hwfltt: tctx_wf gamma) (Hassoc: assoc gamma g).
Variables (pth:Path).
Hypotheses (Hvalid_pth: valid_pathC pth) (Hfair: fair_path pth) (Hpath_start: path_starts_with gamma pth).
Check eventually.

Check typ_p_gtth.

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
    
