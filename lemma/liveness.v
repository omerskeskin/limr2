(* From mathcomp Require Import ssreflect.seq all_ssreflect. *)
From Paco Require Import paco pacotac.
From SST Require Import src.expr src.header src.local CpdtTactics src.lcontext.
From SST Require Import src.global src.projection src.part  src.balanced src.merge src.wfltt src.gttreeh.
From SST Require Import lemma.projection lemma.projection_helper lemma.decidable lemma.liveness_helpers lemma.soundness.
From SST Require Import src.step lemma.step src.assoc lemma.completeness src.ltth src.path_props.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Init.Logic.
From Equations Require Import Equations.


Import ListNotations.

Inductive gtth_eq: gtth -> gtth -> Prop :=
    | gtth_eq_hol : forall n m, gtth_eq (gtth_hol n) (gtth_hol m)
    | gtth_eq_send : forall xs ys p q , 
    Forall2 (fun u v => (u=None /\ v=None) \/ (exists s g1 g2, u=Some (s,g1) /\ v=Some (s,g2) /\ gtth_eq g1 g2)) 
    xs ys ->
    gtth_eq (gtth_send p q xs) (gtth_send p q ys).


Lemma projectionH_ishparts: forall gs gx r p ls lx, 
wfgtth gx ->
(ishParts p gx -> False) -> projectionH gx gs r lx ls ->
(ishlParts p lx ->False).
Proof.
    intros *. revert gs r p ls lx. generalize dependent gx.
    induction gx using gtth_ind_ref.
    {
        intros. inversion H1;subst;inversion H2.
    }
    {
        intros * Hwfg Hishparts Hproj Hishlparts.
        inversion Hproj;subst.
        {
            assert(Hslist: SList xs) by (inversion Hwfg;try easy).
            inversion Hishlparts;subst;[exfalso;apply Hishparts;constructor |].
            eapply Forall2_prop_l in H8;try exact H4;tac_sanitize.
            eapply Forall_prop in H;try exact H1;tac_sanitize.
            eapply H0 with (p:=p0);try exact H6;try easy.
            subtac_wfgth_by_onth. subtac_ishparts_by_onth.
        }
        {
            
            assert(Hslist: SList xs) by (inversion Hwfg;try easy).
            inversion Hishlparts;subst;[exfalso;apply Hishparts;constructor |].
            eapply Forall2_prop_l in H8;try exact H4;tac_sanitize.
            eapply Forall_prop in H;try exact H1;tac_sanitize.
            eapply H0 with (p:=p0);try exact H6;try easy.
            subtac_wfgth_by_onth. subtac_ishparts_by_onth.
        }
        {
            eapply Forall2_prop_l in H6;try exact H11;tac_sanitize.
            
            eapply Forall_prop in H;try exact H1;tac_sanitize.
            eapply H0 with (p:=p0);try exact H6;try easy.
            subtac_wfgth_by_onth.
            subtac_ishparts_by_onth.   
        }   
    }
Qed.

Lemma proj_contains_q_implies_part_send : forall g p q xs,
wfgC g -> projectableA g ->
projectionC g p (ltt_send q xs) ->

isgPartsC p g/\ isgPartsC q g.
Proof.
    intros * Hwfg Hprojable Hproj.
    assert(Hispartsp : isgPartsC p g ) by
    (eapply projection_implies_part_send;try exact Hproj).
    eapply balanced_to_tree in Hispartsp as Hss;try exact Hwfg;destr_hyps.
    eapply restricted_grafting_send in H1;try exact H;try exact Hproj;try easy.
    split. eapply projection_implies_part_send;try exact Hproj.
    Search isgPartsC gttstepC_RT.
    eapply   typ_gtth_means_slist_gs in H as ?Ht;try easy; try eapply typ_gtth_means_wfgtth;try exact H.
    destr_hyps.
    eapply gttstep_reflects_part with (g':=x2);try easy.
    eapply Forall_prop in H1;try exact H3;destruct H1;try easy;destr_hyps;inversion H1;subst.
    eapply wfg_list_by_grafting in H;try easy;destr_hyps.
    red in H4. eapply Forall_prop in H4;try exact H3;tac_sanitize.
    apply decidable_helper.triv_pt_q;easy.
    eapply grafting_means_path;try exact H;try exact H3;easy.
Qed.


Lemma proj_contains_q_implies_part_recv : forall g p q xs,
wfgC g -> projectableA g ->
projectionC g p (ltt_recv q xs) ->

isgPartsC p g/\ isgPartsC q g.
Proof.
    intros * Hwfg Hprojable Hproj.
    assert(Hispartsp : isgPartsC p g ) by
    (eapply projection_implies_part_recv;try exact Hproj).
    eapply balanced_to_tree in Hispartsp as Hss;try exact Hwfg;destr_hyps.
    eapply restricted_grafting_recv in H1;try exact H;try exact Hproj;try easy.
    split;try easy.
    Search isgPartsC gttstepC_RT.
    eapply   typ_gtth_means_slist_gs in H as ?Ht;try easy; try eapply typ_gtth_means_wfgtth;try exact H.
    destr_hyps.
    eapply gttstep_reflects_part with (g':=x2);try easy.
    eapply Forall_prop in H1;try exact H3;destruct H1;try easy;destr_hyps;inversion H1;subst.
    eapply wfg_list_by_grafting in H;try easy;destr_hyps.
    red in H4. eapply Forall_prop in H4;try exact H3;tac_sanitize.
    apply decidable_helper.triv_pt_p;easy.
    eapply grafting_means_path;try exact H;try exact H3;easy.
Qed.

Lemma multigrafting_lemma_1 : forall  ctx_q p q g xs Tq gs_p gs_q ctx_p ,
wfgC g -> projectableA g -> projectionC g p (ltt_send q xs) ->
projectionC g q Tq -> typ_p_gtth gs_p ctx_p p g -> 
usedCtx gs_p ctx_p ->
typ_p_gtth gs_q ctx_q q g ->
usedCtx gs_q ctx_q -> gtth_eq ctx_p ctx_q -> exists ys, Tq =ltt_recv p ys.
Proof.
    induction ctx_q using gtth_ind_ref.
    {
        intros * Hwfg Hprojable Hprojp Hprojq Htypp Husedp Htypq Husedq Hgttheq.
        inversion Hgttheq;subst.
        destruct Htypp as [?Htypp [?Htypp ?Htypp]].
        destruct Htypq as [?Htypq [?Htypq ?Htypq]].
        inversion Htypp;inversion Htypq;subst.
        eapply restricted_grafting_send in Htypp;try exact Hprojp;try easy.
        eapply Forall_prop in Htypp;try exact H1;tac_sanitize.
        pinversion Hprojq;try apply proj_mon;subst;
        [
        exfalso;apply H;apply decidable_helper.triv_pt_q |
        exists ys |
        eapply wfgC_triv in Hwfg|
        ];easy.
    }
    {
        
        intros * Hwfg Hprojable Hprojp Hprojq Htypp Husedp Htypq Husedq Hgttheq.
        Search projectionC isgPartsC ltt_send.
        assert (Hispartsp : isgPartsC p0 g) by (eapply proj_contains_q_implies_part_send in Hprojp;try easy).
        assert (Hispartsq : isgPartsC q0 g) by (eapply proj_contains_q_implies_part_send in Hprojp;try easy).
        
        inversion Hgttheq;subst.
        destruct Htypp as [?Htypp [?Htypp ?Htypp]].
        destruct Htypq as [?Htypq [?Htypq ?Htypq]].
        rename H2 into Hgtth_eqfa2, xs into xsq, xs1 into xsp.
        
        eapply restricted_grafting_send in Htypp as Hrg;try exact Hprojp;try easy.
        pinversion Hprojq;try apply proj_mon;subst;try easy.
        {
            inversion Htypq;subst.
            exfalso;apply Htypq0;apply ha_sendq.   
        }
        {
            inversion Htypq;subst. 
            exfalso;apply Htypq0;apply ha_sendp.     
        }
        {
            inversion Htypq;subst.
            eapply merge_slist in H5 as Hmergeslist.
            eapply slist_implies_some in Hmergeslist;destr_hyps.
            eapply Forall2_prop_l in H4;try exact H6;tac_sanitize.
            eapply Forall2_prop_l in H14;try exact H7;tac_sanitize.
            eapply Forall_prop in H;try exact H8;tac_sanitize.
            eapply Forall2_prop_l in Hgtth_eqfa2;try exact H8;tac_sanitize.
            eapply merge_inv_ss in H6;try exact H5;try easy;subst.
            destruct H10;try easy.
            inversion Husedq;subst.
            inversion Husedp;subst.
            eapply Forall2_prop_l in H17;try exact H8;tac_sanitize.
            eapply Forall2_prop_l in H19;try exact H11;tac_sanitize.
            rename x1 into gs_q', x3 into gs_p', x4 into ghq, x into k,
            x8 into ghp, x7 into s, x6 into g'.
            eapply mergeCtx_onth_subset in H10;try exact H15.
            eapply mergeCtx_onth_subset in H13;try exact H16.
            eapply H4 with (p:=p0) (xs:=xs0) (ctx_p:=ghp) (gs_p:=gs_p') (gs_q:=gs_q') in H;try easy.
            subtac_wfg_by_onth. subtac_projable_by_onth.
            {
                pinversion Hprojp;subst;try apply proj_mon.   
                exfalso;apply Htypq0;apply ha_sendq.

                eapply Forall2_prop_r in H27;try exact H7;tac_sanitize.
                destruct H25;try easy.
                eapply merge_inv_ss in H28;try exact H20;subst;easy.
            }
            {
                red;repeat split.   
                inversion Htypp;subst.
                eapply Forall2_prop_l in H24;try exact H7;tac_sanitize.
                rewrite H18 in H11;inversion H11;subst;clear H11.
                eapply decidable_helper.typh_with_less;try exact H22;try easy.
                subtac_ishparts_by_onth.
                eapply Forall_subset;try exact H10;try exact Htypp1;try easy;auto.
            }
            {
                red;repeat split.   
                inversion Htypq;subst.
                eapply Forall2_prop_l in H24;try exact H7;tac_sanitize.
                rewrite H18 in H8;inversion H8;subst;clear H8.
                eapply decidable_helper.typh_with_less;try exact H22;try easy.
                subtac_ishparts_by_onth.
                eapply Forall_subset;try exact H13;try exact Htypq1;try easy;auto.
            }
        }
    }
Qed.

Ltac subtac_triv_isparts_false := match goal with 
    [H: ishParts ?p (gtth_send ?p ?q ?xs) -> False|- _] => exfalso; apply H;apply ha_sendp
    | [H: ishParts ?q (gtth_send ?p ?q ?xs) -> False|- _] => exfalso; apply H;apply ha_sendq
    | [H: isgPartsC ?p (gtt_send ?p ?q ?xs) -> False|- _] => exfalso; apply H;apply decidable_helper.triv_pt_p;try easy
    | [H: isgPartsC ?q (gtt_send ?p ?q ?xs) -> False|- _] => exfalso; apply H;apply decidable_helper.triv_pt_q;try easy
    end.

Lemma multigrafting_lemma_2 : forall  ctx_p p q g xs ys gs_p gs_q ctx_q ,
wfgC g -> projectableA g -> projectionC g p (ltt_send q xs) ->
projectionC g q (ltt_recv p ys) -> typ_p_gtth gs_p ctx_p p g -> 
usedCtx gs_p ctx_p ->
typ_p_gtth gs_q ctx_q q g ->
usedCtx gs_q ctx_q -> gtth_eq ctx_p ctx_q.
Proof.
    induction ctx_p using gtth_ind_ref.
    {
        intros * Hwfg Hprojable Hprojp Hprojq Htypp Husedp Htypq Husedq.
        destruct Htypp as [?Htypp [?Htypp ?Htypp]].
        destruct Htypq as [?Htypq [?Htypq ?Htypq]].
        inversion Htypp;subst.
        inversion Htypq;subst.
        constructor.
        {   
            eapply restricted_grafting_send in Htypp as Hrg;try exact Hprojp;try easy.
            eapply Forall_prop in Hrg;try exact H1;tac_sanitize.
            exfalso;apply Htypq0;apply ha_sendq.   
        }
    }
    {
        intros * Hwfg Hprojable Hprojp Hprojq Htypp Husedp Htypq Husedq.
        destruct Htypp as [?Htypp [?Htypp ?Htypp]].
        destruct Htypq as [?Htypq [?Htypq ?Htypq]].
        inversion Htypp;subst.
        inversion Htypq;subst.
        eapply Forall_prop in Htypq1;try exact H0;destruct Htypq1;try easy;destr_hyps.
        destruct H1;[|destruct H1].
        {
            inversion H1;subst.
            pinversion Hprojq;try apply proj_mon;subst;try easy.   
        }
        {
            inversion H1;subst.
            pinversion Hprojq;try apply proj_mon;subst;try easy; subtac_triv_isparts_false.           
        }
        {
         inversion H1.   
        }
        {
            constructor.
            eapply Forall2_forall;[tac_forall_to_length|].
            intros;destruct (onth k xs) eqn:Hyg.
            right. 
            eapply Forall_prop in H;try exact Hyg;tac_sanitize.
            eapply Forall2_prop_r in H6;try exact Hyg; tac_sanitize.
            eapply Forall2_prop_l in H8;try exact H2;tac_sanitize.
            exists x0, x3, x1;repeat split;try easy.
            inversion Husedp;subst.
            inversion Husedq;subst.
            eapply Forall2_prop_l in H13;try exact H1;tac_sanitize.
            eapply Forall2_prop_l in H11;try exact Hyg;tac_sanitize.
            pinversion Hprojp;try apply proj_mon;subst;try subtac_triv_isparts_false.
            pinversion Hprojq;try apply proj_mon;subst;try subtac_triv_isparts_false.
            eapply Forall2_prop_r in H27;try exact H2;tac_sanitize.
            eapply Forall2_prop_r in H21;try exact H2;tac_sanitize.
            destruct H25;destruct H26;try easy.
            eapply merge_inv_ss in H14;try exact H28;subst.
            eapply merge_inv_ss in H21;try exact H22;subst.
            eapply H0 with (gs_p:=x0) (gs_q:=x2) (g:=x5);try exact H;try exact H11;try easy.
            subtac_wfg_by_onth. subtac_projable_by_onth.
            {
                red;repeat split;
                eapply mergeCtx_onth_subset in H8;try exact H9.
                eapply decidable_helper.typh_with_less;try exact H8;try easy.
                subtac_ishparts_by_onth.
                eapply Forall_subset;try exact H8;auto.
            }
            {
                red;repeat split;
                eapply mergeCtx_onth_subset in H6;try exact H10.
                eapply decidable_helper.typh_with_less;try exact H7; try easy.
                subtac_ishparts_by_onth.
                eapply Forall_subset;try exact H6;auto.
            }
            left. split;try easy.
            destruct (onth k xs1) eqn:Hyg2;try easy.
            eapply Forall2_prop_r in H8;try exact Hyg2;tac_sanitize.
            eapply Forall2_prop_l in H6;try exact H2;tac_sanitize.
            rewrite Hyg in H1;try easy.
        }
    }
Qed.


Ltac subtac_onth_typ Honthctxlist Hmerge:=
red;repeat split;
eapply mergeCtx_onth_subset in Honthctxlist as Hsubset;try exact Hmerge;
[

eapply decidable_helper.typh_with_less;try exact Hsubset;try easy
|
    subtac_ishparts_by_onth|
eapply Forall_subset;try exact Hsubset;auto].

Ltac subtac_onth_solver := try solve [subtac_ishparts_by_onth  | subtac_projable_by_onth | subtac_triv_isparts_false | subtac_wfg_by_onth | subtac_wfgth_by_onth].

Lemma multigrafting_lemma_3_send : forall  ctx_p p r q g xs ys gs_p gs_q ctx_q ,
wfgC g -> projectableA g -> projectionC g p (ltt_send q xs) ->
(projectionC g q (ltt_send r ys) \/ projectionC g q (ltt_recv r ys) ) -> r <> p -> typ_p_gtth gs_p ctx_p p g -> 
usedCtx gs_p ctx_p ->
typ_p_gtth gs_q ctx_q q g ->
usedCtx gs_q ctx_q -> is_tree_proper_prefix ctx_q ctx_p.
Proof.
    induction ctx_p using gtth_ind_ref.
    {
        intros * Hwfg Hprojable Hprojp Hprojq Hrnp Htypp Husedp Htypq Husedq.
        destruct Htypp as [?Htypp [?Htypp ?Htypp]].
        destruct Htypq as [?Htypq [?Htypq ?Htypq]].
        inversion Htypp;subst.
        inversion Htypq;subst.
        {
            eapply restricted_grafting_send in Hprojp;try exact Htypp;try easy.
            eapply Forall_prop in Hprojp;try exact H1.
            destruct Hprojp;try easy;destr_hyps; inversion H0;subst;clear H0.                
            destruct Hprojq as [Hprojq | Hprojq];
            [eapply restricted_grafting_send in Hprojq|
            eapply restricted_grafting_recv in Hprojq];
            try exact Htypq;try easy;
                eapply Forall_prop in Hprojq;try exact H;
                destruct Hprojq;try easy;destr_hyps;inversion H0;subst;clear H0;easy.
        }
        {
            eapply restricted_grafting_send in Hprojp;try exact Htypp;try easy.
            eapply Forall_prop in Hprojp;try exact H1.
            destruct Hprojp;try easy;destr_hyps; inversion H2;subst;clear H2.
            subtac_triv_isparts_false.                
        }
    }
    {
        intros * Hwfg Hprojable Hprojp Hprojq Hrnp Htypp Husedp Htypq Husedq.
        destruct Htypp as [?Htypp [?Htypp ?Htypp]].
        destruct Htypq as [?Htypq [?Htypq ?Htypq]].
        inversion Htypp;inversion Htypq;subst;[constructor |].
        inversion H11;subst;clear H11.
        constructor.
        eapply Forall2_forall.
        tac_forall_to_length.
        intros.
        destruct (onth k xs) eqn:Hyg.
        {
            right.
            eapply Forall2_prop_r in H6;try exact Hyg;tac_sanitize.   
            eapply Forall2_prop_l in H8;try exact H2;tac_sanitize.
            exists x3, x4, x1.
            repeat split;try easy.
            inversion Husedp;subst.
            inversion Husedq;subst.
            eapply Forall2_prop_l in H13;try exact H1;tac_sanitize.

            eapply Forall2_prop_l in H11;try exact Hyg;tac_sanitize.
            
            rename xs2 into ghsq,xs into ghsp, ys0 into gcs, x4 into s, x5 into g',
            x7 into ghp, x6 into ghq, x0 into gs_q', x3 into gs_p'.
            rename Hyg into Honthghsp, H2 into Honthgcs, H1 into Honthghsq.
            eapply Forall_prop in H as IH;try exact Honthghsp;tac_sanitize.
            rename x into s, x0 into ghp.
            eapply H1 with (g:=g') (gs_p:=gs_p') (gs_q:=gs_q') (p:=p0) (q:=q0)
            (xs:=xs0) (ys:=ys) (r:=r);try easy;
            try solve [subtac_onth_solver | subtac_onth_typ H9 H8 | subtac_onth_typ H4 H10]. 
            {
                pinversion Hprojp;try apply proj_mon;subst.  subtac_triv_isparts_false.
                eapply Forall2_prop_r in H20;try exact Honthgcs;tac_sanitize.
                destruct H18;try easy.
                eapply merge_inv_ss in H11;try exact H21;subst;easy. 
            }
            {
                destruct Hprojq as [Hprojq | Hprojq];
                 pinversion Hprojq;try apply proj_mon;subst;  try subtac_triv_isparts_false;
                eapply Forall2_prop_r in H20;try exact Honthgcs;tac_sanitize;
                destruct H18;try easy;
                eapply merge_inv_ss in H11;try exact H21;subst;auto.
                
            }
        }
        {
            left. destruct (onth k xs2) eqn:Hyg2;try auto.
            eapply Forall2_prop_r in H8;try exact Hyg2;tac_sanitize.
            eapply Forall2_prop_l in H6;try exact H2;tac_sanitize.
            rewrite H1 in Hyg;inversion Hyg;subst;easy.   
        }
    }
Qed.    

Lemma two_send_proj_impossible: forall   p q g xs ys ,
wfgC g -> projectableA g -> projectionC g p (ltt_send q xs) ->
projectionC g q (ltt_send p ys) -> False.
Proof.
Admitted.
Lemma multigrafting_lemma : forall  ctx_q p q g xs Tq gs_p gs_q ctx_p ,
wfgC g -> projectableA g -> projectionC g p (ltt_send q xs) ->
projectionC g q Tq -> typ_p_gtth gs_p ctx_p p g -> 
usedCtx gs_p ctx_p ->
typ_p_gtth gs_q ctx_q q g ->
usedCtx gs_q ctx_q ->
(is_tree_proper_prefix ctx_q ctx_p) \/ (gtth_eq ctx_p ctx_q).
Proof.
    intros. destruct Tq.
    {
        Search projectionC ltt_end isgPartsC. 
        eapply proj_contains_q_implies_part_send in H1;try easy;eapply pmergeCR in H2;
        try easy.
    }
    {
        destruct (Nat.eq_dec n p);subst.
        right.
        eapply multigrafting_lemma_2 with (gs_p:=gs_p) (gs_q:=gs_q) (p:=p) (q:=q); try exact H1;try exact H2;try easy.
        
        left.
        eapply multigrafting_lemma_3_send with (gs_p:=gs_p) (gs_q:=gs_q) (r:=n) (p:=p) (q:=q) (ys:=l);try exact H1;try easy.
        auto.
    }
    {
        destruct (Nat.eq_dec n p);subst.
        exfalso; eapply two_send_proj_impossible;try exact H1;try exact H2;try easy.
        
        left.
        eapply multigrafting_lemma_3_send with (gs_p:=gs_p) (gs_q:=gs_q) (r:=n) (p:=p) (q:=q) (ys:=l);try exact H1;try easy.
        auto.
    }
Qed.

Lemma eventually_if : 
forall (P Q : Path -> Prop) (xs:Path), eventually P xs -> 
(forall ys, P ys -> eventually Q ys) -> eventually Q xs.
Proof.
    intros.
    induction H;[crush|].

    constructor 2. easy.
Qed.

Check Path.

Check seq.foldr.
Search gtth_height.
Print gtth_height.

Definition xs_height_map_fn := fun u : option (sort * gtth) =>
match u with
| Some (_, x) => gtth_height x
| None => 0
end.
Lemma gtth_height_fold : forall p q xs, 
gtth_height (gtth_send p q xs) =
seq.foldr ( fun g a => Init.Nat.max (xs_height_map_fn g + 1) a) 1 xs.
Proof.
    intros * .
    induction xs.
    { 
        simpl;easy.   
    }
    {
        destruct a. 
        destruct p0. rewrite gtth_height_unfold_once_some.
        simpl seq.foldr. rewrite IHxs;easy.
        rewrite gtth_height_unfold_once_none. simpl seq.foldr.
        rewrite <- IHxs.
        rewrite Nat.max_0_l.
        
        destruct (gtth_height (gtth_send p q xs)) eqn:Hyg;try easy.
        eapply gtth_height_0_means_hol_general in Hyg;destr_hyps;easy.
    }
Qed.

Notation global_path := (coseq (gtt*label)) (only parsing).

Section global_path.


Definition global_path_vcriteria (x1 x2: gtt*label) :=
    match (x1,x2) with 
        | ((g1,lcomm p q ell),(g2,l2)) => gttstepC g1 g2 p q ell
        | _ =>False
    end.

Definition global_valid_pathC := valid_path_GC global_path_vcriteria.



Definition global_comm_enabled p q n g := exists xs ys, 
projectionC g p (ltt_send q xs)  /\ projectionC g q (ltt_recv p ys) /\
onth n xs <>None.

Definition enabled_global (P: gtt -> Prop) (xs: global_path) :=  
 match xs with
    | cocons (g, l) xs => P g
    | _                => False 
  end.

Definition headComm_global (p q: part) (pt: global_path): Prop :=
  match pt with
    | cocons (g, (lcomm a b n)) xs => if Nat.eq_dec p a then if Nat.eq_dec q b then True else False else False
    | _                          => False 
  end.

Definition fair_path_inner_global (pt: global_path): Prop :=
  forall p q n, 
  enabled_global (global_comm_enabled p q n) pt ->  
  eventually (headComm_global p q) pt.



Definition fair_path_global := alwaysCG fair_path_inner_global.

Definition global_label_enabled l g:= match l with 
    | lsend p q (Some s) n => exists xs g',
        projectionC g p  (ltt_send q xs) /\ onth n xs=Some (s,g')
    | lrecv p q (Some s) n => exists xs g',
        projectionC g p  (ltt_recv q xs) /\ onth n xs=Some (s,g')
    | lcomm p q n => exists xs ys, projectionC g p (ltt_send q xs)  /\ projectionC g q (ltt_recv p ys) /\
    onth n xs <>None
    | _ => False end.
    
Definition live_path_inner_global (pt: global_path) : Prop := forall p q s n, 
(enabled_global (global_label_enabled (lsend p q (Some s) n)) pt -> 
eventually (headComm_global p q) pt) /\
(enabled_global (global_label_enabled (lrecv p q (Some s) n)) pt -> 
eventually (headComm_global p q) pt).

Definition live_path_global := alwaysCG live_path_inner_global.

Definition all_fair_live_global (g:gtt) := forall l xs,  
  global_valid_pathC (cocons (g, l) xs) -> fair_path_global (cocons (g, l) xs) -> 
  live_path_global (cocons (g, l) xs).

Definition live_type_global (g: gtt) := forall g',
  gttstepRtc g g' -> all_fair_live_global g'.

End global_path.



Notation paired_path := (coseq (tctx*gtt*label)) (only parsing).

Definition paired_path_vcriteria (x1 x2: (tctx*gtt*label)) :=
    match (x1,x2) with 
        | ((t1, g1, lcomm p q ell),
        (t2,g2, l2)) => (gttstepC g1 g2 p q ell) 
        /\ tctxR t1  (lcomm p q ell) t2 /\  l2 = lcomm p q ell
        | _ =>False
    end.

Definition assoc_cond := fun u:paired_path => match u with 
    | (cocons (a,b,_) xs) => assoc a b
    | (conil) => True end.

Definition paired_path_assoc_cond := alwaysCG assoc_cond.

CoFixpoint proj1_paired_path (xs: paired_path) := match xs with 
    | conil => conil
    | cocons (t,g, c) xss => cocons (t,c) (proj1_paired_path xss) end.

CoFixpoint proj2_paired_path (xs: paired_path) := match xs with 
    | conil => conil
    | cocons (t,g,c) xss => cocons (g,c) (proj2_paired_path xss) end.

Definition paired_valid_pathC := valid_path_GC paired_path_vcriteria.

Lemma pair_valid_proj1_valid: forall xs, paired_valid_pathC xs -> (valid_local_path (proj1_paired_path xs)).
Proof.
    pcofix CIH.
    intros.
    destruct xs;
    [
    pfold;
    rewrite coseq_eq; simpl; constructor|].

    pfold.
    rewrite coseq_eq. destruct p as [[[t g] H] l].  simpl.
    destruct xs. rewrite (coseq_eq (proj1_paired_path _)). simpl.
    constructor.
    
    pinversion H0;try apply valid_path_mon;subst.
    destruct p as [[t' g'] l']. rewrite (coseq_eq (proj1_paired_path _));simpl.
    constructor.
    right.
    Check exist.
    Check proj1_paired_path.
    specialize (CIH (cocons (t',g',l') xs)) as CIH'.
    rewrite (coseq_eq (proj1_paired_path _)) in CIH';simpl in CIH';eapply CIH';
    easy.
    destruct l;try easy; red in H5;try easy.
Qed.

Lemma paired_assoc_head : forall t g l xs, 
paired_path_assoc_cond (cocons (t,g,l) xs) -> assoc t g.
Proof.
    intros.
    pinversion H;try apply always_mon;subst. simpl in H2;easy.
Qed.

Lemma proj2_live_proj1_live : forall xs, paired_valid_pathC xs -> 
paired_path_assoc_cond xs ->
live_path_global (proj2_paired_path xs) ->
live_path (proj1_paired_path xs).
Proof.
    pcofix CIH.
    intros * Hpvalid Hpassoc Hlive.
    destruct xs.
    {
        rewrite coseq_eq;simpl;pfold;constructor. red. intros.
        split;intros;
        inversion H.   
    }
    {
        destruct xs.
        {
            destruct p as [[t g]  l].
            assert(Hassoc: assoc t g) by  (eapply paired_assoc_head;try exact Hpassoc).
            
            rewrite (coseq_eq (proj1_paired_path _));simpl. 
            rewrite (coseq_eq (proj1_paired_path _));simpl. 
            rewrite (coseq_eq (proj2_paired_path _)) in Hlive;simpl in Hlive.
            
            pfold. constructor.
            { 
                pinversion Hlive;try apply always_mon;subst.
                red;split;intros.
                {     
                    unfold live_path_inner_global in H1.
                    specialize (H1 p q s n) .
                    destruct H1 as [?Hglob ?Hglob].
                    rewrite (coseq_eq) in H1;simpl in H1.
                }
            }
        }   
    }
    destruct xs.

    


Variant path_assoc (R:Path -> global_path -> Prop): Path -> global_path -> Prop :=
   | path_assoc_nil : path_assoc R conil conil
   | path_assoc_single : forall g gamma l1 l2, assoc gamma g -> 
   path_assoc R (cocons (gamma, l1) conil) (cocons (g, l2) conil)
   | path_assoc_xs : forall g gamma l xs ys, assoc gamma g ->
    R xs ys ->
   path_assoc R (cocons (gamma, l) xs) (cocons (g, l) ys)
   .
   
Definition path_assocC := paco2 path_assoc bot2.

Lemma path_assoc_by_assoc : forall gamma g ptl_tl  l, tctx_wf gamma ->
    wfgC g -> projectableA g -> assoc gamma g -> 
    valid_local_path (cocons (gamma, l) ptl_tl) ->
    exists ptg_tl, global_valid_pathC (cocons (g,l) ptg_tl) /\
    path_assocC (cocons (gamma,l) ptl_tl) (cocons (g,l) ptg_tl).
Proof.
    intros * Htctxwf Hwfg Hprojable Hassoc Hvalid.
    destruct ptl_tl.
    pinversion Hvalid;subst;try apply valid_path_mon.


Definition liveness_by_assoc: forall gamma g, tctx_wf gamma ->
    wfgC g -> projectableA g -> assoc gamma g -> live_type_global g ->
    liveCtx gamma.
Proof.
    intros * Htctxwf Hwfg Hprojable Hassoc Hlive.
    red in Hlive;red. intros;red;intros.
    

Definition head_proj_is_recv p q:=(
    fun (pt:global_path) => match pt with 
        | cocons (hd,l) tl => exists xs, 
        projectionC hd p (ltt_recv q xs)   
        | _ => False end
        ).
(*
Lemma assoc_live_helper_send_helper : typ_ltth lx ls Tq ->

*)

Lemma assoc_live_helper_send : 
forall  p q g l pt_tl xs, fair_path_global (cocons (g,l) pt_tl) -> 
global_valid_pathC (cocons (g,l) pt_tl) ->  wfgC g ->
projectableA g ->
projectionC g p (ltt_send q xs) -> eventually (
    head_proj_is_recv q p
        ) (cocons (g,l) pt_tl) .
Proof.
    intros * Hfair Hvalid Hwfg Hprojable Hprojp.
    assert(Hispartsp : isgPartsC p g /\ isgPartsC q g) by
    (eapply proj_contains_q_implies_part_send in Hprojp;try easy).
    destruct Hispartsp as [Hispartsp Hispartsq].
    eapply balanced_to_tree in Hispartsp as Hgraftp;try easy.
    destruct Hgraftp as [ctx_p [gs_p [?Hgraftp [?Hgraftp [?Hgraftp ?Hgraftp ]]]]].
    eapply typ_gtth_means_wfgtth in Hgraftp as Hwfgth.
    assert (Hgraftp_p : typ_p_gtth gs_p ctx_p p g)
    by (red;crush).   
    
    generalize dependent gs_p.
    generalize dependent g.
    generalize dependent  pt_tl.
    generalize dependent l.
    revert Hgraftp0 xs .
    generalize dependent p.
    generalize dependent q.
    revert Hwfgth.
    revert ctx_p.
    induction ctx_p using gtth_ind_by_height.
    {
        intros. rename H into IH.
        specialize (Hprojable q) as Ht.
        destruct Ht as [Tq Hprojq].
        eapply balanced_to_tree in Hispartsq as Hgraftq;try easy.
        destruct Hgraftq as [ctx_q [gs_q [?Hgraftq [?Hgraftq [?Hgraftq ?Hgraftq]]]]].
        eapply multigrafting_lemma with (q:=q) (p:=p) (gs_p:=gs_p) (ctx_p:=ctx_p)
        (gs_q:=gs_q) (ctx_q:=ctx_q) (Tq:=Tq) in Hprojp as Hmg;try easy.
        destruct Hmg.
        {
            Search typ_ltth.
            eapply local_types_corr_send_and_projH in Hgraftp_p as Hlt;try exact Hprojp;
            try exact Hprojq;try easy.
            destruct Hlt as [ls [lx [?Hlt [?Hlt ?Hlt]]]].

            Lemma assoc_live_helper_send_helper : typ_ltth lx ls Tq ->
            fair_path_global (cocons (g,l) pt_tl) -> 
            global_valid_pathC (cocons (g,l) pt_tl) ->  wfgC g ->
            projectableA g ->
            projectionC g p (ltt_send q xs) -> 
            eventually (head_proj_is_recv q p) (cocons (g,l) pt_tl)

            generalize dependent g.
            (*make another lemma*)
            generalize dependent 
            generalize dependent pt_tl.
            generalize dependent lx.
            induction lx using ltth_ind_ref.
            {
                intros.
                constructor 1. red.
                inversion Hlt;subst.
                red in Hlt1.
                eapply restricted_grafting_send in Hgraftp1;try exact Hprojp;
                try exact Hgraftp;try easy.
                eapply Forall2_prop_l in Hlt1;try exact H1;tac_sanitize.
                eapply Forall_prop in Hgraftp1;try exact H2.
                destruct Hgraftp1;try easy.
                destr_hyps.
                inversion H0;subst.
                pinversion H4;try apply proj_mon;subst;try tauto.
                eapply pmergeCR_s in Hprojq;try easy.
                exists ys;easy.
            }
            {
                rename H0 into IH2. intros.   
            }   
        }
        {
            eapply multigrafting_lemma_1 with (g:=g) (p:=p) (q:=q) (gs_p:=gs_p)
            (gs_q:=gs_q) (Tq:=Tq) (xs:=xs)
            in H;try easy.
            destruct H as [ys H];subst.
            destr_hyps. 
            econstructor. simpl. exists ys;easy.
        }
    }


Lemma assoc_live_helper_send : 
forall gamma p q g  l pt_tl xs, fair_path (cocons (gamma,l) pt_tl) -> 
valid_pathC (cocons (gamma,l) pt_tl) -> tctx_wf gamma -> wfgC g ->
assoc gamma g -> 
M.find p gamma= Some (ltt_send q xs) -> eventually (
    head_contains_q_recv p q
        ) (cocons (gamma,l) pt_tl) .
Proof.
    intros * Hfair Hvalid Htctxwf Hwfg Hassoc Hfindp.
    assert(Hprojable:projectableA g) by 
    (eapply assoc_implies_projectable;try exact Hassoc;easy).
    assert (Hispartsp : isgPartsC p g) by
    (eapply assoc_implies_part;try exact Hfindp;try easy).
    Print tac_use_assoc.   
    tac_use_assoc Hassoc p Hispartsp;destr_hyps.
    rewrite Hfindp in H;inversion H;subst;clear H.
    red in H0;destr_hyps. rename x into spty.
    eapply subtype_send_inv1 in H0;destr_hyps;subst.
    rename x into xsp.
    eapply proj_contains_q_implies_part_send in H as Hispartsq;try easy.
    destruct Hispartsq as [_  Hispartsq].
    eapply balanced_to_tree in Hispartsp as Hgraftp;try easy.
    destruct Hgraftp as [ctx_p [gs_p [?Hgraftp [?Hgraftp [?Hgraftp ?Hgraftp ]]]]].
    eapply typ_gtth_means_wfgtth in Hgraftp as Hwfgth.
    generalize dependent gs_p.
    generalize dependent g.
    generalize dependent gamma.
    generalize dependent  pt_tl.
    generalize dependent l.
    revert Hgraftp0 xs xsp.
    generalize dependent p.
    generalize dependent q.
    revert Hwfgth.
    revert ctx_p.
    induction ctx_p using gtth_ind_by_height.
    {
        intros. rename H into IH, H0 into Hprojp.
        specialize (Hprojable q) as Ht.
        destruct Ht as [Tq Hprojq].
        eapply balanced_to_tree in Hispartsq as Hgraftq;try easy.
        destruct Hgraftq as [ctx_q [gs_q [?Hgraftq [?Hgraftq [?Hgraftq ?Hgraftq]]]]].
        eapply multigrafting_lemma with (q:=q) (p:=p) (gs_p:=gs_p) (ctx_p:=ctx_p)
        (gs_q:=gs_q) (ctx_q:=ctx_q) (Tq:=Tq) in Hprojp as Hmg;try easy.
        destruct Hmg.
        {
            admit.   
        }
        {
            eapply multigrafting_lemma_1 with (g:=g) (p:=p) (q:=q) (gs_p:=gs_p)
            (gs_q:=gs_q) (Tq:=Tq) (xs:=xsp)
            in H;try easy.
            destruct H as [ys H];subst.
            tac_use_assoc Hassoc q Hispartsq.
            destr_hyps. red in H0. destr_hyps. eapply proj_inj in H0;try exact Hprojq;subst;try easy.
            eapply subtype_recv_inv2 in H1;destr_hyps;subst.
            econstructor. red;simpl. exists x0;easy.
        }
    }
    


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
        eapply lem_6_11a_tctx_send_invert in H6. destr_hyps.
        
        eapply assoc_live_path_send with (g:=g)  (pth:=(cocons (g', l) xs)) in H6;try easy.
        4:red.
    }
    
