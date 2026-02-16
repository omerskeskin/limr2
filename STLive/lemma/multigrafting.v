From Paco Require Import paco pacotac.
From live_mpst.STBase Require Import src.expr src.header src.local
src.global src.projection src.part  src.balanced src.merge  src.gttreeh
lemma.projection lemma.projection_helper src.step lemma.step  lemma.decidable.
From live_mpst.STLive Require Import src.wfltt src.lcontext lemma.liveness_helpers lemma.soundness
src.assoc lemma.completeness src.ltth src.path_props.
From live_mpst.cpdtlib Require Import CpdtTactics.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Init.Logic.
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
    (*Search isgPartsC gttstepRtc.*)
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
    (*Search isgPartsC gttstepRtc.*)
    eapply   typ_gtth_means_slist_gs in H as ?Ht;try easy; try eapply typ_gtth_means_wfgtth;try exact H.
    destr_hyps.
    eapply gttstep_reflects_part with (g':=x2);try easy.
    eapply Forall_prop in H1;try exact H3;destruct H1;try easy;destr_hyps;inversion H1;subst.
    eapply wfg_list_by_grafting in H;try easy;destr_hyps.
    red in H4. eapply Forall_prop in H4;try exact H3;tac_sanitize.
    apply decidable_helper.triv_pt_p;easy.
    eapply grafting_means_path;try exact H;try exact H3;easy.
Qed.

Lemma multigrafting_lemma_1_send : forall  ctx_q p q g xs Tq gs_p gs_q ctx_p ,
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
        (*Search projectionC isgPartsC ltt_send.*)
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


Lemma multigrafting_lemma_1_recv : forall  ctx_q p q g xs Tq gs_p gs_q ctx_p ,
wfgC g -> projectableA g -> projectionC g p (ltt_recv q xs) ->
projectionC g q Tq -> typ_p_gtth gs_p ctx_p p g -> 
usedCtx gs_p ctx_p ->
typ_p_gtth gs_q ctx_q q g ->
usedCtx gs_q ctx_q -> gtth_eq ctx_p ctx_q -> exists ys, Tq =ltt_send p ys.
Proof.
    induction ctx_q using gtth_ind_ref.
    {
        intros * Hwfg Hprojable Hprojp Hprojq Htypp Husedp Htypq Husedq Hgttheq.
        inversion Hgttheq;subst.
        destruct Htypp as [?Htypp [?Htypp ?Htypp]].
        destruct Htypq as [?Htypq [?Htypq ?Htypq]].
        inversion Htypp;inversion Htypq;subst.
        eapply restricted_grafting_recv in Htypp;try exact Hprojp;try easy.
        eapply Forall_prop in Htypp;try exact H1;tac_sanitize.
        pinversion Hprojq;try apply proj_mon;subst;
        [
        exfalso;apply H;apply decidable_helper.triv_pt_p |
        eapply wfgC_triv in Hwfg | exists ys |
        
        ]; try easy. 
    }
    {
        
        intros * Hwfg Hprojable Hprojp Hprojq Htypp Husedp Htypq Husedq Hgttheq.
        (*Search projectionC isgPartsC ltt_send.*)
        assert (Hispartsp : isgPartsC p0 g) by (eapply proj_contains_q_implies_part_recv in Hprojp;try easy).
        assert (Hispartsq : isgPartsC q0 g) by (eapply proj_contains_q_implies_part_recv in Hprojp;try easy).
        
        inversion Hgttheq;subst.
        destruct Htypp as [?Htypp [?Htypp ?Htypp]].
        destruct Htypq as [?Htypq [?Htypq ?Htypq]].
        rename H2 into Hgtth_eqfa2, xs into xsq, xs1 into xsp.
        
        eapply restricted_grafting_recv in Htypp as Hrg;try exact Hprojp;try easy.
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
                exfalso;apply Htypq0;apply ha_sendp.

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


Lemma part_after_step_r_redux: forall g g' p q  ell r, wfgC g -> 
    projectableA g ->
    gttstepC g g' p q ell -> r <> p -> r <> q -> isgPartsC r g -> isgPartsC r g'.
    Proof.
        intros * Hwfg Hprojable Hstep Hne1 Hne2 Hisparts.
        specialize (Hprojable r) as Hprojr;destr_hyps. 
        eapply part_after_step_r;try exact Hisparts;try exact Hstep;try exact H;try easy.
        eapply wfgC_after_step;try exact Hstep;try easy.
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

Lemma multigrafting_lemma_3_recv : forall  ctx_p p r q g xs ys gs_p gs_q ctx_q ,
wfgC g -> projectableA g -> projectionC g p (ltt_recv q xs) ->
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
            eapply restricted_grafting_recv in Hprojp;try exact Htypp;try easy.
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
            eapply restricted_grafting_recv in Hprojp;try exact Htypp;try easy.
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
    intros * Hwfg Hprojable Hprojp Hprojq.
    eapply proj_contains_q_implies_part_send in Hprojp as Hisparts;try easy;
    destruct Hisparts as [Hispartsp Hispartsq].
    eapply balanced_to_tree in Hispartsp as Hgraft;try easy.
    destruct Hgraft as [ctx_p [gs_p [Htyp [Hishparts [Hfa Hused]]]]].
    generalize dependent g.
    revert Hused Hfa Hishparts xs ys.
    generalize dependent gs_p.
    induction ctx_p using gtth_ind_ref.
    {
        intros. inversion Htyp;subst. eapply Forall_prop in Hfa;try exact H1.
        destruct Hfa;try easy.
        destr_hyps.
        destruct H;[| destruct H];inversion H;subst;
        pinversion Hprojp;pinversion Hprojq;subst;try apply proj_mon;try easy.
    }
    {
        rename H into IH.
        intros.
        pinversion Hprojp;try apply proj_mon;subst;try easy;inversion Htyp;subst.
        subtac_triv_isparts_false.
        eapply slist_implies_some in H8;destr_hyps.
        eapply Forall_prop in IH;try exact H5;tac_sanitize.
        eapply Forall2_prop_r in H13;try exact H5;tac_sanitize.
        eapply Forall2_prop_r in H3;try exact H9;tac_sanitize.
        destruct H11;try easy.
        inversion Hused;subst.
        eapply Forall2_prop_l in H15;try exact H5;tac_sanitize.
        eapply mergeCtx_onth_subset in H13 as Hsubset;try exact H11;try easy.
        eapply merge_inv_ss in H8 as Hminv;try exact H4;subst.
        
        pinversion Hprojq;subst;try apply proj_mon;try easy.
        eapply Forall2_prop_r in H22;try exact H9;tac_sanitize.
        destruct H20;try easy.
        eapply merge_inv_ss in H23;try exact H15;subst. 
        
        assert (Hstep:gttstepC (gtt_send p1 q1 xs1) x4 p1 q1 x).
        {
            pfold. econstructor;try easy;try exact (eq_sym H9).   
        }
        eapply H7 with (g:=x4) (gs_p:=x3) (xs:=xs0) (ys:=ys);try easy;
        try subtac_onth_solver.
        eapply Forall_subset;try exact Hsubset;try easy;try tauto.
        
        eapply part_after_step_r_redux;try exact Hstep;try easy.
        eapply part_after_step_r_redux;try exact Hstep;try easy.
        eapply decidable_helper.typh_with_less;try exact Hsubset;try easy.
    }
Qed.

Lemma two_recv_proj_impossible: forall   p q g xs ys ,
wfgC g -> projectableA g -> projectionC g p (ltt_recv q xs) ->
projectionC g q (ltt_recv p ys) -> False.
Proof.
    intros * Hwfg Hprojable Hprojp Hprojq.
    eapply proj_contains_q_implies_part_recv in Hprojp as Hisparts;try easy;
    destruct Hisparts as [Hispartsp Hispartsq].
    eapply balanced_to_tree in Hispartsp as Hgraft;try easy.
    destruct Hgraft as [ctx_p [gs_p [Htyp [Hishparts [Hfa Hused]]]]].
    generalize dependent g.
    revert Hused Hfa Hishparts xs ys.
    generalize dependent gs_p.
    induction ctx_p using gtth_ind_ref.
    {
        intros. inversion Htyp;subst. eapply Forall_prop in Hfa;try exact H1.
        destruct Hfa;try easy.
        destr_hyps.
        destruct H;[| destruct H];inversion H;subst;
        pinversion Hprojp;pinversion Hprojq;subst;try apply proj_mon;try easy.
    }
    {
        rename H into IH.
        intros.
        pinversion Hprojp;try apply proj_mon;subst;try easy;inversion Htyp;subst.
        subtac_triv_isparts_false.
        eapply slist_implies_some in H8;destr_hyps.
        eapply Forall_prop in IH;try exact H5;tac_sanitize.
        eapply Forall2_prop_r in H13;try exact H5;tac_sanitize.
        eapply Forall2_prop_r in H3;try exact H9;tac_sanitize.
        destruct H11;try easy.
        inversion Hused;subst.
        eapply Forall2_prop_l in H15;try exact H5;tac_sanitize.
        eapply mergeCtx_onth_subset in H13 as Hsubset;try exact H11;try easy.
        eapply merge_inv_ss in H8 as Hminv;try exact H4;subst.
        
        pinversion Hprojq;subst;try apply proj_mon;try easy.
        eapply Forall2_prop_r in H22;try exact H9;tac_sanitize.
        destruct H20;try easy.
        eapply merge_inv_ss in H23;try exact H15;subst. 
        
        assert (Hstep:gttstepC (gtt_send p1 q1 xs1) x4 p1 q1 x).
        {
            pfold. econstructor;try easy;try exact (eq_sym H9).   
        }
        eapply H7 with (g:=x4) (gs_p:=x3) (xs:=xs0) (ys:=ys);try easy;
        try subtac_onth_solver.
        eapply Forall_subset;try exact Hsubset;try easy;try tauto.
        
        eapply part_after_step_r_redux;try exact Hstep;try easy.
        eapply part_after_step_r_redux;try exact Hstep;try easy.
        eapply decidable_helper.typh_with_less;try exact Hsubset;try easy.
    }
Qed.

Lemma multigrafting_lemma_send : forall  ctx_q p q g xs Tq gs_p gs_q ctx_p ,
wfgC g -> projectableA g -> projectionC g p (ltt_send q xs) ->
projectionC g q Tq -> typ_p_gtth gs_p ctx_p p g -> 
usedCtx gs_p ctx_p ->
typ_p_gtth gs_q ctx_q q g ->
usedCtx gs_q ctx_q ->
(is_tree_proper_prefix ctx_q ctx_p) \/ (gtth_eq ctx_p ctx_q).
Proof.
    intros. destruct Tq.
    {
        (*Search projectionC ltt_end isgPartsC. *)
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


Lemma gtth_eq_sym : forall a b, gtth_eq a b -> gtth_eq b a.
Proof.
    intros a. induction a using gtth_ind_ref.
    {
        intros. inversion H;subst;constructor.   
    }
    {
        intros. inversion H0;subst.
        constructor. eapply Forall2_forall. eapply Forall2_length in H5;try easy.
        intros.
        destruct (onth k ys) eqn:Hyg1. right.
        destruct p0. 
        eapply Forall2_prop_l in H5;try exact Hyg1;tac_sanitize. exists x0 , x2, x1.
        repeat split;try easy.
        eapply Forall_prop in H;try exact H2;tac_sanitize. eapply H1;easy.
        
        left. split;try easy.
        destruct (onth k xs) eqn:Hyg2. eapply Forall2_prop_r in H5;try exact Hyg2;tac_sanitize.
        rewrite Hyg1 in H3. easy. easy.
    }
Qed.

Lemma multigrafting_lemma_recv : forall  ctx_q p q g xs Tq gs_p gs_q ctx_p ,
wfgC g -> projectableA g -> projectionC g p (ltt_recv q xs) ->
projectionC g q Tq -> typ_p_gtth gs_p ctx_p p g -> 
usedCtx gs_p ctx_p ->
typ_p_gtth gs_q ctx_q q g ->
usedCtx gs_q ctx_q ->
(is_tree_proper_prefix ctx_q ctx_p) \/ (gtth_eq ctx_p ctx_q).
Proof.
    intros. destruct Tq.
    {
        eapply proj_contains_q_implies_part_recv in H1;try easy;eapply pmergeCR in H2;
        try easy.
    }
    {
        destruct (Nat.eq_dec n p);subst.
        
        exfalso; eapply two_recv_proj_impossible;try exact H1;try exact H2;try easy.

        left. 
        eapply multigrafting_lemma_3_recv with (gs_p:=gs_p) (gs_q:=gs_q) (r:=n) (p:=p) (q:=q) (ys:=l);try exact H1;try easy.
        auto.

    
    }
    {
        destruct (Nat.eq_dec n p);subst.
        right.
        eapply gtth_eq_sym.
        eapply multigrafting_lemma_2 with (gs_p:=gs_q) (gs_q:=gs_p) (p:=q) (q:=p); try exact H1;try exact H2;try easy.
        
        left.
        eapply multigrafting_lemma_3_recv with (gs_p:=gs_p) (gs_q:=gs_q) (r:=n) (p:=p) (q:=q) (ys:=l);try exact H1;try easy.
        auto.
    }
Qed.