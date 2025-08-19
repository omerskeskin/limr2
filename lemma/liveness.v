(* From mathcomp Require Import ssreflect.seq all_ssreflect. *)
From Paco Require Import paco pacotac.
From SST Require Import src.expr src.header src.local CpdtTactics src.lcontext.
From SST Require Import src.global src.projection src.part  src.balanced src.merge src.wfltt src.gttreeh.
From SST Require Import lemma.projection lemma.projection_helper lemma.decidable lemma.liveness_helpers lemma.soundness.
From SST Require Import src.step lemma.step src.assoc lemma.completeness src.ltth src.path_props.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Init.Logic.
From Coq Require Import IndefiniteDescription.

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
    Search isgPartsC gttstepRtc.
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
    Search isgPartsC gttstepRtc.
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
        Search projectionC isgPartsC ltt_send.
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
Admitted.

Lemma two_recv_proj_impossible: forall   p q g xs ys ,
wfgC g -> projectableA g -> projectionC g p (ltt_recv q xs) ->
projectionC g q (ltt_recv p ys) -> False.
Proof.
Admitted.

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



Lemma eventually_if {A:Type}: 
forall (P Q : coseq A -> Prop) (xs:coseq A), eventually P xs -> 
(forall ys, P ys -> eventually Q ys) -> eventually Q xs.
Proof.
    intros.
    induction H;[crush|].

    constructor 2. easy.
Qed.


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


Variant coseq_bisimI {A:Type} (R: coseq A -> coseq A -> Prop): 
coseq A -> coseq A -> Prop :=
    | coseq_bis_nil : coseq_bisimI R conil conil
    | coseq_bis_cons: forall xs ys x y, 
    R xs ys -> coseq_bisimI R (cocons x xs) (cocons y ys).

Definition coseq_bisimC {A:Type}:= paco2 ( @coseq_bisimI A) bot2.



Variant path_assoc (R:local_path -> global_path -> Prop): local_path -> global_path -> Prop :=
   | path_assoc_nil : path_assoc R conil conil
   | path_assoc_xs : forall g gamma l xs ys, assoc gamma g ->
    R xs ys ->
   path_assoc R (cocons (gamma, l) xs) (cocons (g, l) ys)
   .

Lemma path_assoc_mon : monotone2 path_assoc.
Proof. red;intros. inversion IN;subst;constructor;try tauto. apply LE;easy. Qed.
   
Definition path_assocC := paco2 path_assoc bot2.

Definition conj_props (P:tctx -> Prop) (Q: gtt -> Prop) := forall gamma g,

assoc gamma g -> (P gamma <-> Q g).

Definition tctxREN_comm p q g := exists n, (tctxRE (lcomm p q n) g). 


Definition tctxREN_send p q g := exists n s, (tctxRE (lsend p q s n) g).

Definition tctxREN_recv p q g := exists n s, (tctxRE (lrecv p q s n) g).

Print alwaysG.

Definition wfg_global_path := alwaysCG (to_path_prop (fun a=> wfgC a /\ projectableA a) True).
Definition wf_local_path := alwaysCG (to_path_prop tctx_wf True).
Lemma global_path_always_wf : forall g l xs, wfgC g -> projectableA g -> global_valid_pathC (cocons (g,l) xs) -> 
wfg_global_path (cocons (g,l) xs).
Proof.
    pcofix CIH.
    intros * Hwfg Hprojable Hvalid.
    pfold. constructor. simpl;easy.
    destruct xs. left. pfold. constructor. easy.
    right. destruct p.  pinversion Hvalid;subst;try apply valid_path_mon;try easy.
    eapply CIH;
    
    red in H5; destruct l0;try tauto.
    inversion Hvalid;subst.
    eapply wfgC_after_step;try exact H5;try easy. eapply projectable_after_step;try exact H5;try easy.
Qed.


Lemma local_path_always_wf : forall g l xs, tctx_wf g -> local_valid_pathC (cocons (g,l) xs) -> 
wf_local_path (cocons (g,l) xs).
Proof.
    pcofix CIH.
    intros * Hwfg  Hvalid.
    pfold. constructor. simpl;easy.
    destruct xs. left. pfold. constructor. easy.
    right. destruct p.  pinversion Hvalid;subst;try apply valid_path_mon;try easy.
    eapply CIH;
    
    red in H5; destruct l0;try tauto.
    inversion Hvalid;subst.
    eapply tctx_wf_after_red_comm;try exact H5;try easy.
Qed.

Lemma eventually_and {A:Type} P Q : forall (xs:coseq A),
            eventually ( P /1\ Q) xs <-> eventually (Q /1\ P) xs.
            Proof. split;intros; induction H; 
            try solve [constructor; easy | constructor 2; easy].  Qed.
            
Lemma path_assoc_eventually_enabled : forall xs ys P Q, wfg_global_path ys -> wf_local_path xs -> path_assocC xs ys -> 
conj_props P Q -> eventually (to_path_prop  P False) xs -> eventually (to_path_prop  Q False) ys.
Proof.
    intros * Hwfgp Hwfgl Hpassoc Hconj Hevp.
    generalize dependent ys.
    induction Hevp.
    {
        intros. constructor. red in H. destruct xs;try easy.
        pinversion Hpassoc;try apply path_assoc_mon;subst.
        red.
        eapply Hconj with (gamma:=gamma); easy. 
    }
    {
     intros.
     pinversion Hpassoc;try apply path_assoc_mon;subst.
     constructor 2.
     eapply IHHevp.
     pinversion Hwfgl;try apply always_mon;subst;easy.
     pinversion Hwfgp;try apply always_mon;subst;easy.
     easy.   
    }
Qed.
Lemma path_assoc_preserves_fairness_helper : forall xs p q ys, path_assocC xs ys ->
eventually (headComm p q) xs -> eventually (headComm_global p q) ys.
Proof.
    intros * Hpassoc Hevp.
    generalize dependent ys. induction Hevp.
    {
        intros. red in H. destruct xs as [ | [t l]];try easy.
        destruct l;try tauto;destruct l;try tauto.
        destruct (Nat.eq_dec p n);destruct (Nat.eq_dec q n0);try tauto;subst;clear H.
        pinversion Hpassoc;try apply path_assoc_mon;subst. constructor.  simpl. tauto.
    }
    {
        intros * Hpassoc. pinversion Hpassoc;try apply path_assoc_mon;subst.
        constructor 2.
        eapply IHHevp. easy.  
    }
Qed.


Lemma global_comm_enabled_assoc_local_comm_enabled: forall p q n gamma g, wfgC g ->
tctx_wf gamma -> global_comm_enabled p q n g -> 
assoc gamma g -> exists n', tctxRE (lcomm p q n') gamma.
Proof.
    intros * Hwfg Hwft Hgce Hassoc. 
    red in Hgce. destr_hyps. eapply assoc_soundness with (gamma:=gamma) in H;try easy.
    destr_hyps. exists x2. red. exists x0;easy.
    pinversion H;subst;try apply step_mon;easy.
Qed.

Lemma wfg_global_path_head: forall g l ys, wfg_global_path (cocons (g,l) ys) -> wfgC g.
Proof.
    intros. pinversion H;try apply always_mon;subst. red in H2. tauto.
Qed.

Lemma projable_global_path_head: forall g l ys, wfg_global_path (cocons (g,l) ys) -> projectableA g.
Proof.
    intros. pinversion H;try apply always_mon;subst. red in H2. tauto.
Qed.

Lemma wf_local_path_head: forall g l ys, wf_local_path (cocons (g,l) ys) -> tctx_wf g.
Proof.
    intros. pinversion H;try apply always_mon;subst. red in H2. tauto.
Qed.

Lemma always_tail {A:Type}: forall (g:A) (l:option label) xs P, alwaysCG P (cocons (g,l) xs) -> alwaysCG P xs.
Proof. intros. pinversion H;try apply always_mon;subst. easy. Qed.


    
Lemma path_assoc_preserves_fairness : forall lp gp, wfg_global_path gp -> wf_local_path lp ->
path_assocC lp gp ->
fair_path lp -> fair_path_global gp.
Proof.
    pcofix CIH.
    intros * Hwfgp Hwflp Hpassoc Hfairl.
    pfold.
    pinversion Hpassoc;try apply path_assoc_mon;subst.
    {
        constructor. red. intros. simpl in H. easy.
    }
    constructor.
    { 
        red. intros.
        pinversion Hfairl;subst;try apply always_mon.
        red in H4.
        simpl in H1.
        
        eapply global_comm_enabled_assoc_local_comm_enabled in H1 as Hlc;try exact Hassoc;try easy;
        try solve [
        apply wfg_global_path_head in Hwfgp;easy | apply wf_local_path_head in Hwflp;easy].
        destruct Hlc as [n' Hr].
        
        specialize (H4 p q n').
        simpl in H4. 
        specialize (H4 Hr). inversion H4;subst.
        {  
            simpl in H2.
            destruct l;try tauto.
            destruct l; destruct (Nat.eq_dec p n0);destruct (Nat.eq_dec q n1);subst;try tauto.
            constructor 1. simpl. tauto.
        }
        {
            constructor 2. eapply path_assoc_preserves_fairness_helper;try exact H3;try easy.
        }   
    }
    {
        right. eapply CIH with (lp := xs);
        eapply always_tail in Hwfgp, Hwflp, Hfairl;try easy.
    }
Qed.

Lemma local_send_enabled_global_send_enabled : forall g p q s n gamma, wfgC g -> tctx_wf gamma ->
        assoc gamma g -> tctxRE (lsend p q (Some s) n) gamma ->
        exists s' n', global_label_enabled (lsend p q (Some s') n') g.
Proof.
    intros * Hwfg Hwf Hassoc Hre.
    destruct Hre as [t' Hre].
    eapply lem_6_11a_tctx_send_invert in Hre. destr_hyps. 
    
    eapply assoc_inv_find in H as Hinvf;try exact Hassoc;try easy.
    red in Hinvf. destr_hyps. eapply subtype_send_inv1 in H3 as Hst. destr_hyps;subst. 
    eapply subtype_send_inv in H3. eapply Forall2R_prop in H3;try exact H0;tac_sanitize.
    exists x4, n.
    red. exists x2, x6. tauto.
Qed.

Lemma local_recv_enabled_global_recv_enabled : forall g p q s n gamma, wfgC g -> tctx_wf gamma ->
    assoc gamma g -> tctxRE (lrecv p q (Some s) n) gamma ->
    exists s' n', global_label_enabled (lrecv p q (Some s') n') g.
Proof.
    intros * Hwfg Hwf Hassoc Hre.
    destruct Hre as [t' Hre].
    eapply lem_6_11b_tctx_recv_invert in Hre. destr_hyps. 
    
    eapply assoc_inv_find in H as Hinvf;try exact Hassoc;try easy.
    red in Hinvf. destr_hyps. eapply subtype_recv_inv1 in H3 as Hst. destr_hyps;subst.
    
    eapply projection_implies_wf in H2 as Hwfp;try easy.
    eapply wfltt_slist_recv in Hwfp as Hslist. eapply slist_implies_some in Hslist.
    destr_hyps. destruct x3. exists s0,x1.
    red. exists x2, l. tauto.
Qed.

Lemma path_assoc_reflects_liveness_helper : forall xs p q ys, path_assocC xs ys ->
eventually (headComm_global p q) ys -> eventually (headComm p q) xs.
Proof.
    intros * Hpassoc Hevp.
    generalize dependent xs. induction Hevp.
    {
        intros. red in H. destruct xs as [ | [t l]];try easy.
        destruct l;try tauto;destruct l;try tauto.
        destruct (Nat.eq_dec p n) ;destruct (Nat.eq_dec q n0);try tauto;subst;clear H.
        pinversion Hpassoc;try apply path_assoc_mon;subst. constructor. simpl. tauto.
    }
    {
        intros * Hpassoc. pinversion Hpassoc;try apply path_assoc_mon;subst.
        constructor 2.
        eapply IHHevp. easy.  
    }
Qed.

Lemma path_assoc_reflects_liveness : forall lp gp, wfg_global_path gp -> wf_local_path lp ->
path_assocC lp gp ->
live_path_global gp -> live_path lp.
Proof.
    pcofix CIH.
    intros * Hwfgp Hwflp Hpassoc Hfairl.
    pfold.
    pinversion Hpassoc;try apply path_assoc_mon;subst.
    {
        constructor. red;split; intros; simpl in H; easy.
    }
    constructor.
    { 
        red;split; intros;
        pinversion Hfairl;subst;try apply always_mon;
        red in H4;
        simpl in H1;

        [eapply local_send_enabled_global_send_enabled in H1 as Hlc 
        | eapply local_recv_enabled_global_recv_enabled in H1 as Hlc];
        try exact Hassoc;try easy;
        try solve [
        apply wfg_global_path_head in Hwfgp;easy | apply wf_local_path_head in Hwflp;easy];
        destruct Hlc as [s' [n' Hr]];
        
        specialize (H4 p q s' n'); destruct H4 as [Hlv1 Hlv2];
        [
        assert(Hevg: eventually (headComm_global p q) (cocons (g,l) ys)) by (eapply Hlv1;easy)
        |
        assert(Hevg: eventually (headComm_global p q) (cocons (g,l) ys)) by (eapply Hlv2;easy)];
        eapply path_assoc_reflects_liveness_helper with (ys:=(cocons (g,l) ys));try easy;
        pfold;easy.
    }
    {
        right. eapply CIH with (gp := ys);
        eapply always_tail in Hwfgp, Hwflp, Hfairl;try easy.
    }
Qed.

(*
Definition g_by_gamma_trans : forall t p q ell g t', wfgC g -> tctx_wf t -> assoc t g ->
tctxR t (lcomm p q ell) t' ->
{g' | assoc t' g' /\ gttstepC g g' p q ell}.
Proof.
    intros. eapply assoc_completeness with (g:=g) in H0;try exact H2;try easy.
    destruct (constructive_indefinite_description _ H0) as [g' Hg'].
    exists g'. easy.
Defined.


Lemma valid_local_path_valid_trans: forall t p q ell xs,
valid_local_path (cocons (t, Some (lcomm p q ell)) xs) ->
{s| match s with (t',l,ys) => 
xs= cocons (t',l) ys /\ tctxR t (lcomm p q ell) t' end}.
Proof.
    intros. 
    refine (
        (match xs as m return xs =m -> {s| match s with (t',l,ys) => 
xs= cocons (t',l) ys /\ tctxR t (lcomm p q ell) t' end} with 
    |conil => _
    | cocons (t',l) ys => _ end
) (eq_refl)).
    {
        intros. subst.
        assert(False).
        {
            pinversion H;try apply valid_path_mon.   
        }
        exists (M.empty, None, conil). easy.   
    }
    {
        intros. subst. exists (t', l, ys).
        split. easy.
        pinversion H;subst;try apply valid_path_mon. easy.   
    }
Defined.


Lemma valid_local_path_dilemma: forall t l xs, valid_local_path (cocons (t,l) xs) ->
{ s & match s with (p,q,ell) => {l=Some (lcomm p q ell)} + {l=None} end }.
Proof.
    intros.
    destruct l;try tauto.
    {
        assert(Hrec: { s | match s with (p,q,ell) => l=lcomm p q ell end}).
        {
                refine ((match l as m return 
                (l=m -> { s | match s with (p,q,ell) => l=lcomm p q ell end}) with 
                | lsend a b c d => _
                | lrecv a b c d => _
                
                | lcomm p q ell => _ end) (eq_refl));intros;subst;
                try (
                assert(False) by
                (
                    pinversion H;subst;try apply valid_path_mon; inversion H4  
                );
                exists (0,0,0); easy).
                exists (p,q,ell). reflexivity.
        }
        destruct Hrec. destruct x as [[p q] ell]. subst. exists (p,q,ell). tauto.
    }
    {
        exists (0,0,0). right. easy.   
    }
Defined.
(*
Ltac indef_destruct H := let tth := type of H in match tth with 
     | ex _  => let nx := fresh "x" in let nh:= fresh "H" in  
    destruct (constructive_indefinite_description _ H) as [nx nh];try indef_destruct nh;clear H end.
*)   
CoFixpoint conj_path : forall t g l  xs, wfgC g -> tctx_wf t -> assoc t g ->
    valid_local_path (cocons (t, l) xs) ->
    global_path.
Proof.
    intros * Hwfg Htxt Hassoc Hvalid.
    eapply valid_local_path_dilemma in Hvalid as Hdl.
    destruct Hdl as [[[p q] ell] Hdd].
    destruct Hdd.
    {
        subst.
        eapply valid_local_path_valid_trans in Hvalid as Htrans.
        destruct Htrans as [[[t' l] ys] H1].
        
        destruct H1;subst. 
        set (seq_hd := (g,Some (lcomm p q ell))).
        eapply g_by_gamma_trans with (g:=g) in H0 as Ht2;try easy.
        destruct Ht2.
        rename  x into g'.
        destruct a as [Ha0 Ha1].
        assert(Hwft': tctx_wf t').
        {
            eapply tctx_wf_after_red_comm;try exact H0;try easy.   
        }
        assert(Hwfg': wfgC g').
        {

            eapply wfgC_after_step;try exact Ha1;try easy.
            eapply assoc_implies_projectable;try exact Hassoc;try easy.   
        }
        assert(Hvlxs: valid_local_path (cocons (t', l) ys)).
        {
            pinversion Hvalid;try apply valid_path_mon;tauto.   
        }
        
        specialize (conj_path t' g' l ys Hwfg' Hwft' Ha0 Hvlxs) as vxs.
        exact (cocons seq_hd vxs).
    }
    subst. exact (cocons (g, None) conil).
Defined.


Lemma conj_path_recur : forall (t:tctx) (g:gtt) (l:option label) (xs:local_path) 
 (Hwfg : wfgC g) (Htxwf : tctx_wf t) (Hassoc: assoc t g) 
(Hvalid : valid_local_path (cocons (t,l) xs)), exists ys,
(conj_path _ _ _ _ Hwfg Htxwf Hassoc Hvalid) = cocons (g,l) ys.
Proof.
    intros.
    destruct l.
    {
           destruct l;
        pose proof Hvalid as Hvalid'; pinversion Hvalid'; try apply valid_path_mon;try tauto;subst.
        rewrite (coseq_eq (conj_path _ _ _ _ _ _ _ _   )). simpl.

        destruct (g_by_gamma_trans t n n0 n1 g x Hwfg Htxwf Hassoc) (eqn:Hyg).
        Check eq_rec_r.

    }
    {
        rewrite (coseq_eq (conj_path _ _ _ _ _ _ _ _   )). simpl. exists conil;easy.
    }
    

Lemma conj_path_path_assoc : forall (t:tctx) (g:gtt) (l:option label) (xs:local_path) 
 (Hwfg : wfgC g) (Htxwf : tctx_wf t) (Hassoc: assoc t g) 
(Hvalid : valid_local_path (cocons (t,l) xs)),

path_assocC (cocons (t,l) xs) 
(conj_path _ _ _ _ Hwfg Htxwf Hassoc Hvalid).
Proof.
    pcofix CIH.
    intros.
    destruct l.
    {
        destruct l;
        pose proof Hvalid as Hvalid'; pinversion Hvalid'; try apply valid_path_mon;try tauto;subst.

        rewrite (coseq_eq (conj_path _ _ _ _ _ _ _ _   )).
        pfold.
           
            
    }
    {
        Search valid_path_GC conil.
        eapply valid_path_none_next_nil in Hvalid as Hv2;subst.
        pfold.
        assert(conj_path t g None conil Hwfg Htxwf Hassoc Hvalid = cocons (g,None) conil).
        {
            rewrite (coseq_eq (conj_path _ _ _ _ _ _ _ _   )).
            simpl. reflexivity.
        }
        rewrite H. constructor;try tauto.
        left. pfold. constructor.     
    }
*)

Lemma conj_path_exists: forall g gamma xs l, wfgC g -> tctx_wf gamma -> assoc gamma g ->
    exists ys, path_assocC (cocons (gamma,l) xs) (cocons (g, l) ys).
Proof.
Admitted.


Definition head_proj_is_recv p q:=(
    fun (pt:global_path) => match pt with 
        | cocons (hd,l) tl => exists xs, 
        projectionC hd p (ltt_recv q xs)   
        | _ => False end
        ).

Definition head_proj_is_send p q:=(
    fun (pt:global_path) => match pt with 
        | cocons (hd,l) tl => exists xs, 
        projectionC hd p (ltt_send q xs)   
        | _ => False end
        ).

Check eventually_if.
(*
Lemma assoc_live_helper_send_helper : typ_ltth lx ls Tq ->

*)
Search "typ_p".
Print typ_p_send_ltth.

(*
Definition weak_until {A:Type} F G := fun (u:coseq A) => until F G u \/ alwaysCG F u.

Definition weak_untilC_eq_weak_until {A:Type}: forall F G (xs : coseq A), 
    weak_untilC F G xs <-> weak_until F G xs. 
Proof.
    split.
    {  
        admit.
    }
    {
        generalize dependent xs.
        pcofix CIH.
        intros * Hweak.
        destruct Hweak.
        {
            inversion H;subst. pfold. constructor;easy.
            
            pfold;constructor 2;try easy. right. eapply CIH;left;easy.
        }
        {
            destruct xs. pfold. constructor 3. pinversion H;try apply always_mon;subst;easy. 
            pfold. constructor 2. pinversion H;try apply always_mon;subst;easy.
            right. eapply CIH. right. pinversion H;try apply always_mon;subst;easy.
        }
    }
Admitted.*)

Lemma weak_untilC_to_until {T:Type} A B (xs: coseq T): weak_untilC A B xs -> 
    eventually B xs -> until A B xs.
Proof.
        intros. generalize dependent H. induction H0.
        {
            intros. constructor 1;easy.   
        }
        {
            intros.
            pinversion H;subst. constructor 1;easy.

            constructor 2;try easy. eapply IHeventually;easy.   
        }
Qed.
(*
Lemma weak_until_to_until {T:Type} A B (xs: coseq T): weak_until A B xs -> 
    eventually B xs -> until A B xs.
Proof.
    intros. red in H.
    destruct H;try easy.
    generalize dependent H. induction H0.
    {
        intros. constructor 1;easy.   
    }
    {
        intros. constructor 2;
        pinversion H;try apply always_mon;subst;try easy. eapply IHeventually;easy.   
    }
Qed.*)

Definition trans_involves_p l r :=
    match l with 
        | lsend p q _ _ => p=r \/ q=r  
        | lrecv p q _ _ => p=r \/ q=r
        | lcomm p q  _ => p=r \/ q=r
    end.

Search True False.

Definition head_trans_not_involving_p {A:Type} p (xs:coseq (A * option label)) := match xs with 
    | conil => True
    | cocons (g,Some l) xs =>  (trans_involves_p l p -> False) 
    | _ => True end.

Lemma typ_after_step_r_redux : forall (G G' : gtt) (p q s l : opt_lbl)
                    (T : ltt),
                    wfgC G -> projectableA G ->
                    gttstepC G G' p q l ->
                    s <> q ->
                    s <> p ->
                    projectionC G s T ->
                    exists T' : ltt, projectionC G' s T' /\ T = T'.
                Proof.
                    intros.
                    eapply proj_cont_pq_step in H1 as Hlocals;try easy.
                    destr_hyps.
                    eapply typ_after_step_3_helper with (G:=G) (p:=p) (q:=q) (l:=l) (L1:=x) (L2:=x0);
                    try exact H7;try exact H8; try easy.
                    eapply wfgC_after_step in H1;try easy.
                Qed.
            
Ltac subtac_tail_solve:=
                match goal with [ H: ?ct (cocons _ ?a) |- ?ct ?a] => pinversion H;subst;tauto end.
                
Ltac subtac_tail_valid:=
                match goal with [ H: global_valid_pathC (cocons _ ?a) |- global_valid_pathC ?a] =>
                 pinversion H;subst;try easy;try apply valid_path_mon;try (pfold;constructor) end.
                            

Lemma no_trans_until_heads_match_send : forall p q xs, fair_path_global xs ->
global_valid_pathC xs -> 
wfg_global_path xs -> 
head_proj_is_send p q xs -> weak_untilC (head_trans_not_involving_p p) 
(head_proj_is_recv q p) xs.
Proof.
    intros * Hfair Hvalid Hwfgp Hprojp.
    generalize dependent xs.
    pcofix CIH.
    destruct xs.
    {
        intros;red in Hprojp;easy.   
    }
    {
        generalize dependent xs.
        intros.        
        destruct p0 as [g l].
        assert(Hwfg : wfgC g)
        by  (eapply wfg_global_path_head;try exact Hwfgp).
        
        assert(Hprojable : projectableA g) 
        by (pinversion Hwfgp;subst; red in H1;tauto).
        destruct l.
        {
            pinversion Hvalid;try apply valid_path_mon;subst.
            destruct l;try easy.
            rename n into s, n0 into t, n1 into ell.
            pfold.
            destruct (Nat.eq_dec s p);
            destruct (Nat.eq_dec t p);subst;try tauto;red in H3.
            {
                pinversion H3;try apply step_mon;subst;tauto.
            }
            {
                eapply proj_cont_pq_step in H3 as Hlocals;try easy.
                red in Hprojp. destruct Hprojp as [xsp Hprojp].
                destr_hyps.
                eapply proj_inj in H;try exact Hprojp;try easy.
                inversion H;subst.
                constructor 1. simpl. exists x1. easy.
            }
            {
                eapply proj_cont_pq_step in H3 as Hlocals;try easy.
                red in Hprojp. destruct Hprojp as [xsp Hprojp].
                destr_hyps.
                eapply proj_inj in H0;try exact Hprojp;try easy.
            }
            {
                constructor 2. simpl;destruct (Nat.eq_dec s p);destruct (Nat.eq_dec t p);try tauto.
                
                right. 
                eapply CIH;try solve subtac_tail_solve.
                pfold. inversion Hvalid;subst. destruct H2. punfold H;try apply valid_path_mon;try easy. 
                inversion H.
                                red in Hprojp. destruct Hprojp as [xsp Hprojp].
                eapply typ_after_step_r_redux in H3;try exact Hprojp;try easy;subst.

                red.
                exists xsp. destr_hyps;subst;tauto.
            }
        }
        {
            pinversion Hvalid;try apply valid_path_mon;subst.
            pfold.
            constructor 2; try easy.
            left. pfold. constructor 3 . simpl;easy. 
        }   
    }
Qed.

Lemma no_trans_until_heads_match_recv : forall p q xs, fair_path_global xs ->
global_valid_pathC xs -> 
wfg_global_path xs -> 
head_proj_is_recv p q xs -> weak_untilC (head_trans_not_involving_p p) 
(head_proj_is_send q p) xs.
Proof.
    intros * Hfair Hvalid Hwfgp Hprojp.
    generalize dependent xs.
    pcofix CIH.
    destruct xs.
    {
        intros;red in Hprojp;easy.   
    }
    {
        generalize dependent xs.
        intros.        
        destruct p0 as [g l].
        assert(Hwfg : wfgC g)
        by  (eapply wfg_global_path_head;try exact Hwfgp).
        
        assert(Hprojable : projectableA g) 
        by (pinversion Hwfgp;subst; red in H1;tauto).
        destruct l.
        {
            pinversion Hvalid;try apply valid_path_mon;subst.
            destruct l;try easy.
            rename n into s, n0 into t, n1 into ell.
            pfold.
            destruct (Nat.eq_dec s p);
            destruct (Nat.eq_dec t p);subst;try tauto;red in H3.
            {
                pinversion H3;try apply step_mon;subst;tauto.
            }
            {
                eapply proj_cont_pq_step in H3 as Hlocals;try easy.
                red in Hprojp. destruct Hprojp as [xsp Hprojp].
                destr_hyps.
                eapply proj_inj in H;try exact Hprojp;try easy.
                
            }
            {
                
                eapply proj_cont_pq_step in H3 as Hlocals;try easy.
                red in Hprojp. destruct Hprojp as [xsp Hprojp].
                destr_hyps.
                eapply proj_inj in H0;try exact Hprojp;try easy.
                inversion H0;subst.
                constructor 1. simpl. exists x0. easy.
            }
            {
                constructor 2. simpl;destruct (Nat.eq_dec s p);destruct (Nat.eq_dec t p);try tauto.
                
                right. 
                eapply CIH;try solve subtac_tail_solve.
                pfold. inversion Hvalid;subst. destruct H2. punfold H;try apply valid_path_mon;try easy. 
                inversion H.
                                red in Hprojp. destruct Hprojp as [xsp Hprojp].
                eapply typ_after_step_r_redux in H3;try exact Hprojp;try easy;subst.

                red.
                exists xsp. destr_hyps;subst;tauto.
            }
        }
        {
            pinversion Hvalid;try apply valid_path_mon;subst.
            pfold.
            constructor 2; try easy.
            left. pfold. constructor 3 . simpl;easy. 
        }   
    }
Qed.

Search typ_gtth gttstepC.


Lemma graft_height_after_step: forall gs gx p g' g s t ell, 
p <> s ->
p <> t ->
typ_p_gtth gs gx p g ->
usedCtx gs gx -> gttstepC g g' s t ell ->
exists  gx' gs',
typ_p_gtth gs' gx' p g' /\
usedCtx gs' gx' /\ (gtth_height gx' <= gtth_height gx).
Proof.
    intros * Hps Hpt [?Htypg [?Htypg ?Htypg]] Husedp Hstep.
    generalize dependent gs. revert Hps Hpt Hstep. 
    generalize dependent g'.
    generalize dependent g.
    generalize dependent gx.
    induction gx using gtth_ind_ref.
    {
        intros.
        inversion Htypg;subst.
        exists (gtth_hol n). exists (extendLis n (Some g')). 
        repeat split;try easy.
        constructor. rewrite extendExtract;easy.
        eapply Forall_forall.
        intros.
        destruct x;try tauto. right.

        apply in_some_implies_onth in H. destr_hyps.
        
        eapply extend_onth_inv in H as ?Ht;subst. rewrite extendExtract in H.
        inversion H;subst.
        eapply Forall_prop in Htypg1;try exact H1;tac_sanitize.
        destruct H0 as [?Htr | [?Htr | ?Htr]];
        inversion Htr;subst;
        pinversion Hstep;try apply step_mon;subst;try tauto;
        exists x, ys;tauto.
        constructor.
    }
    {
        intros.   
        pinversion Hstep;try apply step_mon;subst.
        {
            apply eq_sym in H1.
            inversion Htypg;subst.
            rename xs0 into gcs, xs into ghs.
            eapply Forall2_prop_l in H10;try exact H1;tac_sanitize.
            rename x1 into gh', x2 into g', x0 into s0.

            inversion Husedp;subst.
            eapply Forall2_prop_l in H10;try exact H3;tac_sanitize.
            rename x1 into s0, x2 into gx'.
            exists gx',x0.
            repeat split;
            eapply mergeCtx_onth_subset in H8;try exact H4;
            eapply decidable_helper.typh_with_less in H6;try exact H9;try tauto.
            rename x0 into gs'.
            intros. eapply Htypg0. econstructor 3;try exact H3;try easy.
            eapply Forall_subset with (gs:=gs);try tauto.
            Search gtth_height.
            eapply gtth_height_ge_children  with (p:=s) (q:=t) (k :=gtth_height gx') in H3 as Hge;crush.
            
        }
        admit.
    }
Admitted.

Definition head_proj_is p lt (xs:global_path) := match xs with | conil => False
    | cocons (g,l) xs => projectionC g p lt end.

Definition head_proj_is_nil_true p lt (xs:global_path) := match xs with 
| conil => True
    | cocons (g,l) xs => projectionC g p lt end.

Lemma no_trans_implies_same_proj_send : forall xs p q lcs,
fair_path_global xs ->
global_valid_pathC xs -> 
wfg_global_path xs -> 
head_proj_is p (ltt_send q lcs) xs ->
until (head_trans_not_involving_p p) (head_proj_is_recv q p) xs ->
eventually ( head_proj_is p (ltt_send q lcs) /1\ head_proj_is_recv q p) xs.
Proof.
    intros * Hfair Hvalid Hwfgp Hprojp Huntil.

    induction Huntil.
    {
        constructor. tauto.   
    }
    {
        constructor 2.
        eapply IHHuntil;try solve subtac_tail_solve;
        pinversion Hvalid;try apply valid_path_mon;subst; try solve [easy |pfold; constructor].
        
        red in Hprojp.
        inversion Huntil;subst;tauto.

        destruct l;red in H3;try easy.
        rename y into g, x0 into g'.
        red in H;red in Hprojp. 
        
        simpl in H.
        destruct (Nat.eq_dec n p);
        destruct (Nat.eq_dec n0 p);subst;try tauto.
        assert(Hwfg : wfgC g)
        by  (eapply wfg_global_path_head;try exact Hwfgp).
        
        assert(Hprojable : projectableA g) 
        by (pinversion Hwfgp;subst; red in H4;tauto).
        eapply typ_after_step_r_redux in H3;try exact Hprojp;try easy.
        red. destr_hyps. subst. easy.
    }
Qed.


Lemma no_trans_implies_same_proj_recv : forall xs p lcs q,
fair_path_global xs ->
global_valid_pathC xs -> 
wfg_global_path xs -> 
head_proj_is p (ltt_recv q lcs) xs ->
until (head_trans_not_involving_p p) (head_proj_is_send q p) xs ->
eventually ( head_proj_is p (ltt_recv q lcs) /1\ head_proj_is_send q p) xs.
Proof.
    intros * Hfair Hvalid Hwfgp Hprojp Huntil.

    induction Huntil.
    {
        constructor. tauto.   
    }
    {
        constructor 2.
        eapply IHHuntil;try solve subtac_tail_solve;
        pinversion Hvalid;try apply valid_path_mon;subst; try solve [easy |pfold; constructor].
        red in Hprojp.
        inversion Huntil;subst;tauto.
        destruct l;red in H3;try easy.
        rename y into g, x0 into g'.
        red in H;red in Hprojp. 
        simpl in H.
        destruct (Nat.eq_dec n p);
        destruct (Nat.eq_dec n0 p);subst;try tauto.
        assert(Hwfg : wfgC g)
        by  (eapply wfg_global_path_head;try exact Hwfgp).
        
        assert(Hprojable : projectableA g) 
        by (pinversion Hwfgp;subst; red in H4;tauto).
        eapply typ_after_step_r_redux in H3;try exact Hprojp;try easy.
        red. destr_hyps.  subst. easy.
    }
Qed.

Lemma eventually_P_always_PQ_eventually_Q {A:Type} (P: coseq A -> Prop) Q: forall xs, eventually P xs -> alwaysCG (fun u=>
P u -> eventually Q u) xs -> eventually Q xs .
Proof.
    intros. generalize dependent H0. induction H.
    {
        intros. pinversion H0;subst; eapply H1;easy.   
    }
    {
        intros.
        pinversion H0;subst. constructor 2. eapply IHeventually. easy.    
    }
Qed.

Print live_path_inner_global.

Print fair_path_inner_global.

Lemma matching_proj_enables_step : forall g p q xp xq, wfgC g ->
projectionC g p (ltt_send q xp)  ->
projectionC g q (ltt_recv p xq)  ->
exists g' ell, gttstepC g g' p q ell.
Proof.
    intros * Hwfg Hprojp Hprojq .
    assert (Hwflp: wflttC (ltt_send q xp)).
    {
        eapply projection_implies_wf;try exact Hprojp;try easy.   
    }
    assert (Hwflq: wflttC (ltt_recv p xq)).
    {
        eapply projection_implies_wf;try exact Hprojq;try easy.   
    }
    eapply lem_6_16_simul_subproj with (p:=p) (q:=q) (xp:=xp) (xq:=xq) in Hwfg as Hsim;try easy.
    eapply wfltt_slist_send in Hwflp. eapply slist_implies_some in Hwflp. destr_hyps.
    eapply Forall2R_prop in Hsim;try exact H;tac_sanitize.
    eapply typ_after_step_step in Hprojp as Htypstep;try exact Hprojp;try exact Hprojq;try exact H;try exact H2;try easy.
    destr_hyps. exists x0, x. easy.
    eapply projection_implies_part_send;try exact Hprojp.
    exists (ltt_send q xp);
    split;try easy;eapply stRefl.
    exists (ltt_recv p xq);
    split;try easy;eapply stRefl.
    eapply wfltt_slist_send in Hwflp;try easy.
    eapply wfltt_slist_recv in Hwflq;try easy.
Qed.

Lemma matching_head_proj_to_comm: forall p q xs, global_valid_pathC xs -> wfg_global_path xs -> fair_path_global xs ->
eventually (head_proj_is_send p q /1\ head_proj_is_recv q p) xs -> 
eventually (headComm_global p q) xs.
Proof.
    intros * Hvalid Hwfgp Hfair Hev. revert Hvalid Hwfgp Hfair.
    induction Hev.
    {
        intros. red in Hfair. unfold  fair_path_inner_global in Hfair.
        pinversion Hfair;subst;

        [destruct H; inversion H |].
        
        destruct x as [g l].
        assert(Hwfg: wfgC g) by
        (pinversion Hwfgp;subst;red in H4;tauto).
        destruct H as [Hprojp Hprojq].
        red in Hprojp, Hprojq.
        destr_hyps.
        eapply matching_proj_enables_step in H2;try exact H;try easy.
        destruct H2 as [g' [ell Hstep]].
        eapply H0 with (n:=ell).  simpl. 
        red. exists g';easy.    
    }
    {
        intros.
        constructor 2. eapply IHHev;try subtac_tail_solve.
        pinversion Hvalid;subst;try apply valid_path_mon. pfold;constructor.
        easy.   
    }
Qed. 

Inductive is_suffix {A:Type}: coseq A -> coseq A -> Prop :=
    | suffix_refl : forall xs, is_suffix xs xs
    | suffix_cons : forall a xs ys, is_suffix xs ys -> is_suffix xs (cocons a ys).

Lemma graft_height_decreases_strictly : 
                 forall (gs : list (option gtt)) (gx : gtth) (p : opt_lbl) q 
                (g' g : gtt) (s t ell : opt_lbl),
                p <> s ->
                p <> t ->
                (q=s \/ q=t) ->
                ishParts q gx ->
                typ_p_gtth gs gx p g ->
                usedCtx gs gx ->
                gttstepC g g' s t ell ->
                exists (gx' : gtth) (gs' : list (option gtt)),
                typ_p_gtth gs' gx' p g' /\
                usedCtx gs' gx' /\ gtth_height gx' < gtth_height gx.
                Proof.
                Admitted.

Lemma suffix_trans {A:Type}: forall (xs: coseq A) ys zs,is_suffix xs ys -> is_suffix zs xs -> is_suffix zs ys.
Proof.
    intros.
    
    generalize dependent zs.
    induction H.
    intros;easy.

    intros. constructor. eapply IHis_suffix. easy.
Qed.

Lemma always_P_implies_P_suffix {A:Type} (P: coseq A -> Prop): forall xs, 
alwaysCG P xs -> forall ys,
is_suffix ys xs -> alwaysCG P ys.
Proof.
    intros.
    revert H; induction H0.
    intros. easy.
    intros. eapply IHis_suffix. pinversion H;try easy.
Qed.


Lemma always_P_iff_P_suffix {A:Type} (P: coseq A -> Prop): forall xs, 
alwaysCG P xs <-> forall ys,
is_suffix ys xs -> P ys.
Proof.
    split.
    intros.
    revert H; induction H0.
    intros. pinversion H;subst;easy.

    intros. eapply IHis_suffix. pinversion H;try easy.

    
    generalize dependent xs. pcofix CIH.
    intros. destruct xs. pfold. constructor.
    specialize (H0 conil (suffix_refl conil));easy. 
    
    pfold. constructor. specialize (H0 (cocons a xs) (suffix_refl _));easy.
    right. eapply CIH. 
    intros. eapply H0. eapply suffix_trans with (xs:=xs); try easy. constructor;constructor.
Qed.

Definition eventually_P_iff_P_suffix {A:Type} (P: coseq A -> Prop): forall xs, 
eventually P xs <-> exists ys,
is_suffix ys xs /\ P ys.
Proof.
    intros;split;intros.
    induction H.
    exists xs;split;[constructor | easy].
    destr_hyps. exists x0. split;[constructor | ];crush.
    destruct H as [ys [Hsuf Hp]].
    induction Hsuf;
    [constructor 1 | constructor 2];crush.
Qed.


Lemma eventually_idemp {A:Type}: forall (P : coseq A -> Prop) xs, 
eventually P xs <-> eventually (eventually P) xs.
Proof.
    split;intros.
    constructor. easy.
    induction H;try easy.

    constructor 2. easy.
Qed.

(*incorporate the label*)
(*
Definition head_proj_eventually_takes_step p (xs : global_path) := 
    match xs with 
    | cocons (g,l) xs' => forall Tp, projectionC g p Tp ->
        (
            (forall q lcs, Tp=ltt_send q lcs ->
        exists k s Tp', onth k lcs=Some (s,Tp') /\ eventually 
        (fun u => match u with 
            | cocons (g,Some (lcomm a b ell)) (cocons (g',_) _) => 
            a=p /\ b=q /\ ell =k /\ projectionC g p Tp'
            | _ => False
        end) (cocons (g,l) xs') ) 
        /\  

        (forall q lcs, Tp= (ltt_recv q lcs) ->
        exists k s Tp', onth k lcs=Some (s,Tp') /\ eventually 
        (fun u => match u with 
            | cocons (g,Some (lcomm a b ell)) (cocons (g',_) _) => 
            a=q /\ b=p /\ ell =k /\ projectionC g p Tp'
            | _ => False
        end) (cocons (g,l) xs') ))
    | _ => True end.
*)

Print headComm_global.

Definition head_proj_eventually_takes_step p (xs : global_path) := 
    match xs with 
    | cocons (g,l) xs' => forall Tp, projectionC g p Tp ->
        (
            (forall q lcs, Tp=ltt_send q lcs ->
        eventually 
        (headComm_global p q) (cocons (g,l) xs') ) 
        /\  

        (forall q lcs, Tp= (ltt_recv q lcs) ->
        eventually 
        (headComm_global q p) (cocons (g,l) xs') ))
    | _ => True end.

Lemma always_idemp {A:Type}: forall P (xs : coseq A), alwaysCG P xs <-> alwaysCG (alwaysCG P) xs.
Proof.
    split.
    {
        generalize dependent xs.
        pcofix CIH.
        intros.
        destruct xs. pfold. constructor. easy.    
        intros; 
        pfold; constructor; try easy; right; eapply CIH; pinversion H0;subst;easy.
    }
    {
        generalize dependent xs.
        pcofix CIH.
        intros. destruct xs;pfold;constructor. pinversion H0;subst. pinversion H;subst;easy.
        pinversion H0;subst;pinversion H2;subst;try easy.
        right. eapply CIH. pinversion H0;subst;easy.   
    }
Qed. 

Lemma valid_suffix_valid_global : forall xs ys, global_valid_pathC xs -> is_suffix ys xs -> global_valid_pathC ys.
Proof.
    intros. induction H0;try easy. eapply IHis_suffix. pinversion H;subst;try apply valid_path_mon.
    pfold;constructor. easy.
Qed. 

Definition head_grafting_proper_prefix p q (xs:global_path) := match xs with 
    | conil => True
    | cocons (g,l) xs => exists ctx_p gs_p ctx_q gs_q, typ_p_gtth  gs_p ctx_p p g /\
        typ_p_gtth gs_q ctx_q  q g /\ usedCtx gs_p ctx_p /\ usedCtx gs_q ctx_q /\ is_tree_proper_prefix ctx_p ctx_q end.
    

Definition head_grafting_eq p q (xs:global_path) := match xs with 
    | conil => False
    | cocons (g,l) xs => exists ctx_p gs_p ctx_q gs_q, typ_p_gtth  gs_p ctx_p p g /\
        typ_p_gtth gs_q ctx_q  q g /\ usedCtx gs_p ctx_p /\ usedCtx gs_q ctx_q 
        /\ gtth_eq ctx_p ctx_q end.

Definition all_fair_paths P:= forall xs, fair_path_global xs -> 
global_valid_pathC xs ->  wfg_global_path xs -> P xs.

(*
Definition always_local_step_implies_ev_grafting : forall lx g p q l xs ls Tp ,
let full_pt := cocons (g,l) xs in
fair_path_global full_pt -> 
global_valid_pathC full_pt ->  wfg_global_path full_pt ->
alwaysCG (head_proj_eventually_takes_step p) full_pt -> 
projectionC g p Tp -> 
(typ_p_send_ltth ls lx q Tp -> eventually (head_proj_is_send p q) full_pt) /\ 
(typ_p_recv_ltth ls lx q Tp -> eventually (head_proj_is_recv p q) full_pt).
Proof.
    induction lx using ltth_ind_ref.
    {
        intros * Hfair Hvalid Hwfgp Halways Hproj;split;intros Htypp;
        destruct Htypp as [?Htypp [?Htypp ?Htypp]];
        constructor 1; simpl;  inversion Htypp;subst;
        assert (used_in_ltth n (ltth_hol n)) by constructor;
        
        specialize (Htypp1 n H); destr_hyps; rewrite H1 in H0; inversion H0;subst; 
        exists x; easy.
    }
    {
        intros * Hfair Hvalid Hwfgp Halways Hproj;split;intros Htypp;
        destruct Htypp as [?Htypp [?Htypp ?Htypp]];
        
        pose proof Halways as Halways';
        pinversion Halways;subst;rename H2 into Hev_step, H3 into Haw1;
        red in Hev_step;
        inversion Htypp;subst;rename H4 into HFa2_ltg;
        specialize (Hev_step _ Hproj);
        destruct Hev_step as [Hevs_rel _];
        assert (Hstupid1 : ltt_send q ys = ltt_send q ys) by reflexivity;
        specialize (Hevs_rel q ys Hstupid1); 
        destruct Hevs_rel as [k [s [Tp' [Honthk Hev2]]]];
        eapply Forall2_prop_l in HFa2_ltg;try exact Honthk;try easy;tac_sanitize;
        eapply Forall_prop in H;try exact H1;try easy;tac_sanitize;

        rename x into s, x3 into lg, x2 into Tp', H1 into Honthk2, H0 into IHs, H3 into Hlgraft;
        rewrite eventually_P_iff_P_suffix in Hev2;
        destruct Hev2 as [xs1 [Hsuf Hp]];
        destruct xs1;try destruct p0;try easy;
        rewrite eventually_idemp;

        rewrite eventually_P_iff_P_suffix;
        exists (cocons (g0,o) xs1);split;try solve [ 
            unfold full_pt; constructor; easy   
        ];
        assert (Hsuf' : is_suffix (cocons (g0,o) xs1) full_pt) by (unfold full_pt;constructor;easy);
        eapply IHs with (ls:=ls) (Tp:=Tp');try easy;
        try solve [

        eapply always_P_implies_P_suffix with (xs:=full_pt);easy | 
        eapply valid_suffix_valid_global with (xs:=full_pt);easy];
        red; repeat split;try easy;
        assert (Hqq0: q <> q0) by (red;intros; eapply Htypp0;subst;constructor);
        try solve
        [
        intros; eapply Htypp0; econstructor 3 with (g:=lg);try exact Honthk2;easy |
        intros;
        eapply Htypp1; econstructor;try exact Honthk2;easy].
    }
    {
        intros * Hfair Hvalid Hwfgp Halways Hproj;split;intros Htypp;
        destruct Htypp as [?Htypp [?Htypp ?Htypp]];
        
        pose proof Halways as Halways';
        pinversion Halways;subst;rename H2 into Hev_step, H3 into Haw1;
        red in Hev_step;
        inversion Htypp;subst;rename H4 into HFa2_ltg;
        specialize (Hev_step _ Hproj);
        destruct Hev_step as [_ Hevs_rel];
        assert (Hstupid1 : ltt_recv q ys = ltt_recv q ys) by reflexivity;
        specialize (Hevs_rel q ys Hstupid1); 
        destruct Hevs_rel as [k [s [Tp' [Honthk Hev2]]]];
        eapply Forall2_prop_l in HFa2_ltg;try exact Honthk;try easy;tac_sanitize;
        eapply Forall_prop in H;try exact H1;try easy;tac_sanitize;

        rename x into s, x3 into lg, x2 into Tp', H1 into Honthk2, H0 into IHs, H3 into Hlgraft;
        rewrite eventually_P_iff_P_suffix in Hev2;
        destruct Hev2 as [xs1 [Hsuf Hp]];
        destruct xs1;try destruct p0;try easy;
        rewrite eventually_idemp;

        rewrite eventually_P_iff_P_suffix;
        exists (cocons (g0,o) xs1);split;try solve [ 
            unfold full_pt; constructor; easy   
        ];
        assert (Hsuf' : is_suffix (cocons (g0,o) xs1) full_pt) by (unfold full_pt;constructor;easy);
        eapply IHs with (ls:=ls) (Tp:=Tp');try easy;
        try solve [

        eapply always_P_implies_P_suffix with (xs:=full_pt);easy | 
        eapply valid_suffix_valid_global with (xs:=full_pt);easy];
        red; repeat split;try easy;
        assert (Hqq0: q <> q0) by (red;intros; eapply Htypp0;subst;constructor);
        try solve
        [
        intros; eapply Htypp0; econstructor 4 with (g:=lg);try exact Honthk2;easy |
        intros;
        eapply Htypp1; econstructor;try exact Honthk2;easy].
    }    
Qed.*)

Lemma head_gtt_send_not_fair : forall p q xs, wfgC (gtt_send p q xs) ->
fair_path_global (cocons (gtt_send p q xs, None) conil) -> False.
Proof.
    intros.
    pinversion H0;subst.
    red in H3.
    eapply wfgC_triv in H as [?Hwftr ?Hwftr]. eapply slist_implies_some in Hwftr0. destr_hyps.

    specialize (H3 p q x).
    assert (to_path_prop (global_comm_enabled p q x) False
(cocons (gtt_send p q xs, None) conil)).
    simpl. red. destruct x0. exists g. pfold. econstructor; try exact (eq_sym H);try easy.
    specialize (H3 H1).
    inversion H3;subst;try easy. inversion H5;subst;easy.
Qed.

Lemma forall_to_always {A:Type} (P:coseq A -> Prop) : forall ys, (forall xs, P xs) ->  alwaysCG P ys.
Proof.
    pcofix CIH.
    intros.
    pfold. destruct ys. constructor. eapply H0.
    constructor. eapply H0. right. eapply CIH. easy.
Qed.

Definition head_part p (xs : global_path) := match xs with conil => False | cocons (g,_) _ => isgPartsC p g end.
Lemma grafting_contains_prefix : forall  ctx_p p gs_p ctx_q gs_q q g,
    typ_p_gtth gs_q ctx_q q g ->
    usedCtx gs_q ctx_q ->
    typ_p_gtth gs_p ctx_p p g ->
    usedCtx gs_p ctx_p ->
    is_tree_proper_prefix ctx_q ctx_p ->
    ishParts q ctx_p.
    Proof.
        induction ctx_p using gtth_ind_ref.
        {
            intros * Hgraftq Husedq Hgraftp Husedp Hpref.
            inversion Hpref.   
        }
        {
            intros * Hgraftq Husedq Hgraftp Husedp Hpref.
            rename q into r, q0 into q, p into s, p0 into p.
            destruct Hgraftq as [?Hgraftq [?Hgraftq ?Hgraftq]].
                destruct Hgraftp as [?Hgraftp [?Hgraftp ?Hgraftp]].
                
            inversion Hpref;subst.
            {
                inversion Hgraftp;subst.
                inversion Hgraftq;subst.
                eapply Forall_prop in Hgraftq1;try exact H2.
                destruct Hgraftq1;try easy.
                destruct H0 as [q0 [lsg [?Htr | [?Htr | ?Htr]]]];
                try solve [
                    inversion Htr;subst; try eapply ha_sendp;try eapply ha_sendq].
                
            }
            {
                inversion Hgraftp;subst.
                eapply slist_implies_some in H6;destr_hyps.
                eapply Forall_prop in H;try exact H0;tac_sanitize.
                eapply ha_sendr;try exact H0;
                rename x into n, xs into ghs_p, xs0 into ghs_q, x1 into sr, x2 into gh.
                1-2:red;intros;subst;subtac_triv_isparts_false.
                eapply Forall2_prop_l in H2;try exact H0;tac_sanitize.
                eapply Forall2_prop_r in H7;try exact H0;tac_sanitize.
                inversion Hgraftq;subst.
                eapply Forall2_prop_l in H11;try exact H5;tac_sanitize.
                rewrite H2 in H3;inversion H3;subst.

                inversion Husedp;subst. 
                eapply Forall2_prop_l in H13;try exact H0;tac_sanitize.

                
                inversion Husedq;subst. 
                eapply Forall2_prop_l in H15;try exact H2;tac_sanitize.
                
                eapply H1 with (p:=p) (gs_q:=x0) (ctx_q:=x7) (g:=x6) (gs_p:=x1);try easy.
                repeat split;
                eapply mergeCtx_onth_subset in H3;try exact H13.
                eapply decidable_helper.typh_with_less;try exact H3;try easy.
                intros. apply Hgraftq0. eapply ha_sendr;try exact H2;try easy.
                1-2:red;intros;subst;subtac_triv_isparts_false.
                eapply Forall_subset;try exact H3;try tauto.
                
                repeat split;
                eapply mergeCtx_onth_subset in H11;try exact H7.
                eapply decidable_helper.typh_with_less;try exact H11;try easy.
                intros. apply Hgraftp0. eapply ha_sendr;try exact H0;try easy.
                1-2:red;intros;subst;subtac_triv_isparts_false.
                eapply Forall_subset;try exact H11;try tauto.
            }
        }
    Qed.

Lemma forall_to_always2 P : (forall xs, fair_path_global xs -> global_valid_pathC xs -> 
wfg_global_path xs -> P xs) -> (forall xs, fair_path_global xs -> global_valid_pathC xs -> 
wfg_global_path xs -> alwaysCG P xs).
Proof.
    intros * Hassum. pcofix CIH. 
    intros xs Hfair Hvalid Hwfgp.
    destruct xs. pfold; constructor; eapply Hassum;try pfold;try constructor;crush;constructor;easy.
    
    pfold; constructor. eapply Hassum;easy. right. 
    eapply CIH;try solve [subtac_tail_solve | subtac_tail_valid].
Qed.

Lemma always_suffix {A:Type}: forall (P : coseq A -> Prop) ys xs, alwaysCG P xs -> is_suffix ys xs -> alwaysCG P ys.
Proof.
    intros.
    induction H0;try easy. eapply IHis_suffix. pinversion H;subst;easy.
Qed.

Definition head_grafting_is p ctx_p gs_p (xs:global_path) := match xs with conil => False
    | cocons (g,l) xs => typ_p_gtth gs_p ctx_p p g /\ usedCtx gs_p ctx_p end.

Definition head_trans_involving_p r (xs:global_path) := match xs with 
    | cocons (_,Some (lcomm p q ell)) _ => p=r \/ q=r
    | _ => False end.

Definition head_grafting_height_le p hgt_bound (u:global_path) := match u with 
    | cocons (g,l) xs => exists ctx'_p gs'_p, typ_p_gtth  gs'_p ctx'_p p g /\ usedCtx gs'_p ctx'_p /\
    gtth_height ctx'_p <= hgt_bound
    | _ => True end.

Definition head_grafting_contains p q (u:global_path) := match u with 
    | cocons (g,l) xs => exists ctx'_p gs'_p, 
    typ_p_gtth gs'_p ctx'_p p g /\ usedCtx gs'_p ctx'_p /\
    ishParts q ctx'_p
    | _ => True end.

Lemma until_suf {A:Type} (P:coseq A -> Prop) (Q: coseq A -> Prop) :
    forall xs, until P Q xs -> Q xs \/ 
    exists a xsuf, is_suffix (cocons a xsuf) xs /\ P (cocons a xsuf) /\ 
    Q xsuf.
Proof.
    intros.
    induction H;try tauto.
    right. destruct IHuntil. exists x, xs. repeat split;try tauto. constructor.
    destr_hyps.
    exists x0, x1. repeat split;try tauto. constructor. easy.
Qed.

Lemma suffix_tail {A:Type}: forall (a:A) xs ys, is_suffix (cocons a ys) xs ->
is_suffix ys xs.
Proof.
    intros.
    dependent induction H. constructor. constructor.
    specialize (IHis_suffix a ys eq_refl).
    constructor. easy.
Qed.

Lemma q_still_in_grafting_after_step : forall ctx_p gs_p ctx'_p gs'_p p q s ell t g g',
typ_p_gtth gs_p ctx_p  p g ->
ishParts q ctx_p -> gttstepC g g' s t ell -> s <> q -> t <> q -> t <> p -> s <> p ->
 typ_p_gtth gs'_p ctx'_p  p g' -> ishParts q ctx'_p.
Proof.
    intros * Hgraftp Hishparts Hstep ?Hneq ?Hneq ?Hneq ?Hneq Hgraftp'.
Admitted.

Definition head_helper_prop p q hgt_bound (u :global_path) :=   match u with 
    | cocons (g,l) xs => exists ctx'_p gs'_p, typ_p_gtth  gs'_p ctx'_p p g /\ usedCtx gs'_p ctx'_p /\
    gtth_height ctx'_p <= hgt_bound /\ ishParts q ctx'_p
    | _ => True end.


Lemma grafting_height_decreases_until :  forall ctx_p p lcs q gs_p xs hgt_bound, 
fair_path_global xs -> 
global_valid_pathC xs ->  wfg_global_path  xs ->
head_grafting_is p ctx_p gs_p xs -> 
ishParts q ctx_p ->
head_proj_is p (ltt_recv q lcs) xs ->
gtth_height ctx_p <= hgt_bound ->
weak_untilC (    
head_helper_prop p q hgt_bound /1\ head_trans_not_involving_p p /1\
head_trans_not_involving_p q /1\ head_proj_is_nil_true p (ltt_recv q lcs)
)
(head_trans_involving_p q) xs.
Proof.
    intros * Hfair Hvalid Hwfgp Hgraft Hishparts Hprojp Hle.
    generalize dependent gs_p.
    generalize dependent ctx_p.
    generalize dependent xs.
    pcofix CIH.
    
    destruct xs.
    {
        intros. red in Hprojp. easy.
    }
    {
        intros.
        destruct p0 as [g l].
        assert(Hwfg : wfgC g) by
        (eapply wfg_global_path_head;try exact Hwfgp).
        assert(Hprojable : projectableA g) 
        by (pinversion Hwfgp;subst; red in H1;tauto).   
        destruct l.
        {
            pose proof Hvalid as Hvalid'.
            pinversion Hvalid;try apply valid_path_mon;subst.
            destruct l;try easy.
            rename n into s, n0 into t, n1 into ell.
            pfold.
            destruct (Nat.eq_dec s q);
            destruct (Nat.eq_dec t q);subst;try tauto;red in H3;
            try solve [
                pinversion H3;try apply step_mon;tauto |
                constructor 1;simpl;tauto].

            destruct (Nat.eq_dec s p);
            destruct (Nat.eq_dec t p);subst;try tauto;red in H3.
            {
                pinversion H3;try apply step_mon;tauto.   
            }
            {
                eapply proj_cont_pq_step in H3 as Hlocals;try easy.
                red in Hprojp. 
                destr_hyps.
                eapply proj_inj in H;try exact Hprojp;try easy.
            }
            {
                
                eapply proj_cont_pq_step in H3 as Hlocals;try easy.
                red in Hprojp. 
                destr_hyps.
                eapply proj_inj in H0;try exact Hprojp;try easy.
                inversion H0;subst.
                constructor 1. simpl. tauto. 
            }
            {
            simpl in Hgraft;destruct Hgraft as [?Hgraft ?Hgraft];                rename x into g'.
            constructor 2.
            split;[split | ];[split | |];simpl;
            try solve [
            exists ctx_p, gs_p;tauto |
            intros;
            destruct H;subst;tauto | simpl in Hprojp;easy].

                
                right.
                eapply graft_height_after_step in H3 as Hgraftn; try exact Hgraft;try easy.
                destr_hyps.
                 
                eapply CIH with (ctx_p:=x) (gs_p:=x0);try solve 
                [subtac_tail_solve | subtac_tail_valid].
                simpl.
                simpl in Hprojp.
                eapply typ_after_step_r_redux in H3;try exact Hprojp;try easy. destr_hyps;subst;easy.
                
                eapply q_still_in_grafting_after_step;try exact H3;try exact Hgraft;try exact H;try easy.
                all:crush.                
            }
        }
        {
            pinversion Hvalid;try apply valid_path_mon;subst.
            pfold.
            constructor 2; try easy.
            split;[split |];[split | |];simpl;try solve
            [exists ctx_p, gs_p;crush];try easy.
            
            left. pfold. constructor 3. easy.    
        }
    }
Qed.

Lemma forall_local_step : forall ctx_p p gs_p xs, 
fair_path_global xs -> 
global_valid_pathC xs ->  wfg_global_path  xs ->
head_grafting_is p ctx_p gs_p xs -> 
 (head_proj_eventually_takes_step p) xs .
Proof.
    induction ctx_p using gtth_ind_by_height.
    Print head_proj_eventually_takes_step.
    
    rename H into IH.

    
    intros * Hfair Hvalid Hwfgp Hgraft. destruct xs;try easy.
    
    destruct p0 as [g l].
    red in Hgraft. destr_hyps. red in H. destr_hyps. 
    rename H into Hgraft_p, H1 into Hishparts, H2 into Hgraft_pfa, H0 into Hused.

    assert (Hwfg : wfgC g) by (eapply wfg_global_path_head;try exact Hwfgp;easy); 
    assert (Hprojable : projectableA g) by
    (eapply projable_global_path_head; try exact Hwfgp;easy).
    specialize (Hprojable p) as Hprojp. destruct Hprojp as [Tp Hprojp].
    assert(Hgraftp_p : typ_p_gtth gs_p ctx_p p g) by (red;crush).
    destruct Tp.
    {
        intros;split;intros;subst;try eapply proj_inj in H;try exact Hprojp;easy.   
    }
    {
        rename n into q, l0 into lcs.
        assert (Hispartsq:isgPartsC q g) by (eapply proj_contains_q_implies_part_recv in Hprojp;easy).
        specialize (Hprojable q) as Hprojq. destruct Hprojq as [Tq Hprojq].
        eapply balanced_to_tree in Hispartsq as Hgraftq; try easy.
        destruct Hgraftq as [ctx_q [gs_q [?Htypq [?Htypq [?Htypq ?Htypq]]]]];try easy.
        assert(Htyp_q : typ_p_gtth gs_q ctx_q q g) by (red;crush).
        eapply multigrafting_lemma_recv with (p:=p) (q:=q) (xs:=lcs) (Tq:=Tq) in 
        Hwfg as Hmg; 
        try exact Htyp_q;try exact Hgraftp_p;try easy.
        destruct Hmg.
        {
            destruct Tq.
            {
                exfalso; eapply pmergeCR_s;try exact Hprojq;easy.
            }
            {
                rename n into r, l0 into lcqs.
                assert(Hnt: eventually (headComm_global r q) (cocons (g,l) xs)).
                {
                    eapply IH with (gh':=ctx_q) (gs_p:=gs_q) (p:=q) in Hfair as IH_use;try easy.
                    red in IH_use.
                    specialize (IH_use _ Hprojq). eapply IH_use. reflexivity.

                    eapply proper_prefix_height_le;try easy.
                    eapply typ_gtth_means_wfgtth;try exact Htypq.
                    eapply typ_gtth_means_wfgtth;try exact Hgraft_p.
                }
                assert(Hnt' : eventually (head_trans_involving_p q) (cocons (g,l) xs)).
                {
                    eapply eventually_P_iff_P_suffix in Hnt as Hnt_suf.
                    destruct Hnt_suf as [xsuf [?Hntsuf ?Hntsuf]].
                    red in Hntsuf0.
                    destruct xsuf;try easy.
                    destruct p0;destruct o;try easy. destruct l0;try easy.
                    destruct Hntsuf0;subst.
                    rewrite eventually_P_iff_P_suffix. 
                    exists (cocons (g0, Some (lcomm n n0 n1)) xsuf).
                    split;try easy. simpl;tauto.
                }
                eapply grafting_height_decreases_until with (ctx_p:=ctx_p)
                (gs_p:=gs_p) (p:=p) (q:=q) (lcs:=lcs) in Hfair as Hwft;try easy;
                try solve [simpl; exists lcs; easy |
                eapply grafting_contains_prefix;try exact H;
                try exact Hgraftp_p;try exact Htyp_q;try easy].
                eapply weak_untilC_to_until in Hwft;try exact Hnt;try easy. 

              
                assert(Hev' : 
                eventually (head_helper_prop p q (gtth_height ctx_p) /1\     
                 head_proj_is p (ltt_recv q lcs) /1\             
                 head_trans_involving_p q) (cocons (g,l) xs)).
                 {
                    eapply until_suf in Hwft as Hunt_suf.
                    destruct Hunt_suf.
                    {
                        constructor 1. split;try easy. simpl;split;try easy. 
                        exists ctx_p, gs_p. crush.
                        eapply grafting_contains_prefix;try exact H; try exact Htyp_q;
                        try exact Hgraftp_p;try easy.       
                    }
                    {
                        destruct H0 as [unthead [untsuf Hsuf]].
                        destruct Hsuf as [?Hsuf [?Hsuf ?Hsuf_t] ].
                        destruct Hsuf0 as [[?Hsuf  ?Hsuf] ?Hsuf].
                        rewrite eventually_P_iff_P_suffix. exists untsuf.
                        repeat split.
                        {
                            eapply suffix_tail;try exact Hsuf.
                        }
                        {
                            assert(Hvalid_suf: global_valid_pathC (cocons unthead untsuf)).
                            {
                                eapply valid_suffix_valid_global;try exact Hvalid;try easy.   
                            }
                            pinversion Hvalid_suf;subst;try apply valid_path_mon.
                            simpl in Hsuf_t;try easy.
                            red in H3;destruct l0;try easy.
                            rename n into s, n0 into t, n1 into ell.
                            simpl in Hsuf0, Hsuf1, Hsuf2.
                            simpl.
                            destr_hyps.
                            rename x1 into gs'_p, x0 into ctx'_p.
                            eapply graft_height_after_step in H3  as Hgstep;try exact H0;try easy.
                            destr_hyps. exists  x0, x1;split;try tauto;split;try tauto.
                            split;[crush |]. 
                            eapply q_still_in_grafting_after_step;try exact H0;try exact Hgstep;
                            try exact H7;try exact H3;try easy.
                            all:red;intros;subst;tauto.
                        }
                        {
                            assert(Hvalid_suf: global_valid_pathC (cocons unthead untsuf)).
                            {
                                eapply valid_suffix_valid_global;try exact Hvalid;try easy.   
                            }
                            simpl.
                            destruct Hsuf0 as [?Hsuf ?Hsuf].
                            destruct unthead.
                            simpl in Hsuf0, Hsuf1, Hsuf2, Hsuf3.
                            destruct o;try easy;
                            try solve [
                                pinversion Hvalid_suf;try apply valid_path_mon;
                                subst; simpl in Hsuf_t;easy].
                                destruct l0;
                                try solve [
                                pinversion Hvalid_suf;try apply valid_path_mon;
                                subst; simpl in Hsuf_t;easy].
                            pinversion Hvalid_suf;try apply valid_path_mon;subst.
                            red in H4.
                            simpl. eapply typ_after_step_r_redux in H4;try exact Hsuf2;try easy.
                            destr_hyps;subst;easy.
                            1-2:
                            red in Hwfgp;
                            rewrite always_P_iff_P_suffix in Hwfgp;
                            specialize (Hwfgp _ Hsuf);simpl in Hwfgp;tauto.
                            1-2:simpl in Hsuf3, Hsuf1;red;intros;subst;tauto.
                        }
                        {
                            easy.   
                        }
                    }
                 }

                 rewrite eventually_P_iff_P_suffix in Hev'. destr_hyps.
                 rename x into xsuf.
                 assert (Hvalid' : global_valid_pathC xsuf) by
                 (eapply valid_suffix_valid_global;try exact H0;try easy).
                 pose proof H2 as Hht.
                 pinversion Hvalid';try apply valid_path_mon;subst;simpl in H2;try easy.
                 destruct l0;try easy. red in H5.
                 
                simpl in H1. destr_hyps.
                
                assert(Hpneq1 : p <> n) by admit.
                
                assert(Hpneq2 : p <> n0) by admit.
                eapply graft_height_decreases_strictly with (q:=q) 
                in H5 as Hnew_height;try exact H1;try easy;try solve [
                    destruct H2;subst;tauto
                ].
                rename x1 into gs'_p, x0 into ctx'_p.
                destr_hyps.
                rename x0 into gx', x1 into gs'.
                assert(head_grafting_is p gx' gs' (cocons (x, l') xs0)).
                {
                    simpl. tauto.   
                }
                
                eapply IH in H12; try easy.
                assert (Hprojinv: projectionC x p (ltt_recv q lcs)).
                {
                    simpl in H3.
                    eapply typ_after_step_r_redux in H5;try exact H3;destr_hyps;subst;try easy.
                    1-2:red in Hwfgp;
                            rewrite always_P_iff_P_suffix in Hwfgp;
                            specialize (Hwfgp _ H0);simpl in Hwfgp;tauto.
                }
                simpl in H12.
                specialize (H12 _ Hprojinv).
                destruct H12.
                specialize (H13 _ _ eq_refl) as Himp.
                simpl;intros.
                eapply proj_inj in H14;try exact Hprojp;subst;try easy.
                split;intros;try easy.
                inversion H14;subst.
                
                Lemma eventually_suffix2 {A:Type}: forall (P : coseq A -> Prop) xs ys, 
                eventually P ys -> is_suffix ys xs -> eventually P xs.
                Proof.
                    intros * Hev.
                    induction Hev. intros. rewrite eventually_P_iff_P_suffix. exists xs0;easy.

                    intros. eapply IHHev. eapply suffix_tail;try exact H.
                Qed.
                eapply eventually_suffix2;try exact Himp;try easy.
                eapply suffix_tail;try exact H0.
                crush.
                eapply always_suffix;try exact Hfair;try easy.
                eapply suffix_tail;try exact H0.
                
                eapply always_suffix;try exact Hwfgp;try easy.
                eapply suffix_tail;try exact H0.
            }
            admit.
        }
        {
            intros;split;intros;subst;eapply proj_inj in Hprojp as Hprjinj;try exact H0;try easy.
            inversion Hprjinj;subst;clear Hprjinj;clear H0.
            eapply multigrafting_lemma_1_recv with (xs:=lcs) (Tq:=Tq) (p:=p) (q:=q) in Hgraftp_p as 
            Hprojq2;try exact Hgraft_p;
            try exact Htyp_q;try easy.
            destruct Hprojq2;subst.
            pinversion Hfair;subst.
            eapply matching_proj_enables_step in Hprojp as Hstep;try exact Hprojq;try easy.
            destruct Hstep as [g' [ell Hstep]].
            eapply projection_step_label in Hstep as Hslabel;try exact Hprojp;try exact Hprojq;try easy.
            destruct Hslabel as [s [s' [Tq' [Tp' [?Hslabel ?Hslabel]]]]].
            red in H2.
            eapply H2 with (n:=ell). simpl. exists g'. easy.
        }
    }
    admit.
            Admitted.
    

    
Lemma forall_local_step_helper: forall p q lcs ctx_p gs_p xs,  
fair_path_global xs -> global_valid_pathC xs -> wfg_global_path xs ->
head_proj_is p (ltt_recv q lcs) xs-> 
head_grafting_is p ctx_p gs_p  xs ->
(forall gh' : gtth,
        gtth_height gh' < gtth_height ctx_p ->
        forall (p : opt_lbl) (gs_p : list (option gtt))
        (xs : coseq (gtt * option label)),
        fair_path_global xs ->
        global_valid_pathC xs ->
        wfg_global_path xs ->
        head_grafting_is p gh' gs_p xs ->
        head_proj_eventually_takes_step p xs) -> 
        eventually (head_proj_is_send q p) xs.
Proof.
    intros * Hfair Hvalid Hwfgp Hprojp Hgraftp IH_og.
    destruct xs;simpl in Hprojp;try easy.
    destruct p0 as [g l];simpl in Hprojp.
    eapply projection_implies_part_recv in Hprojp as Hispartsp.
    assert (Hwfg : wfgC g) by (eapply wfg_global_path_head;try exact Hwfgp;easy); 
    assert (Hprojable : projectableA g) by
    (eapply projable_global_path_head; try exact Hwfgp;easy).
    simpl in Hgraftp. destruct Hgraftp as [Hgraftp Hused].
    pose proof Hgraftp as Hgraftp_p.
    destruct Hgraftp as [?Hgraftp [?Hgraftp  ?Hgraftp ]].
    specialize (Hprojable q) as Hprojq. destruct Hprojq as [Tq Hprojq].
    eapply local_types_corr_recv_and_projH with (p:=p) (q:=q) (Tq:=Tq) in Hprojp as Hlgraft;
    try exact Hgraftp_p;try easy.
    destruct Hlgraft as [ls [lx [?Hlgraft [?Hlgraft ?Hlgraft]]]].
    clear Hlgraft0.
    generalize dependent g. generalize dependent gs_p.
    generalize dependent ctx_p.
    generalize dependent p.  revert q lcs l xs . generalize dependent Tq. revert ls.
    induction lx using ltth_ind_ref.
    {
        intros.   
        eapply restricted_grafting_recv in Hgraftp1;try exact Hprojp;
            try exact Hgraftp;try easy.
            inversion Hlgraft;subst. 
            eapply Forall2_prop_l in Hlgraft1;try exact H0;tac_sanitize.
            eapply Forall_prop in Hgraftp1;try exact H1. 
            destruct Hgraftp1;try easy.
            destr_hyps. inversion H;subst. 
            pinversion H3;subst;try easy;try apply proj_mon.
            
            subtac_triv_isparts_false. eapply wfg_list_by_grafting in Hgraftp;try easy. destr_hyps.
            eapply Forall_prop in H5;try easy;try exact H1;try easy;tac_sanitize;easy.

            
            constructor 1. simpl. exists ys;easy.   
    }
    {
        intros. rename H into IH_new.
        rename q into r, q0 into q.
        assert(Hispartsq: isgPartsC q g) by (eapply proj_contains_q_implies_part_recv in Hprojp;try easy).
        eapply balanced_to_tree in Hispartsq as Hgraftq;try easy.
        destruct Hgraftq as [ctx_q [gs_q [?Hgraftq [?Hgraftq [?Hgraftq Husedq]]]]].
        assert(Hgraftp_q : typ_p_gtth gs_q ctx_q q g) by (red;tauto).

        eapply multigrafting_lemma_recv with (p:=p) (q:=q) (Tq:=Tq) in Hprojp as Hmg;
        try exact Hgraftp_p;try exact Hgraftp_q;try easy.
        assert (Hwfgth_p: wfgtth ctx_p) by 
        (eapply typ_gtth_means_wfgtth in Hgraftp; easy).
        assert (Hwfgth_q: wfgtth ctx_q) by 
        (eapply typ_gtth_means_wfgtth in Hgraftq; easy).
        destruct Hmg as [Hmg | Hmg].
        {
            eapply proper_prefix_height_le in Hmg as Hheights;try easy.
            eapply IH_og  with (xs:=(cocons (g,l) xs0)) (p:=q) (gs_p:=gs_q) in Hheights;try easy.
            red in Hheights.
            inversion Hlgraft;subst;rename H3 into Hlgraft_fa2.
            specialize (Hheights _ Hprojq).
            destruct Hheights as [Hev_step  _].
            specialize (Hev_step _ _ eq_refl). destruct Hev_step as [ell [s [Tq' [Honthk Hev2]]]].
            
            eapply Forall2_prop_l in Hlgraft_fa2;try exact Honthk;tac_sanitize.
            eapply Forall_prop in IH_new;try exact H0;tac_sanitize.
            rename x into s, x3 into lx', x2 into Tq', H0 into Honthxs, H2 into Htyp', H1 into IH_use.

            eapply eventually_P_iff_P_suffix in Hev2 as Hev_suf.
            destruct Hev_suf as [xsuf [Hxsuf1 Hxsuf2]].
            destruct xsuf;try easy.
            destruct p0 as [g' l'].
            destruct l';try easy.
            destruct l0;try easy.
            destruct xsuf;try easy.
            (*
            destruct xs0.
            inversion Hev2;try easy.
            destruct p0 as [g' l'].
            constructor 2.
            assert(projectionC g' p (ltt_recv q lcs)).
            {
                admit.   
            }*)
            (*insterad of g pass g'*)
            eapply IH_use with (ls:=ls) (Tq:=Tq') (gs_p:=gs_p) (lcs:=lcs);try easy.
        } 
        Search "multigraft".
        Search is_tree_proper_prefix.   
    }
    revert p q lcs l xs ls.

Lemma forall_local_step : forall ctx_p p gs_p xs, 
fair_path_global xs -> 
global_valid_pathC xs ->  wfg_global_path  xs ->
head_grafting_is p ctx_p gs_p xs -> 
 (head_proj_eventually_takes_step p) xs .
Proof.
    induction ctx_p using gtth_ind_by_height.
    
    rename H into IH.

    
    intros * Hfair Hvalid Hwfgp Hgraft. destruct xs;try easy.
    
    destruct p0 as [g l].
    red in Hgraft. destr_hyps. red in H. destr_hyps. 
    rename H into Hgraft_p, H1 into Hishparts, H2 into Hgraft_pfa, H0 into Hused.

    assert (Hwfg : wfgC g) by (eapply wfg_global_path_head;try exact Hwfgp;easy); 
    assert (Hprojable : projectableA g) by
    (eapply projable_global_path_head; try exact Hwfgp;easy).
    destruct (decidable_isgPartsC g p) as [Hispartsp | Hispartpsp];try easy.
    eapply typ_gtth_means_wfgtth in Hgraft_p as Hwfgth.
    assert (Hgraftp_p : typ_p_gtth gs_p ctx_p p g)
    by (red;crush);
    generalize dependent gs_p;
    generalize dependent g;
    generalize dependent p;
    revert Hwfgth l. 
    induction ctx_p using gtth_ind_by_height.
    intros.
    specialize (Hprojable p) as Hprojp;destruct Hprojp as [Tp Hprojp].
    destruct Tp; try solve [eapply pmergeCR_s in Hprojp;easy];
    rename n into q, l0 into lcs.

    assert (Hispartsq:isgPartsC q g) by (eapply proj_contains_q_implies_part_recv in Hprojp;easy).
    specialize (Hprojable q) as Hprojq. destruct Hprojq as [Tq Hprojq].
    eapply balanced_to_tree in Hispartsq as Hgraftq; try easy.
    destruct Hgraftq as [ctx_q [gs_q [?Htypq [?Htypq [?Htypq ?Htypq]]]]];try easy.
    assert(Htyp_q : typ_p_gtth gs_q ctx_q q g) by (red;crush).
    eapply multigrafting_lemma_recv with (p:=p) (q:=q) (xs:=lcs) (Tq:=Tq) in 
    Hwfg as Hmg; 
    try exact Htyp_q;try exact Hgraftp_p;try easy.
    assert(Hevqp : eventually (head_proj_is_send q p) (cocons (g, l) xs)).
    {
        destruct Hmg;
                [
                    |
                eapply multigrafting_lemma_1_recv with (p:=p) (q:=q) (Tq:=Tq) in Hwfg as Htr;
                try exact Hprojp;
                try exact Hgraftp_p;
                try exact Htyp_q; try easy;
                destr_hyps; subst;constructor 1;exists x;simpl; easy].
        Check local_types_corr_send_and_projH.
        eapply local_types_corr_recv_and_projH with (p:=p) (q:=q) (xs:=lcs) (Tq:=Tq)
        in Hwfg as Hlocal_graft;try exact Hgraftp_p;try easy.
        destruct Hlocal_graft as [ls [lx [?Hlg [?Hlg ?Hlg]]]].
        generalize dependent g.
        generalize dependent lx.
        induction lx using ltth_ind_ref.
        {
            intros.
            eapply restricted_grafting_recv in Hgraft_pfa;try exact Hprojp;
            try exact Hgraft_p;try easy.
            inversion Hlg;subst. eapply Forall2_prop_l in Hlg1;try exact H2;tac_sanitize.
            eapply Forall_prop in Hgraft_pfa;try exact H3. destruct Hgraft_pfa;try easy.
            destr_hyps. inversion H1;subst.  pinversion H5;subst;try easy;try apply proj_mon.
            subtac_triv_isparts_false. eapply wfg_list_by_grafting in Hgraft_p;try easy. destr_hyps.
            eapply Forall_prop in H7;try easy;try exact H3;try easy;tac_sanitize;easy.
            
            constructor 1. simpl. exists ys;easy.   
        }
        {

        } 

Lemma forall_local_step : forall p xs,  
fair_path_global xs -> 
global_valid_pathC xs ->  wfg_global_path xs -> 
 head_proj_eventually_takes_step p xs.
Proof.
    intros p xs.  
    intros * Hfair Hvalid Hwfgp.

    destruct xs.   easy.
    
    destruct p0 as [g l].
    
    
    assert (Hwfg : wfgC g) by (eapply wfg_global_path_head;try exact Hwfgp;easy); 
    assert (Hprojable : projectableA g) by
    (eapply projable_global_path_head; try exact Hwfgp;easy).
    destruct (decidable_isgPartsC g p) as [Hispartsp | Hispartpsp];try easy.
    {
        eapply balanced_to_tree in Hispartsp as Hgraftp;try easy;
        destruct Hgraftp as [ctx_p [gs_p [?Hgraftp [?Hgraftp [?Hgraftp ?Hgraftp ]]]]];
        eapply typ_gtth_means_wfgtth in Hgraftp as Hwfgth;
        assert (Hgraftp_p : typ_p_gtth gs_p ctx_p p g)
        by (red;crush);
        generalize dependent gs_p;
        generalize dependent g;
        generalize dependent p;
        revert Hwfgth l.
        induction ctx_p using gtth_ind_by_height.
        {
            intros.
            specialize (Hprojable p) as Hprojp;destruct Hprojp as [Tp Hprojp].
            destruct Tp; try solve [eapply pmergeCR_s in Hprojp;easy];
            rename n into q, l0 into lcs.

            assert (Hispartsq:isgPartsC q g) by (eapply proj_contains_q_implies_part_recv in Hprojp;easy).
            specialize (Hprojable q) as Hprojq. destruct Hprojq as [Tq Hprojq].
            eapply balanced_to_tree in Hispartsq as Hgraftq; try easy.
            destruct Hgraftq as [ctx_q [gs_q [?Htypq [?Htypq [?Htypq ?Htypq]]]]];try easy.
            assert(Htyp_q : typ_p_gtth gs_q ctx_q q g) by (red;crush).
            eapply multigrafting_lemma_recv with (p:=p) (q:=q) (xs:=lcs) (Tq:=Tq) in 
            Hwfg as Hmg; 
            try exact Htyp_q;try exact Hgraftp_p;try easy.
            assert(Hevqp : eventually (head_proj_is_send q p) (cocons (g, l) xs)).
            {
                destruct Hmg;
                [
                    |
                eapply multigrafting_lemma_1_recv with (p:=p) (q:=q) (Tq:=Tq) in Hwfg as Htr;
                try exact Hprojp;
                try exact Hgraftp_p;
                try exact Htyp_q; try easy;
                destr_hyps; subst;constructor 1;exists x;simpl; easy].

                
                eapply local_types_corr_recv_and_projH with (q:=q) (xs:=lcs) (Tq:=Tq) in 
                Hgraftp_p as Hlgraft;
                try easy.
                destruct Hlgraft as [lsq [lxq [?Hlgraft [?Hlgraft ?Hlgraft]]]].

                assert(Hwfgthq : wfgtth ctx_q) by (eapply typ_gtth_means_wfgtth in Htypq;easy).
                
                
                eapply always_local_step_implies_ev_grafting with (Tp:=Tq) (ls:=lsq) (lx:=lxq);try easy.
                eapply H with (gh':=ctx_q) (gs_p:=gs_q);try easy.
                eapply proper_prefix_height_le;easy.
                    
                red. repeat split;try tauto. 
                
                eapply projectionH_ishparts;try exact Hlgraft0;try easy.

                intros.
                eapply typ_ltth_fills_holes in H1;try exact Hlgraft. destr_hyps.
                red in Hlgraft1.
                eapply Forall2_prop_l in Hlgraft1;try exact H1;tac_sanitize.
                
                eapply restricted_grafting_recv in Hgraftp as Hrg;try exact Hprojp;try easy. 
                eapply Forall_prop in Hrg;try exact H3;tac_sanitize.
                pinversion H5;try apply proj_mon;try easy;subst.
                {
                    subtac_triv_isparts_false. 
                    eapply wfg_list_by_grafting in Hgraftp;try easy. destr_hyps.
                    eapply Forall_prop in H6;try exact H3;tac_sanitize;try easy.
                }
                exists ys;easy.
            }
            assert (Hf: head_proj_eventually_takes_step p (cocons (g, l) xs)). admit.
            clear.
            pcofix CIH.
            pfold. constructor. admit.

            destruct xs. left. pfold. constructor. easy.

            right. destruct p0. eapply CIH.
            assert(Headpr: head_proj_is_recv p q (cocons (g, l) xs)) by (red;exists lcs;easy).
            

            eapply no_trans_until_heads_match_recv with (p:=p) (q:=q) in Hwfgp as Hnt;try easy.
            eapply weak_untilC_to_until in Hnt;try easy.

            eapply no_trans_implies_same_proj_recv with (lcs:=lcs) in Hnt;try easy.

            
            rewrite eventually_and in Hnt.
            eapply matching_head_proj_to_comm in Hnt;try easy.

            pfold. constructor. 
            eapply eventually_P_iff_P_suffix in Hnt. destruct Hnt as [xsuf [Hsuf Hhcm]].

            destruct xsuf;try easy.
            destruct p0;destruct o;try destruct l0;try easy.

            destruct (Nat.eqb  q n) eqn:Hg1;destruct (Nat.eqb p n0) eqn:Hg2;subst;red in Hhcm;
            rewrite Hg1 in Hhcm; try rewrite Hg2 in Hhcm;try easy.
            try rewrite Nat.eqb_eq in Hg1, Hg2; apply eq_sym in Hg1, Hg2. subst.
            clear Hhcm. rename n1 into ell.

(*by paco*)
(*
Lemma always_local_step : forall p xs,  
fair_path_global xs -> 
global_valid_pathC xs ->  wfg_global_path xs -> 
alwaysCG (head_proj_eventually_takes_step p) xs.
Proof.
    intros p xs.  
    intros * Hfair Hvalid Hwfgp.
    

    destruct xs.  pfold;constructor; easy.
    
    destruct p0 as [g l].
    
    
    assert (Hwfg : wfgC g) by (eapply wfg_global_path_head;try exact Hwfgp;easy); 
    assert (Hprojable : projectableA g) by
    (eapply projable_global_path_head; try exact Hwfgp;easy).
    destruct (decidable_isgPartsC g p) as [Hispartsp | Hispartpsp];try easy.
    {
        eapply balanced_to_tree in Hispartsp as Hgraftp;try easy;
        destruct Hgraftp as [ctx_p [gs_p [?Hgraftp [?Hgraftp [?Hgraftp ?Hgraftp ]]]]];
        eapply typ_gtth_means_wfgtth in Hgraftp as Hwfgth;
        assert (Hgraftp_p : typ_p_gtth gs_p ctx_p p g)
        by (red;crush);
        generalize dependent gs_p;
        generalize dependent g;
        generalize dependent p;
        revert Hwfgth l.
        induction ctx_p using gtth_ind_by_height.
        {
            intros.
            specialize (Hprojable p) as Hprojp;destruct Hprojp as [Tp Hprojp].
            destruct Tp; try solve [eapply pmergeCR_s in Hprojp;easy];
            rename n into q, l0 into lcs.

            assert (Hispartsq:isgPartsC q g) by (eapply proj_contains_q_implies_part_recv in Hprojp;easy).
            specialize (Hprojable q) as Hprojq. destruct Hprojq as [Tq Hprojq].
            eapply balanced_to_tree in Hispartsq as Hgraftq; try easy.
            destruct Hgraftq as [ctx_q [gs_q [?Htypq [?Htypq [?Htypq ?Htypq]]]]];try easy.
            assert(Htyp_q : typ_p_gtth gs_q ctx_q q g) by (red;crush).
            eapply multigrafting_lemma_recv with (p:=p) (q:=q) (xs:=lcs) (Tq:=Tq) in 
            Hwfg as Hmg; 
            try exact Htyp_q;try exact Hgraftp_p;try easy.
            assert(Hevqp : eventually (head_proj_is_send q p) (cocons (g, l) xs)).
            {
                destruct Hmg;
                [
                    |
                eapply multigrafting_lemma_1_recv with (p:=p) (q:=q) (Tq:=Tq) in Hwfg as Htr;
                try exact Hprojp;
                try exact Hgraftp_p;
                try exact Htyp_q; try easy;
                destr_hyps; subst;constructor 1;exists x;simpl; easy].

                
                eapply local_types_corr_recv_and_projH with (q:=q) (xs:=lcs) (Tq:=Tq) in 
                Hgraftp_p as Hlgraft;
                try easy.
                destruct Hlgraft as [lsq [lxq [?Hlgraft [?Hlgraft ?Hlgraft]]]].

                assert(Hwfgthq : wfgtth ctx_q) by (eapply typ_gtth_means_wfgtth in Htypq;easy).
                
                
                eapply always_local_step_implies_ev_grafting with (Tp:=Tq) (ls:=lsq) (lx:=lxq);try easy.
                eapply H with (gh':=ctx_q) (gs_p:=gs_q);try easy.
                eapply proper_prefix_height_le;easy.
                    
                red. repeat split;try tauto. 
                
                eapply projectionH_ishparts;try exact Hlgraft0;try easy.

                intros.
                eapply typ_ltth_fills_holes in H1;try exact Hlgraft. destr_hyps.
                red in Hlgraft1.
                eapply Forall2_prop_l in Hlgraft1;try exact H1;tac_sanitize.
                
                eapply restricted_grafting_recv in Hgraftp as Hrg;try exact Hprojp;try easy. 
                eapply Forall_prop in Hrg;try exact H3;tac_sanitize.
                pinversion H5;try apply proj_mon;try easy;subst.
                {
                    subtac_triv_isparts_false. 
                    eapply wfg_list_by_grafting in Hgraftp;try easy. destr_hyps.
                    eapply Forall_prop in H6;try exact H3;tac_sanitize;try easy.
                }
                exists ys;easy.
            }
            assert (Hf: head_proj_eventually_takes_step p (cocons (g, l) xs)). admit.
            clear.
            pcofix CIH.
            pfold. constructor. admit.

            destruct xs. left. pfold. constructor. easy.

            right. destruct p0. eapply CIH.
            assert(Headpr: head_proj_is_recv p q (cocons (g, l) xs)) by (red;exists lcs;easy).
            

            eapply no_trans_until_heads_match_recv with (p:=p) (q:=q) in Hwfgp as Hnt;try easy.
            eapply weak_untilC_to_until in Hnt;try easy.

            eapply no_trans_implies_same_proj_recv with (lcs:=lcs) in Hnt;try easy.

            
            rewrite eventually_and in Hnt.
            eapply matching_head_proj_to_comm in Hnt;try easy.

            pfold. constructor. 
            eapply eventually_P_iff_P_suffix in Hnt. destruct Hnt as [xsuf [Hsuf Hhcm]].

            destruct xsuf;try easy.
            destruct p0;destruct o;try destruct l0;try easy.

            destruct (Nat.eqb  q n) eqn:Hg1;destruct (Nat.eqb p n0) eqn:Hg2;subst;red in Hhcm;
            rewrite Hg1 in Hhcm; try rewrite Hg2 in Hhcm;try easy.
            try rewrite Nat.eqb_eq in Hg1, Hg2; apply eq_sym in Hg1, Hg2. subst.
            clear Hhcm. rename n1 into ell.
*)

(*based on suffix*)
Lemma always_local_step : forall p xs,  
fair_path_global xs -> 
global_valid_pathC xs ->  wfg_global_path xs -> 
alwaysCG (head_proj_eventually_takes_step p) xs.
Proof.
    intros p xs.  
    intros * Hfair_p Hvalid_p Hwfgp_p.
    eapply always_P_iff_P_suffix.
    rename xs into xs_parent.
    intros xs Hsufxs.

    destruct xs.  constructor; easy.
    
    destruct p0 as [g l].
    

    assert (Hfair : fair_path_global (cocons (g,l) xs)).
    {
        eapply always_suffix in Hfair_p;try exact Hsufxs; easy.
    }
    

    assert (Hwfgp : wfg_global_path (cocons (g,l) xs)).
    {
        eapply always_suffix in Hwfgp_p;try exact Hsufxs; easy.
    }

    assert (Hvalid : global_valid_pathC (cocons (g,l) xs)).
    {
        eapply valid_suffix_valid_global;try exact Hsufxs; easy.
    }


    assert (Hwfg : wfgC g) by (eapply wfg_global_path_head;try exact Hwfgp;easy); 
    assert (Hprojable : projectableA g) by
    (eapply projable_global_path_head; try exact Hwfgp;easy).
    destruct (decidable_isgPartsC g p) as [Hispartsp | Hispartpsp];try easy.
    {
        eapply balanced_to_tree in Hispartsp as Hgraftp;try easy;
        destruct Hgraftp as [ctx_p [gs_p [?Hgraftp [?Hgraftp [?Hgraftp ?Hgraftp ]]]]];
        eapply typ_gtth_means_wfgtth in Hgraftp as Hwfgth;
        assert (Hgraftp_p : typ_p_gtth gs_p ctx_p p g)
        by (red;crush);
        generalize dependent gs_p;
        generalize dependent g;
        generalize dependent p;
        revert Hwfgth l xs.
        generalize dependent xs_parent.
        induction ctx_p using gtth_ind_by_height.
        {
            intros.
            specialize (Hprojable p) as Hprojp;destruct Hprojp as [Tp Hprojp].
            destruct Tp; try solve [eapply pmergeCR_s in Hprojp;easy];
            rename n into q, l0 into lcs.

            assert (Hispartsq:isgPartsC q g) by (eapply proj_contains_q_implies_part_recv in Hprojp;easy).
            specialize (Hprojable q) as Hprojq. destruct Hprojq as [Tq Hprojq].
            eapply balanced_to_tree in Hispartsq as Hgraftq; try easy.
            destruct Hgraftq as [ctx_q [gs_q [?Htypq [?Htypq [?Htypq ?Htypq]]]]];try easy.
            assert(Htyp_q : typ_p_gtth gs_q ctx_q q g) by (red;crush).
            eapply multigrafting_lemma_recv with (p:=p) (q:=q) (xs:=lcs) (Tq:=Tq) in 
            Hwfg as Hmg; 
            try exact Htyp_q;try exact Hgraftp_p;try easy.
            assert(Hevqp : eventually (head_proj_is_send q p) (cocons (g, l) xs)).
            {
                destruct Hmg;
                [
                    |
                eapply multigrafting_lemma_1_recv with (p:=p) (q:=q) (Tq:=Tq) in Hwfg as Htr;
                try exact Hprojp;
                try exact Hgraftp_p;
                try exact Htyp_q; try easy;
                destr_hyps; subst;constructor 1;exists x;simpl; easy].

                
                eapply local_types_corr_recv_and_projH with (q:=q) (xs:=lcs) (Tq:=Tq) in 
                Hgraftp_p as Hlgraft;
                try easy.
                destruct Hlgraft as [lsq [lxq [?Hlgraft [?Hlgraft ?Hlgraft]]]].

                assert(Hwfgthq : wfgtth ctx_q) by (eapply typ_gtth_means_wfgtth in Htypq;easy).
                
                
                eapply always_local_step_implies_ev_grafting with (Tp:=Tq) (ls:=lsq) (lx:=lxq);try easy.
                
                (*grafting lemma: if g ^p =ltt_send q lcs then 
                (is_tree_proper_prefix ctx_p ctx_q) until (gtth_eq ctx_p ctx_q)*)
                assert (alwaysCG (head_proj_eventually_takes_step q) (cocons (g,l) xs)).
                {
                    rewrite always_P_iff_P_suffix.
                    intros xs2 Hsuf2.
                    destruct xs2;try easy.
                    destruct p0.
                    eapply H with (gh':=ctx_q) (gs_p:=gs_q) (xs_parent :=xs_parent);try easy.   
                }
                eapply H with (gh':=ctx_q) (gs_p:=gs_q);try easy.
                eapply proper_prefix_height_le;easy.
                    
                red. repeat split;try tauto. 
                
                eapply projectionH_ishparts;try exact Hlgraft0;try easy.

                intros.
                eapply typ_ltth_fills_holes in H1;try exact Hlgraft. destr_hyps.
                red in Hlgraft1.
                eapply Forall2_prop_l in Hlgraft1;try exact H1;tac_sanitize.
                
                eapply restricted_grafting_recv in Hgraftp as Hrg;try exact Hprojp;try easy. 
                eapply Forall_prop in Hrg;try exact H3;tac_sanitize.
                pinversion H5;try apply proj_mon;try easy;subst.
                {
                    subtac_triv_isparts_false. 
                    eapply wfg_list_by_grafting in Hgraftp;try easy. destr_hyps.
                    eapply Forall_prop in H6;try exact H3;tac_sanitize;try easy.
                }
                exists ys;easy.
            }
            pcofix CIH.
            pfold. constructor. admit.

            destruct xs. left. pfold. constructor. easy.

            right. destruct p0. eapply CIH.
            assert(Headpr: head_proj_is_recv p q (cocons (g, l) xs)) by (red;exists lcs;easy).
            

            eapply no_trans_until_heads_match_recv with (p:=p) (q:=q) in Hwfgp as Hnt;try easy.
            eapply weak_untilC_to_until in Hnt;try easy.

            eapply no_trans_implies_same_proj_recv with (lcs:=lcs) in Hnt;try easy.

            
            rewrite eventually_and in Hnt.
            eapply matching_head_proj_to_comm in Hnt;try easy.

            pfold. constructor. 
            eapply eventually_P_iff_P_suffix in Hnt. destruct Hnt as [xsuf [Hsuf Hhcm]].

            destruct xsuf;try easy.
            destruct p0;destruct o;try destruct l0;try easy.

            destruct (Nat.eqb  q n) eqn:Hg1;destruct (Nat.eqb p n0) eqn:Hg2;subst;red in Hhcm;
            rewrite Hg1 in Hhcm; try rewrite Hg2 in Hhcm;try easy.
            try rewrite Nat.eqb_eq in Hg1, Hg2; apply eq_sym in Hg1, Hg2. subst.
            clear Hhcm. rename n1 into ell.

            red;intros;split;intros;subst;
            eapply proj_inj in H0; try exact Hprojp;try easy; eapply eq_sym in H0; inversion H0;subst;clear H0.
            set (xs_suf:= cocons (g0, Some (lcomm q p ell)) xsuf).
            assert(Hvalid_suf: global_valid_pathC xs_suf).
            {
                eapply valid_suffix_valid_global;try exact Hvalid. unfold xs_suf. easy.
            }
            pinversion Hvalid_suf;try apply valid_path_mon;try easy;subst. red in H4.
            clear H2. rename H4 into Hstep, x into g1.
            Search gttstepC projectionC.
            eapply typ_after_step_3_helper.
            Search "matching".
            exists ell, sint, ltt_end. split. admit.
            inversion Hsuf. admit. subst. rewrite eventually_P_iff_P_suffix. exists xsuf. 
        }                

            
    }
    { 
        pfold. constructor. red; intros  * Hprojp; split; intros;subst;
        try solve
                    [ 
                    try eapply projection_implies_part_send in Hprojp;
                    try eapply projection_implies_part_recv in Hprojp;easy].
        right. eapply CIH;try solve [subtac_tail_solve | subtac_tail_valid].
    }


    (*
    
        pfold. constructor. admit.
         right. eapply CIH;try solve [subtac_tail_solve | subtac_tail_valid].
        destruct c. constructor. easy.
        destruct p0 as [g l]

        intros; split;intros;subst.   
                    
                    assert (Hispartsq:isgPartsC q g) by (eapply proj_contains_q_implies_part_send in Hprojp;easy).
                    specialize (Hprojable q) as Hprojq. destruct Hprojq as [Tq Hprojq].
                    eapply balanced_to_tree in Hispartsq as Hgraftq; try easy.
                    destruct Hgraftq as [ctx_q [gs_q [?Htypq [?Htypq [?Htypq ?Htypq]]]]];try easy.
                    assert(Htyp_q : typ_p_gtth gs_q ctx_q q g) by (red;crush).
                    eapply multigrafting_lemma with (p:=p) (q:=q) (xs:=lcs) (Tq:=Tq) in 
                    Hwfg as Hmg; 
                    try exact Htyp_q;try exact Hgraftp_p;try easy.
                    assert(Hevqp : eventually (head_proj_is_recv q p) (cocons (g, l) xs)).
                    {
                        destruct Hmg;
                        [|
                        eapply multigrafting_lemma_1 with (p:=p) (q:=q) (Tq:=Tq) in Hwfg as Htr;try exact Hprojp;try exact Hgraftp_p;
                        try exact Htyp_q;try easy;
                        destr_hyps;subst; constructor 1;simpl;exists x;easy].
                         
                        eapply local_types_corr_send_and_projH with (q:=q) (xs:=lcs) (Tq:=Tq) in 
                        Hgraftp_p as Hlgraft;
                        try easy.
                        destruct Hlgraft as [lsq [lxq [?Hlgraft [?Hlgraft ?Hlgraft]]]].

                        assert(Hwfgthq : wfgtth ctx_q) by (eapply typ_gtth_means_wfgtth in Htypq;easy).
                        
                        
                        eapply always_local_step_implies_ev_grafting with (Tp:=Tq) (ls:=lsq) (lx:=lxq);try easy.
                        eapply always_P_iff_P_suffix. intros * Hsuf.
                        destruct ys.
                        pfold;constructor; easy.
                        destruct p0 as [g' l']. 
                        eapply H.
                        set (xss:=cocons (g,l) xs).
                        fold xss. clearbody xss.
                        generalize dependent xss.
                        pcofix CIH2.
                        
                        assert (H_hgt: gtth_height ctx_q < gtth_height ctx_p) by (eapply proper_prefix_height_le;easy).
                        intros.
                        destruct Tq; try solve [eapply pmergeCR_s in Hprojq; easy]. split;intros;subst.
                        
                        eapply H with (g:=g) (l:=l) (gh':=ctx_q) (gs_p:=gs_q) (q:=q0) (Tp:=ltt_send q0 lcs0) ;try easy.
                           
                        red.
                        eapply H.
                        assert (head_proj_eventually_takes_step )
                        eapply H with (gh':= ctx_q) (gs_p:=gs_q) (Tp:=Tq). try easy.
                        eapply proper_prefix_height_le;try easy.
                        red. repeat split;try tauto. 
                        Search ishlParts.
                        eapply projectionH_ishparts;try exact Hlgraft0;try easy.

                        intros.
                        eapply typ_ltth_fills_holes in H1;try exact Hlgraft. destr_hyps.
                        red in Hlgraft1.
                        eapply Forall2_prop_l in Hlgraft1;try exact H1;tac_sanitize.
                        
                        eapply restricted_grafting_send in Hgraftp as Hrg;try exact Hprojp;try easy. 
                        eapply Forall_prop in Hrg;try exact H3;tac_sanitize.
                        pinversion H5;try apply proj_mon;try easy;subst.
                        {
                            subtac_triv_isparts_false. 
                            eapply wfg_list_by_grafting in Hgraftp;try easy. destr_hyps.
                            eapply Forall_prop in H6;try exact H3;tac_sanitize;try easy.
                        }
                        exists ys0;easy.                
                    }
    }
    generalize dependent ctx_p.
    {
        pfold. constructor. easy.   
    }
    {
        pfold. constructor. 
        {
            destruct p0 as [g o].
            pose proof Hvalid as Hvalid'.
            pinversion Hvalid';subst;try apply valid_path_mon.
            {   
                red;split;intros;subst;
                destruct g;
                try solve
                [pinversion H;subst;try apply proj_mon |
                eapply head_gtt_send_not_fair in Hfair;try easy; 
                eapply wfg_global_path_head;try exact Hwfgp].
            }
            {
                destruct l;try easy;
                set (xs := (cocons (x,l') xs0));
                set (l := Some (lcomm n n0 n1));
                fold xs in Hfair, Hvalid', Hvalid, Hwfgp, H1; 
                fold l in Hfair, Hvalid, Hvalid', Hwfgp, H1;
                clear H3 Hvalid' H1;
                clearbody xs l;
                clear l' xs0 n n0 n1 x;
                intros.
                (*now as in assoc_live_helper*)
                red;intros * Hprojp;
                assert (Hwfg : wfgC g) by (eapply wfg_global_path_head;try exact Hwfgp;easy); 
                assert (Hprojable : projectableA g) by
                (eapply projable_global_path_head; try exact Hwfgp;easy).
                destruct (decidable_isgPartsC g p);try easy;rename H into Hispartsp;
                try solve
                [split;intros; subst; 
                try eapply projection_implies_part_send in Hprojp;
                try eapply projection_implies_part_recv in Hprojp;easy];
                eapply balanced_to_tree in Hispartsp as Hgraftp;try easy;
                destruct Hgraftp as [ctx_p [gs_p [?Hgraftp [?Hgraftp [?Hgraftp ?Hgraftp ]]]]];
                eapply typ_gtth_means_wfgtth in Hgraftp as Hwfgth;
                assert (Hgraftp_p : typ_p_gtth gs_p ctx_p p g)
                by (red;crush); 
                generalize dependent gs_p;
                generalize dependent g;
                generalize dependent  xs;
                generalize dependent l;
                generalize dependent p;
                revert Tp;
                revert Hwfgth; 
                induction ctx_p using gtth_ind_by_height.
                {
                    intros; split;intros;subst.   
                    
                    assert (Hispartsq:isgPartsC q g) by (eapply proj_contains_q_implies_part_send in Hprojp;easy).
                    specialize (Hprojable q) as Hprojq. destruct Hprojq as [Tq Hprojq].
                    eapply balanced_to_tree in Hispartsq as Hgraftq; try easy.
                    destruct Hgraftq as [ctx_q [gs_q [?Htypq [?Htypq [?Htypq ?Htypq]]]]];try easy.
                    assert(Htyp_q : typ_p_gtth gs_q ctx_q q g) by (red;crush).
                    eapply multigrafting_lemma with (p:=p) (q:=q) (xs:=lcs) (Tq:=Tq) in 
                    Hwfg as Hmg; 
                    try exact Htyp_q;try exact Hgraftp_p;try easy.
                    assert(Hevqp : eventually (head_proj_is_recv q p) (cocons (g, l) xs)).
                    {
                        destruct Hmg;
                        [|
                        eapply multigrafting_lemma_1 with (p:=p) (q:=q) (Tq:=Tq) in Hwfg as Htr;try exact Hprojp;try exact Hgraftp_p;
                        try exact Htyp_q;try easy;
                        destr_hyps;subst; constructor 1;simpl;exists x;easy].
                         
                        eapply local_types_corr_send_and_projH with (q:=q) (xs:=lcs) (Tq:=Tq) in 
                        Hgraftp_p as Hlgraft;
                        try easy.
                        destruct Hlgraft as [lsq [lxq [?Hlgraft [?Hlgraft ?Hlgraft]]]].

                        assert(Hwfgthq : wfgtth ctx_q) by (eapply typ_gtth_means_wfgtth in Htypq;easy).
                        
                        
                        eapply always_local_step_implies_ev_grafting with (Tp:=Tq) (ls:=lsq) (lx:=lxq);try easy.
                        eapply always_P_iff_P_suffix. intros * Hsuf.
                        destruct ys.
                        pfold;constructor; easy.
                        destruct p0 as [g' l']. 
                        eapply H.
                        set (xss:=cocons (g,l) xs).
                        fold xss. clearbody xss.
                        generalize dependent xss.
                        pcofix CIH2.
                        
                        assert (H_hgt: gtth_height ctx_q < gtth_height ctx_p) by (eapply proper_prefix_height_le;easy).
                        intros.
                        destruct Tq; try solve [eapply pmergeCR_s in Hprojq; easy]. split;intros;subst.
                        
                        eapply H with (g:=g) (l:=l) (gh':=ctx_q) (gs_p:=gs_q) (q:=q0) (Tp:=ltt_send q0 lcs0) ;try easy.
                           
                        red.
                        eapply H.
                        assert (head_proj_eventually_takes_step )
                        eapply H with (gh':= ctx_q) (gs_p:=gs_q) (Tp:=Tq). try easy.
                        eapply proper_prefix_height_le;try easy.
                        red. repeat split;try tauto. 
                        Search ishlParts.
                        eapply projectionH_ishparts;try exact Hlgraft0;try easy.

                        intros.
                        eapply typ_ltth_fills_holes in H1;try exact Hlgraft. destr_hyps.
                        red in Hlgraft1.
                        eapply Forall2_prop_l in Hlgraft1;try exact H1;tac_sanitize.
                        
                        eapply restricted_grafting_send in Hgraftp as Hrg;try exact Hprojp;try easy. 
                        eapply Forall_prop in Hrg;try exact H3;tac_sanitize.
                        pinversion H5;try apply proj_mon;try easy;subst.
                        {
                            subtac_triv_isparts_false. 
                            eapply wfg_list_by_grafting in Hgraftp;try easy. destr_hyps.
                            eapply Forall_prop in H6;try exact H3;tac_sanitize;try easy.
                        }
                        exists ys0;easy.                
                    }
                }
                }
                admit.   
            }
        }
        {
            right. eapply CIH;try solve [subtac_tail_solve | subtac_tail_valid].
        }   
    }
Qed.  
      *)  
Lemma assoc_live_helper : forall  p g ls lx q Tp l pt_tl, fair_path_global (cocons (g,l) pt_tl) -> 
global_valid_pathC (cocons (g,l) pt_tl) ->  wfg_global_path (cocons (g,l) pt_tl) ->
isgPartsC p g -> isgPartsC q g -> projectionC g p Tp ->
(typ_p_send_ltth ls lx q Tp -> eventually (head_proj_is_send p q) (cocons (g,l) pt_tl)) /\ 
(typ_p_recv_ltth ls lx q Tp -> eventually (head_proj_is_recv p q) (cocons (g,l) pt_tl)).
Proof.
    intros * Hfair Hvalid Hwfgp Hispartsp Hispartsq Hprojp.
    
    assert (Hwfg : wfgC g). pinversion Hwfgp;subst;red in H1;tauto.
    assert (Hprojable : projectableA g). pinversion Hwfgp;subst;red in H1;tauto.
    eapply balanced_to_tree in Hispartsp as Hgraftp;try easy.
    destruct Hgraftp as [ctx_p [gs_p [?Hgraftp [?Hgraftp [?Hgraftp ?Hgraftp ]]]]].
    eapply typ_gtth_means_wfgtth in Hgraftp as Hwfgth.
    assert (Hgraftp_p : typ_p_gtth gs_p ctx_p p g)
    by (red;crush). 
    generalize dependent gs_p.
    generalize dependent g.
    generalize dependent  pt_tl.
    generalize dependent l.
    generalize dependent p.
    generalize dependent q.

    revert Hwfgth.
    revert lx ls Tp.
    induction ctx_p using gtth_ind_by_height.
    {
        intros lx. revert ctx_p H.
        destruct lx using ltth_ind_ref.
        {
            intros;
            split; intros Htypp_send;
            red in Htypp_send;
            destruct Htypp_send as [?Htypp_send [?Htypp_send ?Htypp_send]];
            inversion Htypp_send;subst;
            specialize (Htypp_send1 n);
            assert (used_in_ltth n (ltth_hol n)) by constructor;
            specialize (Htypp_send1 H0); destr_hyps; rewrite H1 in H2; inversion H2;subst;
            constructor 1; simpl; exists x; easy.   
        }
        {
            rename H into IH.
            intros;
            split;
            intros Htypp.
            pose proof Htypp as Htypp'.
            
            destruct Htypp as [?Htypp [?Htypp ?Htypp]].
            rename q into r, q0 into q.
            inversion Htypp;subst;rename H4 into Htypp_cont. 
            (*graft r*)
            assert (Hispartsr:isgPartsC r g) by (
                eapply proj_contains_q_implies_part_send in Hprojp;easy).
            eapply balanced_to_tree in Hispartsr as Hgraftr; try easy.
            destruct Hgraftr as [ctx_r [gs_r [?Htypr [?Htypr [?Htypr ?Htypr]]]]];try easy.
            assert(Htyp_r : typ_p_gtth gs_r ctx_r r g) by (red;crush).
            specialize (Hprojable r) as Hprojr;destruct Hprojr as [Tr Hprojr].

            eapply multigrafting_lemma with (p:=p) (q:=r) (xs:=ys) (Tq:=Tr) in Hwfg as Hmg;try exact Htyp_r;
            try exact Hgraftp_p;try easy.

            assert(Hevqp : eventually (head_proj_is_recv r p) (cocons (g, l) pt_tl)).
            {
                destruct Hmg;
                [| 
                eapply multigrafting_lemma_1 with (p:=p) (q:=r) (Tq:=Tr) in Hwfg as Htr;try exact Hprojp;try exact Hgraftp_p;
                try exact Htyp_r;try easy;
                destr_hyps;subst; constructor 1;simpl;exists x;easy]. 
                eapply local_types_corr_send_and_projH with (q:=r) (xs:=ys) (Tq:=Tr) in Hgraftp_p as Hlgraft;
                try easy.
                destruct Hlgraft as [lsr [lxr [?Hlgraft [?Hlgraft ?Hlgraft]]]].
                assert(Hwfgthr : wfgtth ctx_r) by (eapply typ_gtth_means_wfgtth in Htypr;easy).
                
                eapply H with (gh':= ctx_r) (gs_p:=gs_r) (Tp:=Tr) (ls:=lsr) (lx:=lxr);try easy.
                eapply proper_prefix_height_le;try easy.
                red. repeat split;try tauto. 
                Search ishlParts.
                eapply projectionH_ishparts;try exact Hlgraft0;try easy.

                intros.
                eapply typ_ltth_fills_holes in H1;try exact Hlgraft. destr_hyps.
                red in Hlgraft1.
                eapply Forall2_prop_l in Hlgraft1;try exact H1;tac_sanitize.
                
                eapply restricted_grafting_send in Hgraftp as Hrg;try exact Hprojp;try easy. 
                eapply Forall_prop in Hrg;try exact H3;tac_sanitize.
                pinversion H5;try apply proj_mon;try easy;subst.
                {
                    subtac_triv_isparts_false. 
                    eapply wfg_list_by_grafting in Hgraftp;try easy. destr_hyps.
                    eapply Forall_prop in H6;try exact H3;tac_sanitize;try easy.
                }
                exists ys0;easy.                
            }
            assert(Headpr: head_proj_is_send p r (cocons (g, l) pt_tl)) by (red;exists ys;easy).
            eapply no_trans_until_heads_match with (p:=p) (q:=r) in Hwfgp as Hnt;try easy.
            eapply weak_untilC_to_until in Hnt;try easy.
            eapply no_trans_implies_same_proj in Hnt;try easy.
            eapply matching_head_proj_to_comm in Hnt;try easy.
            
            assert (Huse_IH: exists n s' lh' Tp', 
            onth n xs = Some (s',lh') /\ eventually (fun u =>
                match u with cocons (g,l) xs => 
                projectionC g p Tp' /\ typ_p_send_ltth ls lh' 
                q Tp'
                | _ => False 
                end
            ) (cocons (g,l) pt_tl)).
            {
                admit.   
            }
            (*massage the goal so it's cocons (g',l) pt_tl (NOT cocons (g,l))*)
            destruct Huse_IH as [n [s' [lh' [Tp' [Honth Hev2]]]]].
            rewrite eventually_P_iff_P_suffix in Hev2.
            destruct Hev2 as [pt2 [Hsuf2 Hm]].
            enough (eventually (head_proj_is_send p q) pt2).
            {
                rewrite eventually_idemp.
                rewrite eventually_P_iff_P_suffix. exists pt2;try tauto.   
            }
            destruct pt2;try easy.
            destruct p0;try easy.
            eapply Forall_prop in IH2;try exact Honth;tac_sanitize.
            eapply H3 with (gs_p:=gs_p) (Tp:=Tp');try easy.
            
            eapply no_trans_until_heads_match with (p:=p) (q:=r) in Hwfgp as Hnt;try easy.
            eapply weak_untilC_to_until in Hnt;try easy.
            eapply no_trans_implies_same_proj in Hnt;try easy.
            eapply matching_head_proj_to_comm in Hnt;try easy.



Lemma assoc_live_helper : forall  p g ls lx q Tp l pt_tl, fair_path_global (cocons (g,l) pt_tl) -> 
global_valid_pathC (cocons (g,l) pt_tl) ->  wfg_global_path (cocons (g,l) pt_tl) ->
isgPartsC p g -> isgPartsC q g -> projectionC g p Tp ->
(typ_p_send_ltth ls lx q Tp -> eventually (head_proj_is_send p q) (cocons (g,l) pt_tl)) /\ 
(typ_p_recv_ltth ls lx q Tp -> eventually (head_proj_is_recv p q) (cocons (g,l) pt_tl)).
Proof.
    intros * Hfair Hvalid Hwfgp Hispartsp Hispartsq Hprojp.
    
    assert (Hwfg : wfgC g). pinversion Hwfgp;subst;red in H1;tauto.
    assert (Hprojable : projectableA g). pinversion Hwfgp;subst;red in H1;tauto.
    eapply balanced_to_tree in Hispartsp as Hgraftp;try easy.
    destruct Hgraftp as [ctx_p [gs_p [?Hgraftp [?Hgraftp [?Hgraftp ?Hgraftp ]]]]].
    eapply typ_gtth_means_wfgtth in Hgraftp as Hwfgth.
    assert (Hgraftp_p : typ_p_gtth gs_p ctx_p p g)
    by (red;crush). 
    generalize dependent gs_p.
    generalize dependent g.
    generalize dependent  pt_tl.
    generalize dependent l.
    generalize dependent p.
    generalize dependent q.

    revert Hwfgth.
    revert ctx_p ls Tp.
    induction lx using ltth_ind_ref.
    {
        intros;
            split;intros Htypp_send;
            red in Htypp_send;
            destruct Htypp_send as [?Htypp_send [?Htypp_send ?Htypp_send]];
            inversion Htypp_send;subst;
            specialize (Htypp_send1 n);
            assert (used_in_ltth n (ltth_hol n)) by constructor;
            specialize (Htypp_send1 H); destr_hyps; rewrite H0 in H1; inversion H1;subst;
            constructor 1; simpl; exists x; easy.
    }
    {
        intros ctx_p.
        revert q xs H.
        induction ctx_p using gtth_ind_by_height.
        intros.
        rename H0 into IH2.
        intros;split;intros Htypp.   
        pose proof Htypp as Htypp'.
            
        destruct Htypp as [?Htypp [?Htypp ?Htypp]].
        rename q into r, q0 into q.
        inversion Htypp;subst;rename H4 into Htypp_cont. 
            (*graft r*)
        assert (Hispartsr:isgPartsC r g) by (
        eapply proj_contains_q_implies_part_send in Hprojp;easy).
        eapply balanced_to_tree in Hispartsr as Hgraftr; try easy.
        destruct Hgraftr as [ctx_r [gs_r [?Htypr [?Htypr [?Htypr ?Htypr]]]]];try easy.
        assert(Htyp_r : typ_p_gtth gs_r ctx_r r g) by (red;crush).
        specialize (Hprojable r) as Hprojr;destruct Hprojr as [Tr Hprojr].

        eapply multigrafting_lemma with (p:=p) (q:=r) (xs:=ys) (Tq:=Tr) in Hwfg as Hmg;try exact Htyp_r;
        try exact Hgraftp_p;try easy.
        assert(Hevqp : eventually (head_proj_is_recv r p) (cocons (g, l) pt_tl)).
            {
                destruct Hmg;
                [| 
                eapply multigrafting_lemma_1 with (p:=p) (q:=r) (Tq:=Tr) in Hwfg as Htr;try exact Hprojp;try exact Hgraftp_p;
                try exact Htyp_r;try easy;
                destr_hyps;subst; constructor 1;simpl;exists x;easy]. 
                eapply local_types_corr_send_and_projH with (q:=r) (xs:=ys) (Tq:=Tr) in Hgraftp_p as Hlgraft;
                try easy.
                destruct Hlgraft as [lsr [lxr [?Hlgraft [?Hlgraft ?Hlgraft]]]].
                assert(Hwfgthr : wfgtth ctx_r) by (eapply typ_gtth_means_wfgtth in Htypr;easy).
                
                eapply H with (gh':= ctx_r) (gs_p:=gs_r) (ls:=lsr)(Tp:=Tr) (g:=lxr);try easy.
                eapply proper_prefix_height_le;try easy.
                red. repeat split;try tauto. 
                Search ishlParts.
                eapply projectionH_ishparts;try exact Hlgraft0;try easy.

                intros.
                eapply typ_ltth_fills_holes in H1;try exact Hlgraft. destr_hyps.
                red in Hlgraft1.
                eapply Forall2_prop_l in Hlgraft1;try exact H1;tac_sanitize.
                
                eapply restricted_grafting_send in Hgraftp as Hrg;try exact Hprojp;try easy. 
                eapply Forall_prop in Hrg;try exact H3;tac_sanitize.
                pinversion H5;try apply proj_mon;try easy;subst.
                {
                    subtac_triv_isparts_false. 
                    eapply wfg_list_by_grafting in Hgraftp;try easy. destr_hyps.
                    eapply Forall_prop in H6;try exact H3;tac_sanitize;try easy.
                }
                exists ys0;easy.
                
            }
    }
    
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

            (*nested inductive start*)
            generalize dependent g.
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
    
