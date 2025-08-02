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
        pinversion Hpassoc;try apply path_assoc_mon;subst. constructor. simpl. 
        destruct (Nat.eq_dec n n);destruct (Nat.eq_dec n0 n0);tauto.    
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
            constructor 1. simpl. destruct (Nat.eq_dec n0 n0);
            destruct (Nat.eq_dec n1 n1);tauto.     
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
        destruct (Nat.eq_dec p n);destruct (Nat.eq_dec q n0);try tauto;subst;clear H.
        pinversion Hpassoc;try apply path_assoc_mon;subst. constructor. simpl. 
        destruct (Nat.eq_dec n n);destruct (Nat.eq_dec n0 n0);tauto.    
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
        | lsend p q _ _ => if Nat.eq_dec p r then True else if Nat.eq_dec q r then True else False 
        | lrecv p q _ _ => if Nat.eq_dec p r then True else if Nat.eq_dec q r then True else False
    
        | lcomm p q  _ => if Nat.eq_dec p r then True else if Nat.eq_dec q r then True else False
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
                
Lemma no_trans_until_heads_match : forall p q xs, fair_path_global xs ->
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

Lemma no_trans_implies_same_proj : forall xs p q,
fair_path_global xs ->
global_valid_pathC xs -> 
wfg_global_path xs -> 
head_proj_is_send p q xs ->
until (head_trans_not_involving_p p) (head_proj_is_recv q p) xs ->
eventually ( head_proj_is_send p q /1\ head_proj_is_recv q p) xs.
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
        red in H;red in Hprojp. destruct Hprojp as [xsp Hprojp].
        simpl in H.
        destruct (Nat.eq_dec n p);
        destruct (Nat.eq_dec n0 p);subst;try tauto.
        assert(Hwfg : wfgC g)
        by  (eapply wfg_global_path_head;try exact Hwfgp).
        
        assert(Hprojable : projectableA g) 
        by (pinversion Hwfgp;subst; red in H4;tauto).
        eapply typ_after_step_r_redux in H3;try exact Hprojp;try easy.
        red. destr_hyps. exists xsp. subst. easy.
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

Lemma suffix_trans {A:Type}: forall (xs: coseq A) ys zs,is_suffix xs ys -> is_suffix zs xs -> is_suffix zs ys.
Proof.
    intros.
    
    generalize dependent zs.
    induction H.
    intros;easy.

    intros. constructor. eapply IHis_suffix. easy.
Qed.

Lemma eventually_idemp {A:Type}: forall (P : coseq A -> Prop) xs, 
eventually P xs <-> eventually (eventually P) xs.
Proof.
    split;intros.
    constructor. easy.
    induction H;try easy.

    constructor 2. easy.
Qed.


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
        induction lx using ltth_ind_ref.
        {
            intros;
            split;intros Htypp_send;
            red in Htypp_send;
            destruct Htypp_send as [?Htypp_send [?Htypp_send ?Htypp_send]];
            inversion Htypp_send;subst;
            specialize (Htypp_send1 n);
            assert (used_in_ltth n (ltth_hol n)) by constructor;
            specialize (Htypp_send1 H0); destr_hyps; rewrite H1 in H2; inversion H2;subst;
            constructor 1; simpl; exists x; easy.   
        }
        {
            rename H into IH2.
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
            


            (*
Section contexts_mutual_ind.

Variable (P: gtth -> ltth -> Prop).

Hypothesis Hsend : forall gx q xs, 
Forall (fun u => u=None \/ exists s g, u= Some (s,g) /\ P gx g) xs -> P gx (ltth_send q xs).

Hypothesis Hrecv : forall gx q xs, 
Forall (fun u => u=None \/ exists s g, u= Some (s,g) /\ P gx g) xs -> P gx (ltth_recv q xs).
Hypothesis Hsend : forall q xs, Forall (fun u => u=None \/ exists s g, u= Some (s,g) /\ P g) xs -> P (ltth_send q xs).
Hypothesis Hrecv : forall q xs, Forall (fun u => u=None \/ 
exists s g, u= Some (s,g) /\ P g) xs -> P (ltth_recv q xs)
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
    induction ctx_p using gtth_ind_by_height.
    {
        induction lx using ltth_ind_ref.
        {
            intros;
            split;intros Htypp_send;
            red in Htypp_send;
            destruct Htypp_send as [?Htypp_send [?Htypp_send ?Htypp_send]];
            inversion Htypp_send;subst;
            specialize (Htypp_send1 n);
            assert (used_in_ltth n (ltth_hol n)) by constructor;
            specialize (Htypp_send1 H0); destr_hyps; rewrite H1 in H2; inversion H2;subst;
            constructor 1; simpl; exists x; easy.   
        }
        {
            rename H0 into IH2.
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
                rewrite eventually_invol.
                rewrite eventually_P_iff_P_suffix. exists pt2;try tauto.   
            }
            destruct pt2;try easy.
            destruct p0;try easy.
            eapply Forall_prop in IH2;try exact Honth;tac_sanitize.
            eapply H3 with (gs_p:=gs_p) (Tp:=Tp');try easy.
            destr_hyps.
            
            (*prove [always (a -> ev b) xs] with an assertion 
            or lemma with forall xs : fair xs -> valid xs -> ..*)
            Lemma always_event_trans : 
            Search eventually alwaysCG.
            
            Ltac subtac_tail_valid Hglobal := pinversion Hglobal;subst;try apply valid_path_mon;try easy;pfold;constructor.
            
            Lemma eventually_transitions : forall p q xs, global_valid_pathC xs -> 
            wfg_global_path xs -> fair_path_global xs ->
            eventually (headComm_global p q) xs -> 
            eventually (fun u => match u with 
            cocons (g,Some (lcomm p q ell)) (cocons (g', _) _) => 
            gttstepC g g' p q ell
            | _ => False  
            end) xs.
            Proof.
                intros * Hglobal Hwfp Hfair Hev.
                revert Hwfp Hglobal Hfair. induction Hev;intros.

                constructor.
                red in H; pinversion Hglobal; try apply valid_path_mon;subst;try easy.

                constructor 2. eapply IHHev;try subtac_tail_solve;try subtac_tail_valid Hglobal. 
            Qed.
            
            Lemma eventually_if_fair P Q: 
            forall  xs, global_valid_pathC xs -> wfg_global_path xs -> 
            fair_path_global xs ->
            eventually P xs ->
            (forall ys, global_valid_pathC ys -> wfg_global_path ys -> fair_path_global ys ->
            P ys -> eventually Q ys) ->
            eventually Q xs.
            Proof.
                intros * Hvalid Hwfgp Hfair Hev.
                revert Hvalid Hwfgp Hfair.
                induction Hev;
                intros. eapply H0;try easy.

                constructor 2. eapply IHHev;try easy;try subtac_tail_solve;try subtac_tail_valid Hvalid.
            Qed.

            eapply eventually_transitions in Hnt;try easy.
            assert(eventually (fun u => match u with 
            cocons (g,Some (lcomm p r ell)) (cocons (g', _) _) => gttstepC g g' p q ell
            | _ => False  
            end) (cocons (g, l) pt_tl)).
            {
                eapply eventually_if_fair;try exact Hnt;try easy.
                clear;
                intros. red in H2;try easy.
                pcofix CIH.
                pfold.
                constructor.
                intros.

                red in H0.
            }

            
            Check eventually_if.
            admit.   
        }
        {
            intros;
            split;intros Htypp_send;
            red in Htypp_send;
            destruct Htypp_send as [?Htypp_send [?Htypp_send ?Htypp_send]];
            inversion Htypp_send;subst;
            specialize (Htypp_send1 n);
            assert (used_in_ltth n (ltth_hol n)) by constructor;
            specialize (Htypp_send1 H0); destr_hyps; rewrite H1 in H2; inversion H2;subst;
            constructor 1; simpl; exists x; easy.   
        }
        intros. rename H into IH.
        specialize (Hprojable q) as Ht.
        destruct Ht as [Tq Hprojq].
        eapply balanced_to_tree in Hispartsq as Hgraftq;try easy.
        destruct Hgraftq as [ctx_q [gs_q [?Hgraftq [?Hgraftq [?Hgraftq ?Hgraftq]]]]].
        eapply multigrafting_lemma with (q:=q) (p:=p) (gs_p:=gs_p) (ctx_p:=ctx_p)
        (gs_q:=gs_q) (ctx_q:=ctx_q) (Tq:=Tq) in Hprojp as Hmg;try easy.
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
    
