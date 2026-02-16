From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
From live_mpst.STBase Require Import src.header src.sim src.expr src.process src.local 
src.global src.balanced src.typecheck src.part src.gttreeh  src.step src.merge 
src.projection.  
From live_mpst.STLive Require Import src.path_props src.session 
src.lcontext lemma.completeness
lemma.multigrafting lemma.subj_red_helpers lemma.soundness lemma.liveness_helpers.
From live_mpst.STBase Require Import lemma.inversion lemma.inversion_expr  
lemma.substitution_helper lemma.substitution 
lemma.decidable_helper lemma.decidable lemma.expr lemma.part lemma.step 
lemma.projection_helper lemma.projection. 
(*Search substitutionP guardP.*)

Lemma active_parts_subset: forall gamma pt p q ell gamma', 
    tctxR gamma (lcomm p q ell) gamma' -> in_not_end pt gamma' -> in_not_end pt gamma.
    Proof.
      intros * Hred Hin.
      red in Hin. destr_hyps.
      destruct (Nat.eq_dec pt p);subst.
      eapply tctx_comm_invert in Hred;destr_hyps;red;
      exists (ltt_send q x2);split;try easy.
      destruct (Nat.eq_dec pt q);subst.
      eapply tctx_comm_invert in Hred;destr_hyps;red;
      exists (ltt_recv p x4);split;try easy.
      (*Search tctxR M.find.*)
      eapply red_relevance with (r:=pt) in Hred;try easy. red;exists x;split;congruence;try easy.
      simpl. red;intros. destruct H1;subst;tauto.
    Qed.

  

Theorem sub_red : forall M M' gamma, typ_sess M gamma -> betaP M M' -> exists gamma', typ_sess M' gamma' /\ tctxRtc gamma gamma'.
Proof.
  intros * Hsess Hbeta.
  destruct Hbeta as [l Hbeta].
  generalize dependent gamma.
  (*Print betaP.*)
  induction Hbeta;intros.
  {
    inversion Hsess;subst. rename H1 into Htwf, H2 into Hins, H3 into Hnodup, H4 into Hfat.
    inversion Hfat;subst. inversion H3;subst. inversion H5;subst. inversion H6;subst.
    clear H3 H4 H5 H6.
    destruct H2 as [Tp [Htp [Htypp Hguardp]]]. destruct H7 as [Tq [Htq [Htypq Hguardq]]].
    (*Check inv_proc_recv.*)
    eapply inv_proc_recv in Htypp as Hrec_inv;try reflexivity.
    eapply inv_proc_send in Htypq as Hsend_inv;try reflexivity.
    destr_hyps.
    rename x2 into g.
    eapply assoc.subtype_recv_inv1 in H6 as Hn;destr_hyps;subst.
    eapply assoc.subtype_send_inv1 in H5 as Hn;destr_hyps;subst.
    rename H9 into Hassoc, H3 into Hwfg.
    assert(Hispartsp : isgPartsC p g).
    {
      destruct (decidable_isgPartsC g p);try easy.
      specialize (Hassoc p). destruct Hassoc.
      specialize (H10 H3 _ Htp);easy. 
    }
    assert(Hispartsq : isgPartsC q g).
    {
      destruct (decidable_isgPartsC g q);try easy.
      specialize (Hassoc q). destruct Hassoc.
      specialize (H10 H3 _ Htq);easy. 
    }
    eapply subtype_recv_inv in H6 as Hsinvrec.
    eapply subtype_send_inv in H5 as Hsinvsend.

    assert (Honthl : onth l (extendLis l (Some (x, x0))) = Some (x,x0)) by
    eapply extendExtract.
    eapply Forall2R_prop in Hsinvsend;try exact Honthl;tac_sanitize.
    assert(Hpq: p <>q).
    {
      red;intros;subst;congruence. 
    }
    assert (Hsubp: assoc.issubProj (ltt_send p x3) g q).
    {
      tac_use_assoc Hassoc q Hispartsq;destr_hyps. 
      rewrite Htq in H3;inversion H3;subst;easy.
    }
    assert (Hsubq: assoc.issubProj (ltt_recv q x2) g p).
    {
      tac_use_assoc Hassoc p Hispartsp;destr_hyps. 
      rewrite Htp in H3;inversion H3;subst;easy.
    }
    eapply assoc.simul_subproj with (q:=p) (xp:=x3) (xq:=x2) 
    in Hispartsq as Hsim;try easy;try solve [tac_wfl_to_slist

    | 
    specialize (Htwf _ _ Htq); pinversion Htwf; subst;try apply wfltt.wfltt_mon;try easy
    |
    
    specialize (Htwf _ _ Htp); pinversion Htwf; subst;try apply wfltt.wfltt_mon
    ;try easy
    ].
    eapply Forall2R_prop in Hsim;try exact H10;tac_sanitize.
    eapply simple_red_comm in Htp as Hstep;try exact Htq;try easy;
    try exact H10;try exact H13;try easy.
    set (gamma' := (M.add q x4 (M.add p x10 (M.remove q (M.remove p gamma))))).
    exists gamma'.
    split;try solve [constructor;red;exists q, p, l;try easy].
    constructor;try easy.
    assert(Hprojable: projectableA g) by (eapply assoc_implies_projectable in Hassoc;try easy).
    eapply assoc_completeness with (g:=g) in Hstep as Hgstep;try easy. 
    destr_hyps. exists x;split;try easy. eapply wfgC_after_step in H9;try easy.
    
    eapply wfltt.tctx_wf_after_red_comm;try exact Htwf;try exact Hstep.
    
    intros.
    eapply active_parts_subset in H3;try exact Hstep.
    specialize (Hins _ H3) as Hins'.
    red in Hins';simpl in Hins'.
    red;simpl. easy.
    repeat constructor.
    rename x10 into Tp', x4 into Tq'.
    {
      exists Tp'.
      split;unfold gamma';try autorewrite with mmaps;try easy.
      split. 
      eapply Forall2_prop_r in H7;try exact H;tac_sanitize.
      eapply Forall2R_prop in Hsinvrec;try exact H13;tac_sanitize.
      rewrite H9 in H16;inversion H16;subst;clear H16.
      eapply _subst_expr_var with (S:=x11);try easy.
      eapply tc_sub;try exact H18;try easy.

      eapply wfC_recv with (q:=q); try exact H13.
      eapply typable_implies_wfC;try exact Htypp.
      
      + eapply sc_sub;try exact H17. eapply sc_sub;try exact H14;
      eapply sc_sub with (s:=x5);try easy. eapply expr_typ_step;try exact H1;try easy.
      eapply guardP_subst_expr;try easy.
      
      + eapply guardP_cont_recv_n; try exact H;try easy.
    }
    {
      unfold gamma';autorewrite with mmaps.
      exists x4. repeat split;try easy. eapply tc_sub;try exact H4;try easy.
      eapply wfC_send with (p:=p); try exact H10.
      eapply typable_implies_wfC;try exact Htypq.
      (*Search guardP.*)
      intros.  specialize (Hguardq (S n)) as Hq'. destr_hyps. inversion H3;subst.
      exists x. easy.
    }
    do 2  (inversion Hfat;subst). clear H16 H17.
    assert (Hnotint : (InT p M -> False) /\ (InT q M -> False)).
    {
      simpl in Hnodup. 
      eapply NoDup_cons_iff in Hnodup as Hnodup'. destr_hyps.
      eapply NoDup_cons_iff in H9;destr_hyps.
      eapply not_in_cons in H3;destr_hyps.
      split;intros;unfold InT in H19; easy.
    }
    eapply typ_after_step_not_in_label with (gamma:=gamma);try exact Hstep;try easy.
  }

  {
    eapply typ_after_unfold in Hsess as Hunfold1;try exact H.
    eapply IHHbeta in Hunfold1 as Hu2. destr_hyps. eapply typ_after_unfold in H1;try exact H0.
    exists x;tauto.
  }
Qed.


Theorem sub_red_strong : forall M M' gamma, typ_sess M gamma -> betaP M M' -> exists gamma', typ_sess M' gamma' /\ tctxRcomm gamma gamma'.
Proof.
  intros * Hsess Hbeta.
  destruct Hbeta as [l Hbeta].
  generalize dependent gamma.
  (*Print betaP.*)
  induction Hbeta;intros.
  {
    inversion Hsess;subst. rename H1 into Htwf, H2 into Hins, H3 into Hnodup, H4 into Hfat.
    inversion Hfat;subst. inversion H3;subst. inversion H5;subst. inversion H6;subst.
    clear H3 H4 H5 H6.
    destruct H2 as [Tp [Htp [Htypp Hguardp]]]. destruct H7 as [Tq [Htq [Htypq Hguardq]]].
    (*Check inv_proc_recv.*)
    eapply inv_proc_recv in Htypp as Hrec_inv;try reflexivity.
    eapply inv_proc_send in Htypq as Hsend_inv;try reflexivity.
    destr_hyps.
    rename x2 into g.
    eapply assoc.subtype_recv_inv1 in H6 as Hn;destr_hyps;subst.
    eapply assoc.subtype_send_inv1 in H5 as Hn;destr_hyps;subst.
    rename H9 into Hassoc, H3 into Hwfg.
    assert(Hispartsp : isgPartsC p g).
    {
      destruct (decidable_isgPartsC g p);try easy.
      specialize (Hassoc p). destruct Hassoc.
      specialize (H10 H3 _ Htp);easy. 
    }
    assert(Hispartsq : isgPartsC q g).
    {
      destruct (decidable_isgPartsC g q);try easy.
      specialize (Hassoc q). destruct Hassoc.
      specialize (H10 H3 _ Htq);easy. 
    }
    eapply subtype_recv_inv in H6 as Hsinvrec.
    eapply subtype_send_inv in H5 as Hsinvsend.

    assert (Honthl : onth l (extendLis l (Some (x, x0))) = Some (x,x0)) by
    eapply extendExtract.
    eapply Forall2R_prop in Hsinvsend;try exact Honthl;tac_sanitize.
    assert(Hpq: p <>q).
    {
      red;intros;subst;congruence. 
    }
    assert (Hsubp: assoc.issubProj (ltt_send p x3) g q).
    {
      tac_use_assoc Hassoc q Hispartsq;destr_hyps. 
      rewrite Htq in H3;inversion H3;subst;easy.
    }
    assert (Hsubq: assoc.issubProj (ltt_recv q x2) g p).
    {
      tac_use_assoc Hassoc p Hispartsp;destr_hyps. 
      rewrite Htp in H3;inversion H3;subst;easy.
    }
    eapply assoc.simul_subproj with (q:=p) (xp:=x3) (xq:=x2) 
    in Hispartsq as Hsim;try easy;try solve [tac_wfl_to_slist

    | 
    specialize (Htwf _ _ Htq); pinversion Htwf; subst;try apply wfltt.wfltt_mon;try easy
    |
    
    specialize (Htwf _ _ Htp); pinversion Htwf; subst;try apply wfltt.wfltt_mon
    ;try easy
    ].
    eapply Forall2R_prop in Hsim;try exact H10;tac_sanitize.
    eapply simple_red_comm in Htp as Hstep;try exact Htq;try easy;
    try exact H10;try exact H13;try easy.
    set (gamma' := (M.add q x4 (M.add p x10 (M.remove q (M.remove p gamma))))).
    exists gamma'.
    split;try solve [constructor;red;exists q, p, l;try easy].
    constructor;try easy.
    assert(Hprojable: projectableA g) by (eapply assoc_implies_projectable in Hassoc;try easy).
    eapply assoc_completeness with (g:=g) in Hstep as Hgstep;try easy. 
    destr_hyps. exists x;split;try easy. eapply wfgC_after_step in H9;try easy.
    
    eapply wfltt.tctx_wf_after_red_comm;try exact Htwf;try exact Hstep.
    
    intros.
    eapply active_parts_subset in H3;try exact Hstep.
    specialize (Hins _ H3) as Hins'.
    red in Hins';simpl in Hins'.
    red;simpl. easy.
    repeat constructor.
    rename x10 into Tp', x4 into Tq'.
    {
      exists Tp'.
      split;unfold gamma';try autorewrite with mmaps;try easy.
      split. 
      eapply Forall2_prop_r in H7;try exact H;tac_sanitize.
      eapply Forall2R_prop in Hsinvrec;try exact H13;tac_sanitize.
      rewrite H9 in H16;inversion H16;subst;clear H16.
      eapply _subst_expr_var with (S:=x11);try easy.
      eapply tc_sub;try exact H18;try easy.

      eapply wfC_recv with (q:=q); try exact H13.
      eapply typable_implies_wfC;try exact Htypp.
      
      + eapply sc_sub;try exact H17. eapply sc_sub;try exact H14;
      eapply sc_sub with (s:=x5);try easy. eapply expr_typ_step;try exact H1;try easy.
      eapply guardP_subst_expr;try easy.
      
      + eapply guardP_cont_recv_n; try exact H;try easy.
    }
    {
      unfold gamma';autorewrite with mmaps.
      exists x4. repeat split;try easy. eapply tc_sub;try exact H4;try easy.
      eapply wfC_send with (p:=p); try exact H10.
      eapply typable_implies_wfC;try exact Htypq.
      (*Search guardP.*)
      intros.  specialize (Hguardq (S n)) as Hq'. destr_hyps. inversion H3;subst.
      exists x. easy.
    }
    do 2  (inversion Hfat;subst). clear H16 H17.
    assert (Hnotint : (InT p M -> False) /\ (InT q M -> False)).
    {
      simpl in Hnodup. 
      eapply NoDup_cons_iff in Hnodup as Hnodup'. destr_hyps.
      eapply NoDup_cons_iff in H9;destr_hyps.
      eapply not_in_cons in H3;destr_hyps.
      split;intros;unfold InT in H19; easy.
    }
    eapply typ_after_step_not_in_label with (gamma:=gamma);try exact Hstep;try easy.
	red. exists q, p, l. easy.
  }

  {
    eapply typ_after_unfold in Hsess as Hunfold1;try exact H.
    eapply IHHbeta in Hunfold1 as Hu2. destr_hyps. eapply typ_after_unfold in H1;try exact H0.
    exists x;tauto.
  }
Qed.

Theorem sub_red_strong_labelled : forall M M' lb gamma, typ_sess M gamma -> betaP_lbl M lb M' -> exists gamma', typ_sess M' gamma' /\ tctxR gamma lb gamma'.
Proof.
  intros * Hsess Hbeta.
  generalize dependent gamma.
  (*Print betaP.*)
  induction Hbeta;intros.
  {
    inversion Hsess;subst. rename H1 into Htwf, H2 into Hins, H3 into Hnodup, H4 into Hfat.
    inversion Hfat;subst. inversion H3;subst. inversion H5;subst. inversion H6;subst.
    clear H3 H4 H5 H6.
    destruct H2 as [Tp [Htp [Htypp Hguardp]]]. destruct H7 as [Tq [Htq [Htypq Hguardq]]].
    (*Check inv_proc_recv.*)
    eapply inv_proc_recv in Htypp as Hrec_inv;try reflexivity.
    eapply inv_proc_send in Htypq as Hsend_inv;try reflexivity.
    destr_hyps.
    rename x2 into g.
    eapply assoc.subtype_recv_inv1 in H6 as Hn;destr_hyps;subst.
    eapply assoc.subtype_send_inv1 in H5 as Hn;destr_hyps;subst.
    rename H9 into Hassoc, H3 into Hwfg.
    assert(Hispartsp : isgPartsC p g).
    {
      destruct (decidable_isgPartsC g p);try easy.
      specialize (Hassoc p). destruct Hassoc.
      specialize (H10 H3 _ Htp);easy. 
    }
    assert(Hispartsq : isgPartsC q g).
    {
      destruct (decidable_isgPartsC g q);try easy.
      specialize (Hassoc q). destruct Hassoc.
      specialize (H10 H3 _ Htq);easy. 
    }
    eapply subtype_recv_inv in H6 as Hsinvrec.
    eapply subtype_send_inv in H5 as Hsinvsend.

    assert (Honthl : onth l (extendLis l (Some (x, x0))) = Some (x,x0)) by
    eapply extendExtract.
    eapply Forall2R_prop in Hsinvsend;try exact Honthl;tac_sanitize.
    assert(Hpq: p <>q).
    {
      red;intros;subst;congruence. 
    }
    assert (Hsubp: assoc.issubProj (ltt_send p x3) g q).
    {
      tac_use_assoc Hassoc q Hispartsq;destr_hyps. 
      rewrite Htq in H3;inversion H3;subst;easy.
    }
    assert (Hsubq: assoc.issubProj (ltt_recv q x2) g p).
    {
      tac_use_assoc Hassoc p Hispartsp;destr_hyps. 
      rewrite Htp in H3;inversion H3;subst;easy.
    }
    eapply assoc.simul_subproj with (q:=p) (xp:=x3) (xq:=x2) 
    in Hispartsq as Hsim;try easy;try solve [tac_wfl_to_slist

    | 
    specialize (Htwf _ _ Htq); pinversion Htwf; subst;try apply wfltt.wfltt_mon;try easy
    |
    
    specialize (Htwf _ _ Htp); pinversion Htwf; subst;try apply wfltt.wfltt_mon
    ;try easy
    ].
    eapply Forall2R_prop in Hsim;try exact H10;tac_sanitize.
    eapply simple_red_comm in Htp as Hstep;try exact Htq;try easy;
    try exact H10;try exact H13;try easy.
    set (gamma' := (M.add q x4 (M.add p x10 (M.remove q (M.remove p gamma))))).
    exists gamma'.
    split;try solve [constructor;red;exists q, p, l;try easy].
    constructor;try easy.
    assert(Hprojable: projectableA g) by (eapply assoc_implies_projectable in Hassoc;try easy).
    eapply assoc_completeness with (g:=g) in Hstep as Hgstep;try easy. 
    destr_hyps. exists x;split;try easy. eapply wfgC_after_step in H9;try easy.
    
    eapply wfltt.tctx_wf_after_red_comm;try exact Htwf;try exact Hstep.
    
    intros.
    eapply active_parts_subset in H3;try exact Hstep.
    specialize (Hins _ H3) as Hins'.
    red in Hins';simpl in Hins'.
    red;simpl. easy.
    repeat constructor.
    rename x10 into Tp', x4 into Tq'.
    {
      exists Tp'.
      split;unfold gamma';try autorewrite with mmaps;try easy.
      split. 
      eapply Forall2_prop_r in H7;try exact H;tac_sanitize.
      eapply Forall2R_prop in Hsinvrec;try exact H13;tac_sanitize.
      rewrite H9 in H16;inversion H16;subst;clear H16.
      eapply _subst_expr_var with (S:=x11);try easy.
      eapply tc_sub;try exact H18;try easy.

      eapply wfC_recv with (q:=q); try exact H13.
      eapply typable_implies_wfC;try exact Htypp.
      
      + eapply sc_sub;try exact H17. eapply sc_sub;try exact H14;
      eapply sc_sub with (s:=x5);try easy. eapply expr_typ_step;try exact H1;try easy.
      eapply guardP_subst_expr;try easy.
      
      + eapply guardP_cont_recv_n; try exact H;try easy.
    }
    {
      unfold gamma';autorewrite with mmaps.
      exists x4. repeat split;try easy. eapply tc_sub;try exact H4;try easy.
      eapply wfC_send with (p:=p); try exact H10.
      eapply typable_implies_wfC;try exact Htypq.
      (*Search guardP.*)
      intros.  specialize (Hguardq (S n)) as Hq'. destr_hyps. inversion H3;subst.
      exists x. easy.
    }
    do 2  (inversion Hfat;subst). clear H16 H17.
    assert (Hnotint : (InT p M -> False) /\ (InT q M -> False)).
    {
      simpl in Hnodup. 
      eapply NoDup_cons_iff in Hnodup as Hnodup'. destr_hyps.
      eapply NoDup_cons_iff in H9;destr_hyps.
      eapply not_in_cons in H3;destr_hyps.
      split;intros;unfold InT in H19; easy.
    }
    eapply typ_after_step_not_in_label with (gamma:=gamma);try exact Hstep;try easy.
	 easy.
  }

  {
    eapply typ_after_unfold in Hsess as Hunfold1;try exact H.
    eapply IHHbeta in Hunfold1 as Hu2. destr_hyps. eapply typ_after_unfold in H1;try exact H0.
    exists x;tauto.
  }
Qed.

Lemma gtt_end_not_part : forall p, ~ isgPartsC p gtt_end.
Proof.
  red;intros.
  eapply part_break in H;destr_hyps. destruct H2;subst. inversion H0. destr_hyps;subst.
  
  pinversion H;try apply gttT_mon.
  red. exists g_end. split. pfold;constructor. split;try constructor.
  intros. exists 0.  eapply gg_end.

   red;intros.  inversion H0;subst.
  destruct H1; inversion H1.
Qed.

Lemma assoc_implies_end_or_atleast_send : forall gamma g, wfgC g -> wfltt.tctx_wf gamma ->
  assoc.assoc gamma g ->
  is_end_tctx gamma \/ exists p q xsp xsq, M.find p gamma = Some (ltt_send q xsp) /\
  M.find q gamma = Some (ltt_recv p xsq).
Proof.
  intros * Hwf Htwf Hassoc.
  destruct g.
  {
    left. red;intros. assert (~ isgPartsC pt gtt_end) by (eapply gtt_end_not_part).
    tac_use_assoc Hassoc pt H0. eapply Hassoc_u. easy.
  }
  {
    rename n into p, n0 into q.
    right. exists p, q.
    assert(Hispartsp : isgPartsC p (gtt_send p q l)) by (eapply decidable_helper.triv_pt_p;easy).
    assert(Hispartsq : isgPartsC q (gtt_send p q l)) by (eapply decidable_helper.triv_pt_q;easy).
    tac_use_assoc Hassoc p Hispartsp.
    tac_use_assoc Hassoc q Hispartsq. destr_hyps. red in H1, H2;destr_hyps.
    pinversion H2;subst;try apply proj_mon;try easy.
    pinversion H1;subst;try apply proj_mon;try easy.
    eapply subtype_recv_inv2 in H3. eapply subtype_send_inv2 in H4. destr_hyps. subst. exists x2,x1. split;easy.
  }
Qed.

Create HintDb procs.
Hint Constructors unfoldP :procs.
(*Search unfoldP.*)
Hint Resolve unf_cont_r unf_cont_l betaPr_unfold_h betaPr_unfold:procs.
(*Print HintDb procs.*)

  
Theorem prog : forall M G, typ_sess M G -> (exists M', unfoldP M M' /\ (ForallT (fun _ P => P = p_inact) M')) \/ exists M', betaP M M'.
Proof.
	intros * Hsess.

	inversion Hsess;subst. 
	rename H into Htwf, H1 into Hnodup, H0 into Hinend, H2 into Hfa.
	destruct Hassocable as [g [Hwfg Hassoc]].
	eapply assoc_implies_end_or_atleast_send in Hassoc as Hdil;try easy.
	destruct Hdil as [Hdil | Hdil].
	{
		eapply canonical_glob_n_strong in Hdil;try exact Hsess.
		destruct Hdil as [M' [Hunf Hfat]]. 
		left; exists M'. split;tauto.
	}
	{
		destruct Hdil as [p [q [xsp [xsq [Hfindp Hfindq]]]]].
		right.
		assert (Hinp: InT p M).
		{
			eapply Hinend. red.  exists (ltt_send q xsp). split;try easy. 
		}
		assert (Hinq: InT q M).
		{
			eapply Hinend. red.  exists (ltt_recv p xsq). split;try easy. 
		} 
		assert(Hpq: p <> q) by (red;intros;subst;congruence).
		eapply canonical_glob_nt in Hsess as Hcanon;try exact Hfindq;try exact Hfindp;try easy.
		{
			destruct Hcanon as [M' [P [Q Hunf]]].
			eapply typ_after_unfold in Hunf as Hsess';try exact Hsess.
			inversion Hsess';subst. rename H1 into Hdup, H2 into Hfat. 
			
			clear Hassocable H.
			inversion Hfat;subst. inversion H2;subst. inversion H4;subst. inversion H5;subst.
			clear H4 H5 H2.
			destr_hyps.
			rewrite Hfindp in H1;inversion H1;subst;clear H1. 
			rewrite Hfindq in H;inversion H;subst;clear H.
			eapply guardP_break_tau in H6 as Hgb;try exact H5. destruct Hgb as [P' [Hrec_unf Htr]].
			eapply typ_after_tauRtc in H5 as Htyp';try exact Hrec_unf.
			destruct Htr as [Htr | Htr];[| destruct Htr as [Htr | Htr]].
			{
				eapply inv_proc_inact in Htyp';try easy. 
			}
			{
				destr_hyps;subst.
				eapply inv_proc_send in Htyp';try reflexivity.
				destr_hyps.
				
				eapply guardP_break_tau in H4 as Htq;try exact H2. destruct Htq as [Q' [Hrec_unfq Htq]].
				eapply typ_after_tauRtc in H2 as Htyq';try exact Hrec_unfq.

				destruct Htq;subst. eapply inv_proc_inact in Htyq';try easy.
				destruct H8; 
				destr_hyps;subst.
				
				eapply inv_proc_send in Htyq';try reflexivity. destr_hyps.
				pinversion H10;try apply sub_mon.
				destr_hyps;subst.
				
				eapply inv_proc_recv in Htyq';try reflexivity. destr_hyps.
				rename x into q', x0 into ell, x1 into e, x2 into P_c, x3 into se, x4 into Tpc.
				rename x5 into p', x6 into chcs, x7 into xq'.
				
				assert (q'=q) by (pinversion H7;subst;try apply sub_mon;easy);subst.
				assert (p'=p) by (pinversion H9;subst;try apply sub_mon;easy);subst.
				
				assert (Hsubq: assoc.issubProj (ltt_recv p xsq) g q) by
					(eapply assoc_inv_find with (g:=g) in Hfindq; easy).
				
				assert (Hsubp: assoc.issubProj (ltt_send q xsp) g p) by 
				(eapply assoc_inv_find with (g:=g) in Hfindp; easy).
				assert (Hax1 : SList xsp) by
					(specialize (Htwf _ _ Hfindp); pinversion Htwf;subst;try apply wfltt.wfltt_mon;easy).
				
				assert (Hax2 : SList xsq) by
					(specialize (Htwf _ _ Hfindq); pinversion Htwf;subst;try apply wfltt.wfltt_mon;easy).
				assert(Hispartsp: isgPartsC p g).
				{
					destruct (decidable.decidable_isgPartsC g p);try easy.
					red in Hsubp;destr_hyps. eapply assoc.subtype_send_inv1 in H14. destr_hyps;subst.
					pinversion H13;subst;try easy;try apply proj_mon.
				}
				eapply assoc.simul_subproj in Hsubp as Hsimul;try exact Hsubq;try easy.
				move H7 at bottom. eapply subtype_send_inv in H7.
				assert(Honthl: onth ell (extendLis ell (Some (se, Tpc)))=Some (se,Tpc)) by (rewrite extendExtract;easy).
				eapply Forall2R_prop in H7;try exact Honthl;tac_sanitize.
				eapply Forall2R_prop in Hsimul;try exact H13;tac_sanitize.
				eapply subtype_recv_inv in H9. 
				eapply Forall2R_prop in H9;try exact H16;tac_sanitize.
				eapply Forall2_prop_l in H10;try exact H12;tac_sanitize.
				(*Search unfoldP tauRtc.*)
				(*Check tauRtc_unfold.*)
				Hint Resolve  tauRtc_unfold :procs.
				assert(Hunf'' : unfoldP (((p <-- P) ||| (q <-- Q)) ||| M') (((p <-- p_send q ell e P_c) ||| (q <-- Q)) ||| M'))
				by 
				eauto with procs.

				assert(Hunf' : unfoldP M (((q <-- p_recv p chcs)) ||| (p <-- p_send q ell e P_c) ||| M')) by  (eauto 7 with procs).
				eapply expr_eval_ss in H;destr_hyps.
				eapply r_comm with (p:=q) (q:=p) (e:=e) (Q:=P_c) (M:=M') (v:=x)  in H9 as Hbeta;try easy.
        
				exists (((q <-- subst_expr_proc x6 (e_val x) 0 0) ||| (p <-- P_c)) ||| M').
        exists (lcomm p q ell).
				eapply r_struct with (M2':= (((q <-- subst_expr_proc x6 (e_val x) 0 0)
				||| (p <-- P_c)) ||| M'));try exact Hunf';try easy. constructor.
			}
				{
					destr_hyps;subst.
					eapply inv_proc_recv in Htyp';try reflexivity;subst;destr_hyps.
					pinversion H1;subst;try apply sub_mon. 
				}
			}
		}
Qed.



Theorem stuck_free : forall M G, typ_sess M G -> stuckM M -> False.
Proof.
  intros. 
  unfold stuckM in H0. destruct H0 as (M',(Ha,Hb)).
  revert Hb H. revert G.
  induction Ha; intros.
  - destruct Hb.
    specialize(prog x G H); intros. destruct H2. apply H0. easy. apply H1. easy.
  - specialize(sub_red x y G H0 H); intros.
    destruct H1 as (G',(Hc,Hd)).
    apply IHHa with (G := G'); try easy.
Qed.

Lemma typ_proc_inv_send : forall P q xsp, typ_proc [] [] P (ltt_send q xsp) -> all_guarded P -> exists  ell e P', tauRtc P (p_send q ell e P'). 
Proof.
	intros.
	eapply guardP_break_tau in H0;try exact H. destr_hyps.
	eapply typ_after_tauRtc in H0 as Ht;try exact H.
	destruct H1;subst. eapply inv_proc_inact in Ht;try easy.
	destruct H1;destr_hyps;subst. eapply inv_proc_send in Ht;try reflexivity;destr_hyps.
	exists x1, x2, x3. 
	pinversion H3;subst;try apply sub_mon. easy.
	eapply inv_proc_recv in Ht;try reflexivity;destr_hyps. pinversion H2;try apply sub_mon.
Qed. 

Lemma typ_proc_inv_recv : forall P q xsp, typ_proc [] [] P (ltt_recv q xsp) -> all_guarded P -> exists  llp, tauRtc P (p_recv q llp). 
Proof.
	intros.
	eapply guardP_break_tau in H0;try exact H. destr_hyps.
	eapply typ_after_tauRtc in H0 as Ht;try exact H.
	destruct H1;subst. eapply inv_proc_inact in Ht;try easy.
	destruct H1;destr_hyps;subst. eapply inv_proc_send in Ht;try reflexivity;destr_hyps. pinversion H3;try apply sub_mon.
	exists x1. eapply inv_proc_recv in Ht;try reflexivity;destr_hyps. pinversion H2;subst;try apply sub_mon. 
	easy.
Qed.

Lemma guard_after_tauRtc: forall P Q, all_guarded P -> tauRtc P Q ->all_guarded Q.
Proof.
  intros;induction H0;try easy.
  eapply guard_after_tau;try exact H;try easy.
  tauto.
Qed.

Lemma all_guarded_recv_cont: forall P k q llp, all_guarded (p_recv q llp) -> onth k llp=Some P -> all_guarded P.
Proof.
  intros.
  red. intros. specialize (H (S n)). destr_hyps.
  inversion H;subst. eapply  Forall_prop in H4;try exact H0;tac_sanitize. exists x;easy.
Qed.

Lemma all_guarded_send_cont: forall q ell  e P', all_guarded (p_send q ell e P') -> all_guarded P'.
Proof.
  intros.
  red. intros. specialize (H (S n)). destr_hyps.
  inversion H;subst.  exists x;easy.
Qed.

Theorem sess_fidelity : forall M gamma p q ell gamma', 
typ_sess M gamma -> tctxR gamma (lcomm p q ell) gamma' ->
    exists gamma'' M' ell', tctxR gamma (lcomm p q ell') gamma'' /\ betaP_lbl M (lcomm p q ell') M' /\ typ_sess M' gamma''.
Proof.
	intros.
	eapply tctx_comm_invert in H0 as Hinvert;destr_hyps.
	
	assert(Hinp: InT p M) by (inversion H;subst;eapply H9; red;exists (ltt_send q x1);split;try easy).

	assert(Hinq: InT q M) by (inversion H;subst;eapply H9; red;exists (ltt_recv p x3);split;try easy).
	assert(Hpq : p<> q) by (red;intros;subst;congruence).
	eapply canonical_glob_nt in H as Hcanon;try exact H1; try exact H2;try easy.
	destruct Hcanon as [M' [P [Q Hunf]]].
	eapply typ_after_unfold in H as Htyp;try exact Hunf.
	inversion Htyp;subst. inversion_clear H11. inversion_clear H12. inversion_clear H11. inversion_clear H14.
	destr_hyps.
	assert(x6=ltt_send q x1) by congruence.
	
	assert(x5=ltt_recv p x3) by congruence.
	subst.
	eapply typ_proc_inv_send in H17 as Htinvp;try easy.
	eapply typ_proc_inv_recv in H15 as Htinvq;try easy.
	destr_hyps.

	eapply assoc_inv_find in H12 as Hsub1;try exact H14;try easy.
	eapply assoc_inv_find in H11 as Hsub2;try exact H14;try easy.
	assert(Hpartp :isgPartsC p x7).
	{
		red in Hsub1;destr_hyps. pinversion H23;try apply sub_mon;subst.
		eapply proj_contains_q_implies_part_send in H22;destr_hyps;try easy.
		eapply assoc_implies_projectable in H19;try easy.	
	}
	assert(Hslist1: SList x1).
	{
		red in H8. specialize (H8 _ _ H12). pinversion H8;try apply wfltt.wfltt_mon;try easy.
	}
	assert(Hslist2 : SList x3).
	{
		red in H8. specialize (H8 _ _ H11). pinversion H8;try apply wfltt.wfltt_mon;try easy.
	}
	eapply assoc.simul_subproj in Hsub1 as Hsim;try exact Hsub2;try easy.
	eapply typ_after_tauRtc in H21 as Ht2;try exact H17. eapply inv_proc_send in Ht2;try reflexivity;destr_hyps.
	eapply subtype_send_inv in H24.
	assert(onth x6 (extendLis x6 (Some (x10,x11)))=(Some (x10,x11))) by (rewrite extendExtract;easy).
	eapply Forall2R_prop in H24;try exact H25;tac_sanitize.
	eapply Forall2R_prop in Hsim;try exact H27;tac_sanitize.
	set (gamma'' :=M.add p x12 (M.add q x18 (M.remove p (M.remove q gamma)))).
	assert (Hstep: tctxR gamma (lcomm p q x6) gamma'').
	{
		eapply simple_red_comm; try exact H27; try exact H30;try easy.	
	}
	eapply typ_after_tauRtc in H20 as Ht3;try exact H15.
	eapply inv_proc_recv in Ht3;try reflexivity;destr_hyps.
	eapply subtype_recv_inv in H26. 
	eapply Forall2R_prop in H26;try exact H30;tac_sanitize.
	eapply Forall2_prop_l in H32;try exact H35;tac_sanitize.
	eapply expr_eval_ss in H22 as Hnt;destr_hyps.
	assert(Hbeta: betaP_lbl (((q <-- p_recv p x5) ||| (p <-- p_send q x6 x8 x9)) ||| M') (lcomm p q x6) (((q <-- subst_expr_proc x17 (e_val x14) 0 0) ||| (p <-- x9)) ||| M')).
	{
      	eapply r_comm with (p:= q) (q:=p) (Q:=x9) (M:=M') in H32 as Hcomm;try exact H26.
		easy.	
	}
	Hint Resolve  tauRtc_unfold unf_cont_l unf_cont unf_cont_r:procs.
    (*Check unf_cont_l.*)
            
    assert(Hunf2: unfoldP (((p <-- P) ||| (q <-- Q)) ||| M') (((p <-- p_send q x6 x8 x9) ||| (q <-- p_recv p x5)) ||| M')). eauto  with procs.
    assert(Hunf3: unfoldP M (((p <-- p_send q x6 x8 x9) ||| (q <-- p_recv p x5)) ||| M')). eauto  with procs.
    
	assert(Hunf_b: unfoldP M (((q <-- p_recv p x5) ||| (p <-- p_send q x6 x8 x9)) ||| M')). eauto  with procs.
	assert(Hbeta' : betaP_lbl M (lcomm p q x6) (((q <-- subst_expr_proc x17 (e_val x14) 0 0) ||| (p <-- x9)) ||| M')). 

    eapply r_struct;try exact Hunf_b;try exact Hbeta;try constructor;try easy.
    set (M_next :=(((q <-- subst_expr_proc x17 (e_val x14) 0 0) ||| (p <-- x9)) ||| M')).
    exists gamma'', M_next, x6.
    split;try easy. split;try easy.
    eapply assoc_completeness in Hstep as Hcomp;try exact H19;try easy.
    econstructor;try easy.
    {
      destr_hyps. exists x19. split;try easy. eapply wfgC_after_step in H39;try easy.
      eapply assoc_implies_projectable;try exact H19;try easy. 
    }
    {
      eapply wfltt.tctx_wf_after_red_comm;try exact Hstep;try easy. 
    }
    {
      intros. eapply active_parts_subset in H34;try exact Hstep.
      (*Search InT.*)
      specialize (H9 _  H34) as Hin_no.

      unfold M_next. unfold InT. simpl. unfold InT in *. simpl in *. tauto. 
    }
    {
      unfold M_next.
      unfold flattenT in H10. unfold flattenT. 
      Create HintDb nodup_hints.
      Hint Resolve app_assoc nodup_swap2 nodup_swap :nodup_hints.
      eauto with nodup_hints.      
    }
    {
		unfold M_next. econstructor. econstructor. 
		{
		econstructor. exists x20.
		split. unfold gamma'';autorewrite with mmaps;easy.
		split.
		(*Search typ_proc subst_expr_proc.*)
		assert(typ_expr [] (e_val x14) x18).
		{
			eapply expr_typ_step in H22;try exact H26;try easy.
			Create HintDb sc_hints.
			Hint Constructors typ_expr :sc_hints.
			eauto with sc_hints.
		}
		eapply _subst_expr_var;try exact H34;try easy.
		eapply tc_sub;try exact H38;try easy.
		eapply typable_implies_wfC in H15 as Hwf1.
		eapply wfC_recv;try exact H30;try exact Hwf1.

		eapply guardP_subst_expr.
		
		assert(all_guarded (p_recv p x5)).
			eapply guard_after_tauRtc;try exact H20;try easy.
			eapply all_guarded_recv_cont;try exact H34;try exact H32.
		} 
		{
			econstructor. exists x12.
			split. unfold gamma'';autorewrite with mmaps;easy.
			split.
			assert(Hwf:wfC x12). 
			{
				eapply wfC_send with (p:=q);try exact H27.
				eapply typable_implies_wfC;try exact H17.
			}

			eapply tc_sub;try exact H23;try easy.
			
			assert(all_guarded (p_send q x6 x8 x9)). 
			eapply guard_after_tauRtc;try exact H18;try easy.
			eapply all_guarded_send_cont;try exact H34;try exact H32.
		}
		{
			(*Search ForallT.*)
			eapply typ_after_step_not_in_label;try exact Hstep;try easy;
			red;intros;unfold InT in H34; move H10 at bottom;
			unfold flattenT in H10; fold flattenT in H10;
			rewrite <- app_assoc in H10.
			change ([q] ++ flattenT M') with (q::flattenT M') in H10.
			eapply NoDup_remove_2 in H10.
			eapply H10.
			eapply in_or_app;tauto.
			
			eapply NoDup_remove in H10;destr_hyps.
			change ([p]++ flattenT M') with (p::flattenT M') in H10.
			inversion H10;subst. easy.
		} 
    }
Qed.
    
