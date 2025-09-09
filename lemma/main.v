From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
From SST Require Import src.header src.sim src.expr src.process src.local 
src.global src.balanced src.typecheck src.part src.gttreeh src.path_props src.step src.merge src.projection src.session src.lcontext.  
From SST Require Import lemma.inversion lemma.inversion_expr lemma.completeness lemma.substitution_helper lemma.substitution lemma.decidable_helper lemma.decidable lemma.expr lemma.part lemma.step 
lemma.projection_helper lemma.projection lemma.main_helper lemma.soundness lemma.liveness_helpers. 


Search substitutionP guardP.

Lemma active_parts_subset: forall gamma pt p q ell gamma', 
    tctxR gamma (lcomm p q ell) gamma' -> in_not_end pt gamma' -> in_not_end pt gamma.
    Proof.
      intros * Hred Hin.
      red in Hin. destr_hyps.
      destruct (Nat.eq_dec pt p);subst.
      eapply lem_6_11c_tctx_comm_invert in Hred;destr_hyps;red;
      exists (ltt_send q x2);split;try easy.
      destruct (Nat.eq_dec pt q);subst.
      eapply lem_6_11c_tctx_comm_invert in Hred;destr_hyps;red;
      exists (ltt_recv p x4);split;try easy.
      Search tctxR M.find.
      eapply lem_6_10 with (r:=pt) in Hred;try easy. red;exists x;split;congruence;try easy.
      simpl. red;intros. destruct H1;subst;tauto.
    Qed.

(*


Fixpoint get_proc (p:part) (M:session) : option process :=
  match M with 
  | s_ind q T => if Nat.eqb p q then Some T else None 
  | s_par M1 M2 => match get_proc p M1 with Some x => Some x |
      None => get_proc p M2 end
  end. 

Lemma get_proc_par1 : forall p M1 M2 x, get_proc p M1 = Some x ->
get_proc p (M1 ||| M2) = Some x.
Proof.
  induction M1.
  intros. simpl in H. destruct (Nat.eqb p n) eqn:Hpn. rewrite Nat.eqb_eq in Hpn. 
  subst.
  inversion H;subst. simpl. rewrite Nat.eqb_refl. easy. easy. 

  intros.

Lemma get_proc_in : forall p M, get_proc p M <> None <-> InT p M.
Proof.
    induction M;
    intros. 
    {
      split;intros.
      eapply opt_lem1 in H;destr_hyps; 
      destruct(Nat.eqb p n) eqn:Hpn;subst;simpl in H; 
      rewrite -> Hpn in H;inversion H;subst. 
      rewrite Nat.eqb_eq in Hpn;subst;constructor;easy.

      red in H. simpl in H. destruct H;subst;try easy. simpl. rewrite Nat.eqb_refl. easy.
  }
  {
    split;intros.
    {
      red;simpl. eapply in_or_app.
    } 
  }
*)
  

Theorem sub_red : forall M M' gamma, typ_sess M gamma -> betaP M M' -> exists gamma', typ_sess M' gamma' /\ tctxRtc gamma gamma'.
Proof.
  intros * Hsess Hbeta.
  generalize dependent gamma.
  Print betaP.
  induction Hbeta;intros.
  {
    inversion Hsess;subst. rename H1 into Htwf, H2 into Hins, H3 into Hnodup, H4 into Hfat.
    inversion Hfat;subst. inversion H3;subst. inversion H5;subst. inversion H6;subst.
    clear H3 H4 H5 H6.
    destruct H2 as [Tp [Htp [Htypp Hguardp]]]. destruct H7 as [Tq [Htq [Htypq Hguardq]]].
    Check inv_proc_recv.
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
    eapply assoc.lem_6_16_simul_subproj with (q:=p) (xp:=x3) (xq:=x2) 
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
      Search guardP.
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
Search unfoldP.
Hint Resolve unf_cont_r unf_cont_l betaPr_unfold_h betaPr_unfold:procs.
Print HintDb procs.

  
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
				eapply assoc.lem_6_16_simul_subproj in Hsubp as Hsimul;try exact Hsubq;try easy.
				move H7 at bottom. eapply subtype_send_inv in H7.
				assert(Honthl: onth ell (extendLis ell (Some (se, Tpc)))=Some (se,Tpc)) by (rewrite extendExtract;easy).
				eapply Forall2R_prop in H7;try exact Honthl;tac_sanitize.
				eapply Forall2R_prop in Hsimul;try exact H13;tac_sanitize.
				eapply subtype_recv_inv in H9. 
				eapply Forall2R_prop in H9;try exact H16;tac_sanitize.
				eapply Forall2_prop_l in H10;try exact H12;tac_sanitize.
				Search unfoldP tauRtc.
				Check tauRtc_unfold.
				Hint Resolve  tauRtc_unfold :procs.
				assert(Hunf'' : unfoldP (((p <-- P) ||| (q <-- Q)) ||| M') (((p <-- p_send q ell e P_c) ||| (q <-- Q)) ||| M'))
				by 
				eauto with procs.

				assert(Hunf' : unfoldP M (((q <-- p_recv p chcs)) ||| (p <-- p_send q ell e P_c) ||| M')) by  (eauto 7 with procs).
				eapply expr_eval_ss in H;destr_hyps.
				eapply r_comm with (p:=q) (q:=p) (e:=e) (Q:=P_c) (M:=M') (v:=x)  in H9 as Hbeta;try easy.
				exists (((q <-- subst_expr_proc x6 (e_val x) 0 0) ||| (p <-- P_c)) ||| M').
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
