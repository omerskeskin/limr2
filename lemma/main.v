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
    inversion Hsess;subst;inversion H3;subst. inversion H6;subst;destr_hyps.
    eapply inv_proc_ite in H8 as Hinvpr;try reflexivity;destr_hyps.
    exists gamma;split;try solve [constructor 2]. 
    rename P into Pp, Q into Qp.
    constructor;try easy. exists x0;tauto.
    constructor;try easy. constructor. exists x;split;try easy;split. eapply tc_sub;try exact H11;try easy.
    eapply typable_implies_wfC in H8;try easy.
    intros. 
    specialize (H9 n). destr_hyps. inversion H9;subst. exists 0. constructor.
    exists m. easy. 
  }
  {
   inversion Hsess;subst;inversion H3;subst. inversion H6;subst;destr_hyps.
    eapply inv_proc_ite in H8 as Hinvpr;try reflexivity;destr_hyps.
    exists gamma;split;try solve [constructor 2]. 
    rename P into Pp, Q into Qp.
    constructor;try easy. exists x0;tauto.
    constructor;try easy. constructor. exists x;split;try easy;split. eapply tc_sub;try exact H12;try easy.
    eapply typable_implies_wfC in H8;try easy.
    intros. 
    specialize (H9 n). destr_hyps. inversion H9;subst. exists 0. constructor.
    exists m. easy.  
  }
  {
     inversion Hsess;subst. rename H1 into Htwf, H2 into Hins, H3 into Hnodup, H4 into Hfat.
    inversion Hfat;subst. inversion H3;subst. inversion H4;subst. 
    
    destruct H2 as [Tp [Htp [Htypp Hguardp]]]. destruct H5 as [Tq [Htq [Htypq Hguardq]]].
    eapply inv_proc_recv in Htypp as Hrec_inv;try reflexivity.
    eapply inv_proc_send in Htypq as Hsend_inv;try reflexivity.
    destr_hyps.
    rename x2 into g.
    eapply assoc.subtype_recv_inv1 in H8 as Hn;destr_hyps;subst.
    eapply assoc.subtype_send_inv1 in H7 as Hn;destr_hyps;subst.
    rename H11 into Hassoc, H5 into Hwfg.
    assert(Hispartsp : isgPartsC p g).
    {
      destruct (decidable_isgPartsC g p);try easy.
      specialize (Hassoc p). destruct Hassoc.
      specialize (H12 H5 _ Htp);easy. 
    }
    assert(Hispartsq : isgPartsC q g).
    {
      destruct (decidable_isgPartsC g q);try easy.
      specialize (Hassoc q). destruct Hassoc.
      specialize (H12 H5 _ Htq);easy. 
    }
    eapply subtype_recv_inv in H8 as Hsinvrec.
    eapply subtype_send_inv in H7 as Hsinvsend.

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
      rewrite Htq in H5; inversion H5;subst;easy.
    }
    assert (Hsubq: assoc.issubProj (ltt_recv q x2) g p).
    {
      tac_use_assoc Hassoc p Hispartsp;destr_hyps. 
      rewrite Htp in H5;inversion H5;subst;easy.
    }
    eapply assoc.lem_6_16_simul_subproj with (q:=p) (xp:=x3) (xq:=x2) 
    in Hispartsq as Hsim;try easy;try solve [tac_wfl_to_slist

    | 
    specialize (Htwf _ _ Htq); pinversion Htwf; subst;try apply wfltt.wfltt_mon;try easy
    |
    
    specialize (Htwf _ _ Htp); pinversion Htwf; subst;try apply wfltt.wfltt_mon
    ;try easy
    ].
    eapply Forall2R_prop in Hsim;try exact H12;tac_sanitize.
    eapply simple_red_comm in Htp as Hstep;try exact Htq;try easy;
    try exact H12;try exact H15;try easy.
    set (gamma' := (M.add q x4 (M.add p x10 (M.remove q (M.remove p gamma))))).
    exists gamma'.
    split;try solve [constructor;red;exists q, p, l;try easy].
    constructor;try easy.
    assert(Hprojable: projectableA g) by (eapply assoc_implies_projectable in Hassoc;try easy).
    eapply assoc_completeness with (g:=g) in Hstep as Hgstep;try easy. 
    destr_hyps. exists x;split;try easy. eapply wfgC_after_step in H11;try easy.
    
    eapply wfltt.tctx_wf_after_red_comm;try exact Htwf;try exact Hstep.
    
    intros.
    eapply active_parts_subset in H5;try exact Hstep.
    specialize (Hins _ H5) as Hins'.
    red in Hins';simpl in Hins'.
    red;simpl. easy.
    repeat constructor.
    rename x10 into Tp', x4 into Tq'.
    {
      exists Tp'.
      split;unfold gamma';try autorewrite with mmaps;try easy.
      split. 
      eapply Forall2_prop_r in H9;try exact H;tac_sanitize.
      eapply Forall2R_prop in Hsinvrec;try exact H15;tac_sanitize.
      rewrite H11 in H18;inversion H18;subst;clear H18.
      eapply _subst_expr_var with (S:=x11);try easy.
      eapply tc_sub;try exact H20;try easy.

      eapply wfC_recv with (q:=q); try exact H15.
      eapply typable_implies_wfC;try exact Htypp.
      
      + eapply sc_sub;try exact H19. eapply sc_sub;try exact H16;
      eapply sc_sub with (s:=x5);try easy. eapply expr_typ_step;try exact H1;try easy.
      eapply guardP_subst_expr;try easy.
      
      + eapply guardP_cont_recv_n; try exact H;try easy.
    }
    {
      unfold gamma';autorewrite with mmaps.
      exists x4. repeat split;try easy. eapply tc_sub;try exact H6;try easy.
      eapply wfC_send with (p:=p); try exact H12.
      eapply typable_implies_wfC;try exact Htypq.

      intros.  specialize (Hguardq (S n)) as Hq'. destr_hyps. inversion H5;subst.
      exists x. easy.
    }
  }
  {
    inversion Hsess;subst;inversion H3;subst. destr_hyps.
    eapply inv_proc_ite in H6 as Hinvpr;try reflexivity;destr_hyps.
    exists gamma;split;try solve [constructor 2]. 
    rename P into Pp, Q into Qp.
    constructor;try easy. exists x0;tauto.
    constructor;try easy.  exists x;split;try easy;split. eapply tc_sub;try exact H11;try easy.
    eapply typable_implies_wfC in H6;try easy.
    intros. 
    specialize (H7 n). destr_hyps. inversion H7;subst. exists 0. constructor.
    exists m. easy. 
  }
  {
    inversion Hsess;subst;inversion H3;subst. destr_hyps.
    eapply inv_proc_ite in H6 as Hinvpr;try reflexivity;destr_hyps.
    exists gamma;split;try solve [constructor 2]. 
    rename P into Pp, Q into Qp.
    constructor;try easy. exists x0;tauto.
    constructor;try easy.  exists x;split;try easy;split. eapply tc_sub;try exact H10;try easy.
    eapply typable_implies_wfC in H6;try easy.
    intros. 
    specialize (H7 n). destr_hyps. inversion H7;subst. exists 0. constructor.
    exists m. easy. 
  }
  {
    eapply typ_after_unfold in Hsess as Hunfold1;try exact H.
    eapply IHHbeta in Hunfold1 as Hu2. destr_hyps. eapply typ_after_unfold in H1;try exact H0.
    exists x;tauto.
  }
Qed.

Theorem sub_red : forall M M' G, typ_sess M G -> betaP M M' -> exists G', typ_sess M' G' /\ tctxRtc G G'.
Proof.
  intros. revert H. revert G.
  induction H0; intros; try easy.
  (* R-COMM *)
  inversion H1. subst.
  - inversion H5. subst. clear H5. inversion H8. subst. clear H8. 
    inversion H7. subst. clear H7. inversion H10. subst. clear H10. clear H1.
    destruct H6. destruct H1. destruct H7. destruct H6. rename x into T. rename x0 into T'.
    destruct H7 as (H7, Ht). destruct H5 as (H5, Htt).
    - specialize(inv_proc_recv q xs (p_recv q xs) nil nil T H5 (erefl (p_recv q xs))); intros. 
      destruct H8. destruct H8. destruct H10. destruct H11.
    - specialize(inv_proc_send p l e Q (p_send p l e Q) nil nil T' H7 (erefl (p_send p l e Q))); intros.
      destruct H13. destruct H13. destruct H13. destruct H14. rename x0 into S. rename x1 into LT.
    
    specialize(typ_after_step_h q p l); intros.
    specialize(subtype_recv T q x H10); intros. destruct H17. subst.
    specialize(subtype_send T' p (extendLis l (Some (S, LT))) H15); intros. destruct H17. subst.
    rename x0 into LQ. rename x1 into LP.
    specialize(H16 G LP LQ S LT).
    specialize(sub_red_helper l xs x y H H11); intros. destruct H17. destruct H17. destruct H17.
    specialize(H16 x (x0, x1)). 
    assert(exists G' : gtt, gttstepC G G' q p l).
    apply H16; try easy. destruct H19. subst. rename x2 into G'. 
    assert(multiC G G').
    specialize(multiC_step G G' G' q p l); intros. apply H20; try easy. constructor.
    exists G'. split; try easy. clear H20.
    clear H16.
    specialize(wfgC_after_step G G' q p l H2 H19); intros. 
    assert(wfgC G').
    intros. apply H16.
    unfold projectableA. intros.
    specialize(decidable_isgPartsC G pt H2); intros. unfold Decidable.decidable in H20.
    destruct H20.
    specialize(H3 pt H20).
    - unfold InT in H3. simpl in H3.
      - destruct H3. subst. exists (ltt_recv q LQ). easy.
      - destruct H3. subst. exists (ltt_send p LP). easy.
      - specialize(sub_red_helper_3 M G pt); intros. apply H21; try easy.
    - unfold not in H20. exists ltt_end. pfold. constructor; try easy.
    constructor; try easy.
    - intros.
      apply H3; try easy.
      - specialize(part_after_step G G' q p pt l LP LQ); intros. 
        apply H22; try easy.
    specialize(projection_step_label G G' q p l LP LQ); intros.
    assert(exists (LS LS' : sort) (LT LT' : ltt), onth l LP = Some (LS, LT) /\ onth l LQ = Some (LS', LT')).
    apply H21; try easy.
    destruct H22 as (SL,(SL',(TL,(TL',(H22,H23))))).
    
    specialize(canon_rep_w G q p LP LQ SL TL SL' TL' l H2 H6 H22 H1 H23); intros. subst.

    specialize(sub_red_helper_1 H23 H17 H10); intros.
    specialize(sub_red_helper_2 H15 H22); intros. 
    constructor. constructor.
    - constructor.
      specialize(typ_after_step_12_helper q p l G G' LP LQ SL' TL SL' TL'); intros.
      assert(projectionC G' p TL'). apply H26; try easy. clear H26. 
      exists TL'. split; try easy.
      split.
      apply _subst_expr_var with (S := x0); try easy.
      - apply tc_sub with (t := x1); try easy.
        specialize(typable_implies_wfC H5); intros.
        specialize(wfC_recv H26 H23); try easy.
      - apply sc_sub with (s := S); try easy.
        apply expr_typ_step with (e := e); try easy.
        apply sstrans with (s2 := SL'); try easy.
      - specialize(guardP_cont_recv_n l xs y q Htt H); intros.
        specialize(guardP_subst_expr y (e_val v) 0 0); intros. apply H28; try easy.
    - constructor.
      specialize(typ_after_step_12_helper q p l G G' LP LQ SL' TL SL' TL'); intros.
      assert(projectionC G' q TL). apply H26; try easy. clear H26.
      exists TL. split; try easy. split.
      - apply tc_sub with (t := LT); try easy.
        specialize(typable_implies_wfC H7); intros.
        specialize(wfC_send H26 H22); try easy.
      - intros. specialize(Ht (Nat.succ n)). destruct Ht. inversion H26.
        subst. exists x2. easy.
    - specialize(typ_after_step_3_helper_s M q p G G' l LP LQ); intros.
      inversion H4. subst. inversion H30. subst.
      specialize(Classical_Prop.not_or_and (q = p) (In p (flattenT M)) H29); intros. destruct H27.
      apply H26; try easy.

  (* T-COND *)
  inversion H0. subst. inversion H4. subst. clear H4. inversion H7. subst. clear H7.
  destruct H5. destruct H4. destruct H5 as (H5, Ha).
  specialize(inv_proc_ite (p_ite e P Q) e P Q x nil nil H5 (erefl (p_ite e P Q))); intros.
  destruct H6. destruct H6. destruct H6. destruct H7. destruct H9. destruct H10. 
  exists G. split.
  apply t_sess; try easy. apply ForallT_par; try easy.
  apply ForallT_mono; try easy. exists x.
  split; try easy. split.
  apply tc_sub with (t := x0); try easy.
  specialize(typable_implies_wfC H5); try easy.
  - intros. specialize(Ha n). destruct Ha. inversion H12. subst. exists 0. constructor.
    subst. exists m. easy.
  apply multiC_refl.
  
  (* F-COND *)
  inversion H0. subst. inversion H4. subst. clear H4. inversion H7. subst. clear H7.
  destruct H5. destruct H4. destruct H5 as (H5, Ha).
  specialize(inv_proc_ite (p_ite e P Q) e P Q x nil nil H5 (erefl (p_ite e P Q))); intros.
  destruct H6. destruct H6. destruct H6. destruct H7. destruct H9. destruct H10. 
  exists G. split.
  apply t_sess; try easy. apply ForallT_par; try easy.
  apply ForallT_mono; try easy. exists x.
  split; try easy. split.
  apply tc_sub with (t := x1); try easy.
  specialize(typable_implies_wfC H5); try easy.
  - intros. specialize(Ha n). destruct Ha. inversion H12. subst. exists 0. constructor.
    subst. exists m. easy.
  apply multiC_refl.
  
  (* R-COMM *)
  inversion H1. subst.
  - inversion H5. subst. clear H5. inversion H8. subst. clear H8. 
    inversion H9. subst. clear H9.
    destruct H6 as (T,(Ha,(Hb,Hc))). destruct H7 as (T1,(Hd,(He,Hf))).
    - specialize(inv_proc_recv q xs (p_recv q xs) nil nil T Hb (erefl (p_recv q xs))); intros. 
      destruct H5 as (STT,(Hg,(Hh,(Hi,Hj)))).
    - specialize(inv_proc_send p l e Q (p_send p l e Q) nil nil T1 He (erefl (p_send p l e Q))); intros.
      destruct H5 as (S,(T',(Hk,(Hl,Hm)))).
    
    specialize(typ_after_step_h q p l); intros.
    specialize(subtype_recv T q STT Hh); intros. destruct H6. subst.
    specialize(subtype_send T1 p (extendLis l (Some (S, T'))) Hm); intros. destruct H6. subst.
    rename x into LQ. rename x0 into LP.
    specialize(H5 G LP LQ S T').
    specialize(sub_red_helper l xs STT y H Hi); intros. destruct H6. destruct H6. destruct H6.
    specialize(H5 STT (x, x0)). 
    assert(exists G' : gtt, gttstepC G G' q p l).
    apply H5; try easy. destruct H8. subst. rename x1 into G'. 
    assert(multiC G G').
    specialize(multiC_step G G' G' q p l); intros. apply H9; try easy. constructor.
    exists G'. split; try easy.
    specialize(wfgC_after_step G G' q p l H2 H8); intros. 
    assert(wfgC G').
    intros. apply H10.
    unfold projectableA. intros.
    specialize(decidable_isgPartsC G pt H2); intros. unfold Decidable.decidable in H11.
    destruct H11.
    specialize(H3 pt H11).
    - unfold InT in H3. simpl in H3.
      - destruct H3. subst. exists (ltt_recv q LQ). easy.
      - destruct H3. subst. exists (ltt_send p LP). easy.
      - easy.
    - unfold not in H11. exists ltt_end. pfold. constructor; try easy.
    constructor; try easy.
    - intros.
      apply H3; try easy.
      - specialize(part_after_step G G' q p pt l LP LQ); intros. 
        apply H13; try easy.
    specialize(projection_step_label G G' q p l LP LQ); intros.
    assert(exists (LS LS' : sort) (LT LT' : ltt), onth l LP = Some (LS, LT) /\ onth l LQ = Some (LS', LT')).
    apply H12; try easy.
    destruct H13 as (SL,(SL',(TL,(TL',(H22,H23))))).
    
    specialize(canon_rep_s G q p LP LQ SL TL SL' TL' l H2 Hd H22 Ha H23); intros.
    destruct H13 as (Gl,(ctxG,(SI,(Sn,(Hta,(Htb,(Htc,(Htd,(Hte,(Htf,Htg)))))))))).
    specialize(sub_red_helper_1 H23 H6 Hh); intros.
    specialize(sub_red_helper_2 Hm H22); intros. 
    constructor. constructor.
    - specialize(typ_after_step_12_helper q p l G G' LP LQ SL TL SL' TL'); intros.
      assert(projectionC G' p TL'). apply H15; try easy. clear H15. 
      exists TL'. split; try easy.
      split.
      apply _subst_expr_var with (S := x); try easy.
      - apply tc_sub with (t := x0); try easy.
        specialize(typable_implies_wfC Hb); intros.
        specialize(wfC_recv H15 H23); try easy.
      - apply sc_sub with (s := S); try easy.
        apply expr_typ_step with (e := e); try easy.
        apply sstrans with (s2 := SL'); try easy.
        apply sstrans with (s2 := Sn); try easy. 
        apply sstrans with (s2 := SL); try easy.
      - specialize(guardP_cont_recv_n l xs y q Hc H); intros.
        specialize(guardP_subst_expr y (e_val v) 0 0); intros. apply H17; try easy.
    - constructor.
      specialize(typ_after_step_12_helper q p l G G' LP LQ SL TL SL' TL'); intros.
      assert(projectionC G' q TL). apply H15; try easy. clear H15.
      exists TL. split; try easy. split.
      - apply tc_sub with (t := T'); try easy.
        specialize(typable_implies_wfC He); intros.
        specialize(wfC_send H15 H22); try easy.
      - intros. specialize(Hf (Nat.succ n)). destruct Hf. inversion H15.
        subst. exists x1. easy.

  (* T-COND *)
  inversion H0. subst. inversion H4. subst. clear H4.
  destruct H6. destruct H4. destruct H5 as (H5, Ha).
  specialize(inv_proc_ite (p_ite e P Q) e P Q x nil nil H5 (erefl (p_ite e P Q))); intros.
  destruct H6. destruct H6. destruct H6. destruct H7. destruct H8. destruct H9. 
  exists G. split.
  apply t_sess; try easy. constructor. exists x.
  split; try easy. split.
  apply tc_sub with (t := x0); try easy.
  specialize(typable_implies_wfC H5); try easy.
  - intros. specialize(Ha n). destruct Ha. inversion H11. subst. exists 0. constructor.
    subst. exists m. easy.
  apply multiC_refl.
  
  (* F-COND *)
  inversion H0. subst. inversion H4. subst. clear H4.
  destruct H6. destruct H4. destruct H5 as (H5, Ha).
  specialize(inv_proc_ite (p_ite e P Q) e P Q x nil nil H5 (erefl (p_ite e P Q))); intros.
  destruct H6. destruct H6. destruct H6. destruct H7. destruct H8. destruct H9. 
  exists G. split.
  apply t_sess; try easy. constructor. exists x.
  split; try easy. split.
  apply tc_sub with (t := x1); try easy.
  specialize(typable_implies_wfC H5); try easy.
  - intros. specialize(Ha n). destruct Ha. inversion H11. subst. exists 0. constructor.
    subst. exists m. easy.
  apply multiC_refl.
  
  (* R-STRUCT *)
  specialize(typ_after_unfold M1 M1' G H2 H); intros.
  specialize(IHbetaP G H3); intros. destruct IHbetaP. exists x. 
  destruct H4. split; try easy.
  specialize(typ_after_unfold M2' M2 x H4 H0); intros. easy.
Qed.


Theorem prog : forall M G, typ_sess M G -> (exists M', unfoldP M M' /\ (ForallT (fun _ P => P = p_inact) M')) \/ exists M', betaP M M'.
Proof.
  intros.
  destruct G.
  - specialize(canonical_glob_n M H); intros.
    destruct H0 as (M',(Ha,Hb)).
    assert(ForallT (fun _ P => P = p_inact) M' \/ (exists p e p1 p2, typ_proc nil nil (p_ite e p1 p2) ltt_end /\ ((exists M'', unfoldP M' ((p <-- p_ite e p1 p2) ||| M'')) \/ unfoldP M' (p <-- p_ite e p1 p2)))).
    {
      clear H Ha. clear M. revert Hb.
      induction M'; intros.
      - inversion Hb. subst. clear Hb. destruct H0.
        - subst. left. constructor. easy.
        - destruct H as (e,(p1,(p2,(Ha,Hb)))).
          right. exists n. exists e. exists p1. exists p2.  
          split. easy.
          right. subst. apply pc_refl.
      - inversion Hb. subst. clear Hb.
        specialize(IHM'1 H1). specialize(IHM'2 H2). clear H1 H2.
        destruct IHM'1.
        - destruct IHM'2. left. constructor; try easy.
        - destruct H0 as (p0,(e,(p1,(p2,(Ha,Hb))))).
          right. exists p0. exists e. exists p1. exists p2. split. easy.
          left. destruct Hb.
          - destruct H0 as (M1,Hc).
            exists (M1 ||| M'1).
            apply pc_trans with (M' := M'2 ||| M'1). constructor.
            apply pc_trans with (M' := ((p0 <-- p_ite e p1 p2) ||| M1) ||| M'1).
            apply unf_cont_l. easy. constructor.
          - exists M'1. 
            apply pc_trans with (M' := M'2 ||| M'1). constructor.
            apply unf_cont_l. easy.
        - destruct H as (p,(e,(p1,(p2,(Ha,Hb))))).
          destruct Hb.
          - destruct H as (M',H). 
            right. exists p. exists e. exists p1. exists p2. split. easy.
            left. exists (M' ||| M'2).
            apply pc_trans with (M' := ((p <-- p_ite e p1 p2 ||| M') ||| M'2)). apply unf_cont_l. easy.
            constructor.
          - right. exists p. exists e. exists p1. exists p2.
            split. easy.
            left. exists M'2. apply unf_cont_l. easy.
    }
    clear Hb. destruct H0.
    - left. exists M'. easy.
    - destruct H0 as (p,(e,(p1,(p2,(Hb,Hc))))). right.
      destruct Hc. 
      - destruct H0 as (M1,H0).
        assert(unfoldP M ((p <-- p_ite e p1 p2) ||| M1)). apply pc_trans with (M' := M'); try easy.
        clear H0 Ha.
        assert(exists M2, betaP ((p <-- p_ite e p1 p2) ||| M1) M2).
        {
          specialize(inv_proc_ite (p_ite e p1 p2) e p1 p2 ltt_end nil nil Hb (erefl (p_ite e p1 p2))); intros.
          destruct H0 as (T1,(T2,(Ha,(Hf,(Hc,(Hd,He)))))).
          specialize(expr_eval_b e He); intros.
          destruct H0.
          - exists ((p <-- p1) ||| M1). constructor. easy.
          - exists ((p <-- p2) ||| M1). constructor. easy.
        }
        destruct H0 as (M2,H0). exists M2.
        apply r_struct with (M1' := ((p <-- p_ite e p1 p2) ||| M1)) (M2' := M2); try easy. 
        constructor.
      - assert(exists M2, betaP ((p <-- p_ite e p1 p2)) M2).
        { 
          specialize(inv_proc_ite (p_ite e p1 p2) e p1 p2 ltt_end nil nil Hb (erefl (p_ite e p1 p2))); intros.
          destruct H1 as (T1,(T2,(Hg,(Hf,(Hc,(Hd,He)))))).
          specialize(expr_eval_b e He); intros. destruct H1.
          - exists ((p <-- p1)). constructor. easy.
          - exists ((p <-- p2)). constructor. easy.
        }
        destruct H1 as (M2,H1). exists M2.
        apply r_struct with (M1' := (p <-- p_ite e p1 p2)) (M2' := M2); try easy.
        apply pc_trans with (M' := M'); try easy. constructor.
  - right.
    rename n into p. rename n0 into q.
    specialize(canonical_glob_nt M p q l H); intros.
    destruct H0.
    - destruct H0 as (M',(P,(Q,Ha))).
      specialize(typ_after_unfold M (((p <-- P) ||| (q <-- Q)) ||| M') (gtt_send p q l)); intros.
      assert(typ_sess (((p <-- P) ||| (q <-- Q)) ||| M') (gtt_send p q l)). apply H0; try easy.
      clear H0.
      assert(exists M1, betaP (((p <-- P) ||| (q <-- Q)) ||| M') M1).
      {
        inversion H1. subst. inversion H4. subst. clear H4. inversion H7. subst. clear H7.
        inversion H6. subst. clear H6. inversion H9. subst. clear H9.
        destruct H5 as (T,(Hd,(Hb,Hc))). destruct H6 as (T1,(He,(Hf,Hg))).
        clear Ha H2 H3 H8.
        specialize(guardP_break P Hc); intros.
        destruct H2 as (Q1,(Hh,Ho)).
        specialize(typ_proc_after_betaPr P Q1 nil nil T Hh Hb); intros.
        pinversion Hd. subst. assert False. apply H3. apply triv_pt_p; try easy. easy. subst. easy. subst. 
        - specialize(guardP_break Q Hg); intros.
          destruct H3 as (Q2,(Hj,Hl)).
          specialize(typ_proc_after_betaPr Q Q2 nil nil T1 Hj Hf); intros.
          clear H7 H9 Hg Hc H H1 Hd.
          pinversion He; try easy. subst. assert False. apply H. apply triv_pt_q; try easy. easy.
          subst. clear H7 H9 H5 He Hb Hf.
          assert(exists M1, betaP (((p <-- Q1) ||| (q <-- Q2)) ||| M') M1).
          {
            clear Hh Hj.
            destruct Ho.
            - subst. specialize(inv_proc_inact p_inact (ltt_send q ys) nil nil H2 (erefl (p_inact))); intros. 
              easy.
            - destruct H. destruct H as (e,(p1,(p2,Ha))). subst.
              specialize(inv_proc_ite (p_ite e p1 p2) e p1 p2 (ltt_send q ys) nil nil H2 (erefl (p_ite e p1 p2))); intros.
              destruct H as (T1,(T2,(Ha,(Hb,(Hc,(Hd,He)))))).
              specialize(expr_eval_b e He); intros. 
              destruct H.
              - exists ((p <-- p1) ||| ((q <-- Q2) ||| M')).
                apply r_struct with (M1' := ((p <-- p_ite e p1 p2) ||| ((q <-- Q2) ||| M'))) (M2' := ((p <-- p1) ||| ((q <-- Q2) ||| M'))); try easy. constructor. constructor. constructor. easy.
              - exists ((p <-- p2) ||| ((q <-- Q2) ||| M')).
                apply r_struct with (M1' := ((p <-- p_ite e p1 p2) ||| ((q <-- Q2) ||| M'))) (M2' := ((p <-- p2) ||| ((q <-- Q2) ||| M'))); try easy. constructor. constructor. constructor. easy.
            - destruct H.
              destruct H as (pt,(lb,(ex,(pr,Ha)))). subst.
              specialize(inv_proc_send pt lb ex pr (p_send pt lb ex pr) nil nil (ltt_send q ys) H2 (erefl ((p_send pt lb ex pr)))); intros. destruct H as (S,(T1,(Ht,Hb))). clear H2. rename T1 into Tl. rename Hb into Hta. clear M P Q.
              destruct Hl.
              - subst. specialize(inv_proc_inact p_inact (ltt_recv p ys0) nil nil H3 (erefl (p_inact))); intros. 
                easy.
              - destruct H. destruct H as (e,(p1,(p2,Ha))). subst. 
                specialize(inv_proc_ite (p_ite e p1 p2) e p1 p2 (ltt_recv p ys0) nil nil H3 (erefl (p_ite e p1 p2))); intros.
                destruct H as (T1,(T2,(Ha,(Hb,(Hc,(Hd,He)))))).
                specialize(expr_eval_b e He); intros. 
                destruct H.
                - exists ((q <-- p1) ||| ((p <-- p_send pt lb ex pr) ||| M')).
                  apply r_struct with (M1' := ((q <-- p_ite e p1 p2) ||| ((p <-- p_send pt lb ex pr) ||| M'))) (M2' := ((q <-- p1) ||| ((p <-- p_send pt lb ex pr) ||| M'))).
                  apply pc_trans with (M' := ((q <-- p_ite e p1 p2) ||| (p <-- p_send pt lb ex pr)) ||| M').
                  constructor. constructor. apply unf_cont_r. constructor.
                  constructor. easy.
                - exists ((q <-- p2) ||| ((p <-- p_send pt lb ex pr) ||| M')).
                  apply r_struct with (M1' := ((q <-- p_ite e p1 p2) ||| ((p <-- p_send pt lb ex pr) ||| M'))) (M2' := ((q <-- p2) ||| ((p <-- p_send pt lb ex pr) ||| M'))).
                  apply pc_trans with (M' := ((q <-- p_ite e p1 p2) ||| (p <-- p_send pt lb ex pr)) ||| M').
                  constructor. constructor. apply unf_cont_r. constructor.
                  constructor. easy.
              - destruct H. destruct H as (pt1,(lb1,(ex1,(pr1,Ha)))). subst.
                specialize(inv_proc_send pt1 lb1 ex1 pr1 (p_send pt1 lb1 ex1 pr1) nil nil (ltt_recv p ys0) H3 (erefl (p_send pt1 lb1 ex1 pr1))); intros.
                destruct H as (S1,(T1,(Ha,(Hb,Hc)))). pinversion Hc. apply sub_mon.
              - destruct H as (pt2,(llp,Ha)). subst.
                specialize(expr_eval_ss ex S Ht); intros. destruct H as (v, Ha).
                destruct Hta as (Hta,Htb).
                pinversion Htb. subst.
                specialize(inv_proc_recv pt2 llp (p_recv pt2 llp) nil nil (ltt_recv p ys0) H3 (erefl (p_recv pt2 llp))); intros.
                destruct H as (STT,(He,(Hb,(Hc,Hd)))).
                pinversion Hb. subst.
                assert(exists y, onth lb llp = Some y).
                {
                  specialize(subtype_send_inv q (extendLis lb (Some (S, Tl))) ys); intros.
                  assert(Forall2R
                    (fun u v : option (sort * ltt) =>
                     u = None \/
                     (exists (s s' : sort) (t t' : ltt),
                        u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t t'))
                    (extendLis lb (Some (S, Tl))) ys). apply H; try easy.
                  pfold. easy.
                  
                  specialize(subtype_recv_inv p STT ys0); intros.
                  assert(Forall2R
                   (fun u v : option (sort * ltt) =>
                    u = None \/
                    (exists (s s' : sort) (t t' : ltt),
                       u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t' t)) ys0 STT). apply H5. pfold. easy.
                  clear H2 H5 Hd Hb He H H1 Ha Htb Hta Ht H3 H6 H0.
                  revert H7 Hc H4 H11 H10.
                  revert p q l ys ys0 llp S Tl STT. 
                  induction lb; intros.
                  - destruct ys; try easy. destruct l; try easy. destruct ys0; try easy. destruct STT; try easy. destruct llp; try easy.
                    inversion H10. subst. clear H10. inversion H11. subst. clear H11. inversion H7. subst. clear H7. inversion Hc. subst. clear Hc. inversion H4. subst. clear H4.
                    clear H13 H11 H10 H8 H5.
                    destruct H9; try easy. destruct H as (s1,(s2,(t1,(t2,(Ha,(Hb,(Hc,Hd))))))). subst.
                    destruct H2; try easy. destruct H as (s3,(g1,(t3,(He,(Hf,Hg))))). subst.
                    destruct H3; try easy. destruct H as (s4,(g2,(t4,(Hh,(Hi,Hj))))). subst.
                    destruct H6; try easy. destruct H as (s5,(s6,(t5,(t6,(Hk,(Hl,(Hm,Hn))))))). subst.
                    destruct H7; try easy. destruct H as (p1,(s7,(t7,(Ho,(Hp,Hq))))). subst.
                    exists p1. easy.
                  - destruct ys; try easy. destruct l; try easy. destruct ys0; try easy. destruct STT; try easy. destruct llp; try easy.
                    inversion H10. subst. clear H10. inversion H11. subst. clear H11. inversion H7. subst. clear H7. inversion Hc. subst. clear Hc. inversion H4. subst. clear H4.
                    specialize(IHlb p q l ys ys0 llp S Tl STT). apply IHlb; try easy.
                }
                destruct H as (y, H).
                exists ((q <-- subst_expr_proc y (e_val v) 0 0) ||| (p <-- pr) ||| M').
                apply r_struct with (M1' := (((q <-- p_recv p llp) ||| (p <-- p_send q lb ex pr)) ||| M')) (M2' := (((q <-- subst_expr_proc y (e_val v) 0 0) ||| (p <-- pr)) ||| M')); try easy.
                constructor. constructor. constructor. easy. easy.
                apply sub_mon. apply sub_mon.
            - destruct H as (pt,(llp,Ha)). subst.
              specialize(inv_proc_recv pt llp (p_recv pt llp) nil nil (ltt_send q ys) H2 (erefl (p_recv pt llp))); intros.
              destruct H as (STT,(Ha,(Hb,Hc))). pinversion Hb. apply sub_mon.
          }
          destruct H as (M1,Hta). exists M1.
          apply r_struct with (M1' := (((p <-- Q1) ||| (q <-- Q2)) ||| M')) (M2' := M1); try easy.
          apply betaPr_unfold; try easy.
          constructor.
          apply proj_mon.
        subst. easy.
        apply proj_mon.
      }
      destruct H0 as (M1,H0). exists M1.
      apply r_struct with (M1' := (((p <-- P) ||| (q <-- Q)) ||| M')) (M2' := M1); try easy. constructor.
    - destruct H0 as (P,(Q,Ha)).
      specialize(typ_after_unfold M (((p <-- P) ||| (q <-- Q))) (gtt_send p q l)); intros.
      assert(typ_sess ((p <-- P) ||| (q <-- Q)) (gtt_send p q l)). apply H0; try easy.
      clear H0.
      assert(exists M1, betaP (((p <-- P) ||| (q <-- Q))) M1).
      {
        inversion H1. subst. inversion H4. subst. clear H4. inversion H7. subst. clear H7.
        inversion H8. subst. clear H8.
        destruct H5 as (T,(Hd,(Hb,Hc))). destruct H6 as (T1,(He,(Hf,Hg))).
        clear Ha H2 H3.
        specialize(guardP_break P Hc); intros.
        destruct H2 as (Q1,(Hh,Ho)).
        specialize(typ_proc_after_betaPr P Q1 nil nil T Hh Hb); intros.
        pinversion Hd. subst. assert False. apply H3. apply triv_pt_p; try easy. easy. subst. easy. subst. 
        - specialize(guardP_break Q Hg); intros.
          destruct H3 as (Q2,(Hj,Hl)).
          specialize(typ_proc_after_betaPr Q Q2 nil nil T1 Hj Hf); intros.
          clear H7 H9 Hg Hc H H1 Hd.
          pinversion He; try easy. subst. assert False. apply H. apply triv_pt_q; try easy. easy.
          subst. clear H7 H9 H5 He Hb Hf.
          assert(exists M1, betaP (((p <-- Q1) ||| (q <-- Q2))) M1).
          {
            clear Hh Hj.
            destruct Ho.
            - subst. specialize(inv_proc_inact p_inact (ltt_send q ys) nil nil H2 (erefl (p_inact))); intros. 
              easy.
            - destruct H. destruct H as (e,(p1,(p2,Ha))). subst.
              specialize(inv_proc_ite (p_ite e p1 p2) e p1 p2 (ltt_send q ys) nil nil H2 (erefl (p_ite e p1 p2))); intros.
              destruct H as (T1,(T2,(Ha,(Hb,(Hc,(Hd,He)))))).
              specialize(expr_eval_b e He); intros. 
              destruct H.
              - exists ((p <-- p1) ||| ((q <-- Q2))).
                apply r_struct with (M1' := ((p <-- p_ite e p1 p2) ||| ((q <-- Q2)))) (M2' := ((p <-- p1) ||| ((q <-- Q2)))); try easy. constructor. constructor. constructor. easy.
              - exists ((p <-- p2) ||| ((q <-- Q2))).
                apply r_struct with (M1' := ((p <-- p_ite e p1 p2) ||| ((q <-- Q2)))) (M2' := ((p <-- p2) ||| ((q <-- Q2)))); try easy. constructor. constructor. constructor. easy.
            - destruct H.
              destruct H as (pt,(lb,(ex,(pr,Ha)))). subst.
              specialize(inv_proc_send pt lb ex pr (p_send pt lb ex pr) nil nil (ltt_send q ys) H2 (erefl ((p_send pt lb ex pr)))); intros. destruct H as (S,(T1,(Ht,Hb))). clear H2. rename T1 into Tl. rename Hb into Hta. clear M P Q.
              destruct Hl.
              - subst. specialize(inv_proc_inact p_inact (ltt_recv p ys0) nil nil H3 (erefl (p_inact))); intros. 
                easy.
              - destruct H. destruct H as (e,(p1,(p2,Ha))). subst. 
                specialize(inv_proc_ite (p_ite e p1 p2) e p1 p2 (ltt_recv p ys0) nil nil H3 (erefl (p_ite e p1 p2))); intros.
                destruct H as (T1,(T2,(Ha,(Hb,(Hc,(Hd,He)))))).
                specialize(expr_eval_b e He); intros. 
                destruct H.
                - exists ((q <-- p1) ||| ((p <-- p_send pt lb ex pr))).
                  apply r_struct with (M1' := ((q <-- p_ite e p1 p2) ||| ((p <-- p_send pt lb ex pr)))) (M2' := ((q <-- p1) ||| ((p <-- p_send pt lb ex pr)))).
                  apply pc_trans with (M' := ((q <-- p_ite e p1 p2) ||| (p <-- p_send pt lb ex pr))).
                  constructor. constructor. apply unf_cont_r. constructor.
                  constructor. easy.
                - exists ((q <-- p2) ||| ((p <-- p_send pt lb ex pr))).
                  apply r_struct with (M1' := ((q <-- p_ite e p1 p2) ||| ((p <-- p_send pt lb ex pr)))) (M2' := ((q <-- p2) ||| ((p <-- p_send pt lb ex pr)))).
                  apply pc_trans with (M' := ((q <-- p_ite e p1 p2) ||| (p <-- p_send pt lb ex pr))).
                  constructor. constructor. apply unf_cont_r. constructor.
                  constructor. easy.
              - destruct H. destruct H as (pt1,(lb1,(ex1,(pr1,Ha)))). subst.
                specialize(inv_proc_send pt1 lb1 ex1 pr1 (p_send pt1 lb1 ex1 pr1) nil nil (ltt_recv p ys0) H3 (erefl (p_send pt1 lb1 ex1 pr1))); intros.
                destruct H as (S1,(T1,(Ha,(Hb,Hc)))). pinversion Hc. apply sub_mon.
              - destruct H as (pt2,(llp,Ha)). subst.
                specialize(expr_eval_ss ex S Ht); intros. destruct H as (v, Ha).
                destruct Hta as (Hta,Htb).
                pinversion Htb. subst.
                specialize(inv_proc_recv pt2 llp (p_recv pt2 llp) nil nil (ltt_recv p ys0) H3 (erefl (p_recv pt2 llp))); intros.
                destruct H as (STT,(He,(Hb,(Hc,Hd)))).
                pinversion Hb. subst.
                assert(exists y, onth lb llp = Some y).
                {
                  specialize(subtype_send_inv q (extendLis lb (Some (S, Tl))) ys); intros.
                  assert(Forall2R
                    (fun u v : option (sort * ltt) =>
                     u = None \/
                     (exists (s s' : sort) (t t' : ltt),
                        u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t t'))
                    (extendLis lb (Some (S, Tl))) ys). apply H; try easy.
                  pfold. easy.
                  
                  specialize(subtype_recv_inv p STT ys0); intros.
                  assert(Forall2R
                   (fun u v : option (sort * ltt) =>
                    u = None \/
                    (exists (s s' : sort) (t t' : ltt),
                       u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t' t)) ys0 STT). apply H5. pfold. easy.
                  clear H2 H5 Hd Hb He H H1 Ha Htb Hta Ht H3 H6 H0.
                  revert H7 Hc H4 H11 H10.
                  revert p q l ys ys0 llp S Tl STT. 
                  induction lb; intros.
                  - destruct ys; try easy. destruct l; try easy. destruct ys0; try easy. destruct STT; try easy. destruct llp; try easy.
                    inversion H10. subst. clear H10. inversion H11. subst. clear H11. inversion H7. subst. clear H7. inversion Hc. subst. clear Hc. inversion H4. subst. clear H4.
                    clear H13 H11 H10 H8 H5.
                    destruct H9; try easy. destruct H as (s1,(s2,(t1,(t2,(Ha,(Hb,(Hc,Hd))))))). subst.
                    destruct H2; try easy. destruct H as (s3,(g1,(t3,(He,(Hf,Hg))))). subst.
                    destruct H3; try easy. destruct H as (s4,(g2,(t4,(Hh,(Hi,Hj))))). subst.
                    destruct H6; try easy. destruct H as (s5,(s6,(t5,(t6,(Hk,(Hl,(Hm,Hn))))))). subst.
                    destruct H7; try easy. destruct H as (p1,(s7,(t7,(Ho,(Hp,Hq))))). subst.
                    exists p1. easy.
                  - destruct ys; try easy. destruct l; try easy. destruct ys0; try easy. destruct STT; try easy. destruct llp; try easy.
                    inversion H10. subst. clear H10. inversion H11. subst. clear H11. inversion H7. subst. clear H7. inversion Hc. subst. clear Hc. inversion H4. subst. clear H4.
                    specialize(IHlb p q l ys ys0 llp S Tl STT). apply IHlb; try easy.
                }
                destruct H as (y, H).
                exists ((q <-- subst_expr_proc y (e_val v) 0 0) ||| (p <-- pr)).
                apply r_struct with (M1' := (((q <-- p_recv p llp) ||| (p <-- p_send q lb ex pr)))) (M2' := (((q <-- subst_expr_proc y (e_val v) 0 0) ||| (p <-- pr)))); try easy.
                constructor. constructor. constructor. easy. easy.
                apply sub_mon. apply sub_mon.
            - destruct H as (pt,(llp,Ha)). subst.
              specialize(inv_proc_recv pt llp (p_recv pt llp) nil nil (ltt_send q ys) H2 (erefl (p_recv pt llp))); intros.
              destruct H as (STT,(Ha,(Hb,Hc))). pinversion Hb. apply sub_mon.
          }
          destruct H as (M1,Hta). exists M1.
          apply r_struct with (M1' := (((p <-- Q1) ||| (q <-- Q2)))) (M2' := M1); try easy.
          apply betaPr_unfold_h; try easy.
          constructor.
          apply proj_mon.
        subst. easy.
        apply proj_mon.
      }
      destruct H0 as (M1,H0). exists M1.
      apply r_struct with (M1' := (((p <-- P) ||| (q <-- Q)))) (M2' := M1); try easy. constructor.
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
