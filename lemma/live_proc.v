From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Coq.Program.Equality Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
From SST Require Import src.header src.sim src.expr src.process src.local 
src.global src.balanced src.typecheck src.part src.gttreeh src.path_props src.step src.merge src.projection src.session src.lcontext.  
From SST Require Import lemma.inversion lemma.inversion_expr lemma.completeness lemma.substitution_helper lemma.substitution lemma.decidable_helper lemma.decidable lemma.expr lemma.part lemma.step 
lemma.projection_helper lemma.subj_red_prog lemma.projection lemma.main_helper lemma.soundness lemma.liveness_helpers. 

Inductive betaRtc : session -> session -> Prop:=
    | betaRt_unf : forall a b, unfoldP a b -> betaRtc a b
    | betaRt_beta : forall a b, betaP a b -> betaRtc a b
    | betaRtrans : forall a b c, betaRtc a b -> betaRtc b c -> betaRtc a c.

Definition all_guarded P := forall n, exists m, guardP n m P.

Lemma guard_ite_inv : forall e P Q, all_guarded (p_ite e P Q) -> all_guarded P /\ all_guarded Q. 
Proof.
    intros;split;unfold all_guarded in *;
        intros; specialize (H n); destr_hyps; inversion H;subst;
        try solve [
        exists 0; constructor |  exists m;easy].
Qed.

Fixpoint is_unfolded P := match P with
  | p_ite e P1 P2 => is_unfolded P1 /\ is_unfolded P2
  | p_send _ _ _ _ => True
  | p_recv _ _ => True
  | p_inact => True
  | _ => False end.

Lemma guardP_break_full :forall P,
    (forall n : fin, exists m : fin, guardP n m P) -> 
    exists Q, multi betaPr P Q /\ is_unfolded Q.
Proof.
    intros * Hguard.
    induction P.
    {
        exists (p_send n n0 e P);split;try constructor;easy.
    }
    {
        exists (p_recv n l);split;try constructor;easy. 
    }
    {
        eapply guard_ite_inv in Hguard as Hg2. destr_hyps.
        specialize (IHP1 H). specialize (IHP2 H0). destr_hyps.
        assert(betaPr (p_ite e P1 P2) (p_ite e x0 P2)).
        {
            econstructor 2.         
        }
        exists (p_ite e x0 x). split. econstructor 2.   
    }
  eapply guardP_break in H.
  destruct H. exists x. 
  
  destruct H. split;try easy.
  induction x;try easy.
  {

  }
  destruct H0;subst;try easy.
  destruct H0;subst;destr_hyps.

Lemma guarded_after_unfold : forall P P', all_guarded P ->  betaPr P P' -> all_guarded P'.
Proof.
    intros. unfold all_guarded in *.
    Search guardP.
    inversion H0;subst.
    intros. specialize (H n). destr_hyps. inversion H;subst. exists 0. constructor.
    Search substitutionP.
    eapply substitution_helper.inj_substP in H1;try exact H3;subst;exists m;easy.
Qed.

Lemma guarded_after_multi_unfold : forall P P', all_guarded P ->  multi betaPr P P' -> all_guarded P'.
Proof.
    intros.
    induction H0;try easy.
    eapply IHmulti. eapply guarded_after_unfold with (P:=x);easy.
Qed.

Lemma betaPr_unfold_one : forall P P' p, multi betaPr P P' -> unfoldP (p <-- P) (p <-- P').
Proof.
    intros.
    induction H.
    constructor. inversion H;subst. Search unfoldP.
    eapply pc_trans with (M':= (p <-- y));try easy.
    eapply pc_subm. easy.
Qed.
(*
Hint Resolve betaPr_unfold_one :procs.

Fixpoint is_unfolded Q := 
    match Q with 
    | p_inact => True
    | p_send _ _ _ _ => True
    | p_recv _ _ => True
    | p_ite e p1 p2 => is_unfolded p1 /\ is_unfolded p2 
    | _ => False end.


Lemma guardP_break_plus : forall P, all_guarded P -> exists Q, 
    forall r, unfoldP (r <-- P) (r <-- Q) /\ is_unfolded Q.
Proof.
    intros.
    induction P;
    eapply guardP_break in H as Hguard; destr_hyps;
    try solve [
    exists x;intros;split;try eauto with procs;inversion H0;subst;easy].
    eapply guarded_after_multi_unfold in H as Hguard';try exact H0.
    
    destruct H1 as [Hu | [Hu | [Hu | Hu]]];destr_hyps;subst;
    inversion H0;subst;try easy.
    eapply guard_ite_inv in Hguard'. destr_hyps.
    specialize (IHP1 H1). specialize (IHP2 H2).
    destr_hyps.
    exists (p_ite x0 x3 x2). intros. specialize (H4 r). specialize (H3 r).
    destr_hyps.
    split;try eauto with procs.
    Search unfoldP.
    inversion H0;subst. clear H1.
*)

(*
Lemma inv_proc_send : forall M gamma p q xsp, typ_sess M gamma ->
M.find p gamma = Some (ltt_send q xsp) -> (exists M' M'' P' e ell,
(betaRtc M M' \/ unfoldP M M') /\ 
unfoldP M' ((p <-- p_send q ell e P')||| M'')).
Proof.
    intros * Hsess Hfindp.
    assert(Hinp:InT p M) by (
    inversion Hsess;subst;eapply H0;red;exists (ltt_send q xsp);split;easy).
    eapply move_forward_h in Hinp as Hmf.
    destruct Hmf.
    {
        destruct H as [P [M' Hunf]].
        eapply typ_after_unfold in Hsess as Hsess';try exact Hunf.
        assert(Hprocs  :typ_proc [] [] P (ltt_send q xsp) /\
        (forall n : opt_lbl, exists m : opt_lbl, guardP n m P)).
        {
            inversion Hsess';subst.
        
            inversion_clear H2;subst;inversion_clear H3. destr_hyps.
            clear H4 H1 H0.
            rewrite Hfindp in H2;inversion H2;subst;clear H2. tauto.
        }
        destruct Hprocs as [Hproc Hguard].
        evar (Cs: list (option sort)).
        evar (Ct: list (option ltt)).
        instantiate (Ct:=[]).
        instantiate (Cs:=[]).
        generalize dependent M.
        generalize dependent M'.
        generalize dependent gamma.
        fold Cs in Hproc.
        fold Ct in Hproc.
        clearbody Cs Ct.
        pose proof Hproc as Htyp'.
        dependent induction Htyp'.
        {
            specialize (Hguard 1). destr_hyps. inversion H1. 
        }
        {
            intros.
            assert(exists Q, substitutionP 0 0 0 (p_rec p0) p0 Q).
            {
                eapply guardP_break in Hguard.
                destr_hyps. inversion H;subst.
                destruct H0 as [H0 | [H0 | [H0 | H0]]];destr_hyps;subst; try easy.
                inversion H1;subst.
                exists y;easy.
            }
            destruct H as [Q Hsubst].
            Search substitutionP typ_proc.
            eapply IHHtyp' with (,:=in Htyp'.
            eapply inv_proc_rec in Hproc;try reflexivity. destr_hyps.
            eapply subst_proc_varf in Hsubst;try exact H.
            Print typ_proc.
 
            
            assert(typ_proc cs (Some (ltt_send q xsp) :: ct) p0 (ltt_send q xsp)) by admit.

            eapply IHHtyp' in H1;try easy.
            intros.
            specialize (Hguard n). destr_hyps. inversion H2;subst. exists 0. constructor.
            Search guardP substitutionP.
            assert(betaPr (p_rec p0) Q). constructor;easy.
            Search guardP betaPr.
            eapply gp_rec in H4;try exact H7. Print guardP.
            inversion Hproc;subst.
        }
        {
            intros. eapply inv_proc_ite in Htyp;try reflexivity;destr_hyps.
            assert(Hguard1: all_guarded p1).
            {
                eapply guarded_after_multi_unfold in Punf;try exact Hguard.
                eapply guard_ite_inv in Punf;try easy.
            }
            assert(Hguard2: all_guarded p2).
            {
                eapply guarded_after_multi_unfold in Punf;try exact Hguard.
                eapply guard_ite_inv in Punf;try easy.
            }
            eapply guardP_break in Hguard1 as [P1 Hbre1]. 
            eapply guardP_break in Hguard2 as [P2 Hbre2].
            assert (Hnp: unfoldP M ((p <-- p_ite e p1 p2) ||| M')).
            {
                destr_hyps.   
                eauto with procs.
            }
            eapply expr_eval_b in H4. destruct H4.            

            assert(Hbet: betaP ((p <-- p_ite e p1 p2) ||| M') ((p <-- p1) ||| M'))
            by (eapply rt_ite;easy).
            eapply IHHtyp'1 with (P:=P1) (M:=((p <-- P1) ||| M')) in Hfindp as IH_use; try easy. 
            admit. right.
        }

        induction Punf.
        assert(typ_proc [] [] )
    }
*)


Lemma typ_proc_inv_send : forall M gamma p q xsp xsq, typ_sess M gamma ->
    M.find p gamma = Some (ltt_send q xsp) ->
    M.find q gamma = Some (ltt_recv p xsq) ->
    (exists Mr ell e P', unfoldP M ((p <-- p_send q ell e P') ||| Mr)) \/
    (exists Mr e Pt Pf, unfoldP M ((p <-- p_ite e Pt Pf) ||| Mr)).
Proof.
    intros * Hsess Hfindp Hfindq.
    assert(Hpq: p <> q) by (red;intros;subst;congruence).
    eapply canonical_glob_nt with (xsq:=xsq) in Hfindp as Hcanon;try exact Hsess;try easy.
    destruct Hcanon.
    {
        destr_hyps. eapply typ_after_unfold in H as Htu;try exact Hsess. inversion Htu;subst.
        inversion_clear H3. inversion_clear H4. inversion_clear H3 . inversion_clear H6.
        destr_hyps.
        assert(x3=ltt_send q xsp) by (congruence);subst.
        assert(x2=ltt_recv p xsq) by congruence;subst.
        eapply guardP_break in H10;destr_hyps.
        destruct H12 as [Hdr | [Hdr | [Hdr |Hdr]]];destr_hyps;subst;eapply typ_proc_after_betaPr in H10 as Htunf;try exact H9.
        {
         eapply inv_proc_inact in Htunf;easy.
        }
        {
            right.
            exists ((q <-- x1) ||| x), x3, x5, x6.
            assert(unfoldP M ((p <-- x0) ||| ((q <-- x1) ||| x))). eauto with procs.
            assert(multi betaPr x1 x1) by constructor.
            eauto with procs.
        }
        {
            left. 
            eapply inv_proc_send in Htunf as Ht;try reflexivity. 
            destr_hyps. pinversion H14;subst;try apply sub_mon.
            
            exists ((q <-- x1) ||| x), x5, x6, x7.
            assert(multi betaPr x1 x1) by constructor. eauto with procs.
        }
        {
            eapply inv_proc_recv in Htunf;try reflexivity. destr_hyps. pinversion H13;try apply sub_mon.   
        }
    }
    {
        destr_hyps. eapply typ_after_unfold in H as Htu;try exact Hsess. inversion Htu;subst.
        inversion_clear H3. inversion_clear H4. inversion_clear H3 . inversion_clear H5.
        destr_hyps.
        assert(x1=ltt_send q xsp) by (congruence);subst.
        assert(x2=ltt_recv p xsq) by congruence;subst.
        eapply guardP_break in H9;destr_hyps.
        destruct H11 as [Hdr | [Hdr | [Hdr |Hdr]]];destr_hyps;subst;eapply typ_proc_after_betaPr in H9 as Htunf;try exact H8.
        {
         eapply inv_proc_inact in Htunf;easy.
        }
        {
            right.
            exists ((q <-- x0)), x2, x4, x5.
            assert(unfoldP M ((p <-- x) ||| ((q <-- x0)))). eauto with procs.
            assert(multi betaPr x0 x0) by constructor.
            eauto with procs.
        }
        {
            left. 
            eapply inv_proc_send in Htunf as Ht;try reflexivity. 
            destr_hyps. pinversion H13;subst;try apply sub_mon.
            
            exists ((q <-- x0) ), x4, x5, x6.
            assert(multi betaPr x0 x0) by constructor. eauto with procs.
        }
        {
            eapply inv_proc_recv in Htunf;try reflexivity. destr_hyps. pinversion H12;try apply sub_mon.   
        }
    }
Qed.

Lemma SList_extendLis {A:Type}: forall n (a:A), SList (extendLis n (Some a)).
                Proof.
                    induction n;intros; simpl;easy.
                Qed.
(*
Theorem sess_fidelity_send : forall M gamma p q   ell gamma', 
typ_sess M gamma -> tctxR gamma (lcomm p q ell) gamma' -> 
    (exists gamma'' M' ell', tctxR gamma (lcomm p q ell') gamma'' /\ 
    betaP M M' /\ typ_sess M' gamma'') \/
    (exists gamma M', 
    betaP M M' /\ typ_sess M' gamma).
Proof.
    intros * Hsess Hstep.
    eapply lem_6_11c_tctx_comm_invert in Hstep;destr_hyps.
    eapply typ_proc_inv_send in H as Hp_dil;try exact Hsess;try exact H0.
    destruct Hp_dil.
    {
        destr_hyps.
        left.
        eapply typ_after_unfold in H6 as Hu;try exact Hsess.
        assert ((exists Q M', unfoldP x5 ((q <-- Q) ||| M')) \/ (exists Q, unfoldP x5 ((q <-- Q)))).
        {
            inversion Hu;subst.
            assert(Hinq : InT q ((p <-- p_send q x6 x7 x8) ||| x5)).
            {
                eapply H8;red;exists (ltt_recv p x3);split;easy.   
            }
            red in Hinq. simpl in Hinq.
            destruct Hinq;subst;try congruence. assert(InT q x5) by (red;easy).
            eapply move_forward_h in H12;destr_hyps.
            destruct H12. destr_hyps. left. exists x10, x11;easy.
            right. destr_hyps. exists x10;easy.
        }
        destruct H7 as [Hunfq | Hunfq];destr_hyps.
        {
            assert (Hunfm :unfoldP M ((p <-- p_send q x6 x7 x8) |||( (q <-- x9) ||| x10))).
            {
                eauto with procs.   
            }
            eapply typ_after_unfold in Hunfm as Hsess2;try exact Hsess.
            inversion Hsess2;subst. inversion_clear H11. inversion_clear H13.
            inversion_clear H11. inversion_clear H12.
            destr_hyps.
            assert(x11 = ltt_send q x1) by congruence.
            assert(x12 = ltt_recv p x3) by congruence.
            subst.
            eapply inv_proc_send in H15;try reflexivity. destr_hyps.
            assert(exists gamma'', tctxR gamma (lcomm p q x6) gamma'').
            {
                rename x13 into g.
                assert (assoc.issubProj (ltt_send q (extendLis x6 (Some (x11, x12)))) g p).
                {
                    eapply assoc_inv_find with (g:=g) in H11;try easy.
                    red in H11. destr_hyps.
                    red. exists x13. split;try easy. eapply stTrans;try exact H21;easy.
                }
                eapply assoc_inv_find with (g:=g) in H12 as Hinf;try easy.
                assert(SList x3).
                {
                    red in H8. specialize (H8 _ _ H12). pinversion H8;subst;try easy;try apply wfltt.wfltt_mon.   
                }
                assert (isgPartsC p g).
                {
                    red in H22. destr_hyps. destruct (decidable.decidable_isgPartsC g p);try easy.
                    eapply assoc.subtype_send_inv1 in H24;destr_hyps;subst. pinversion H22;subst;try easy;
                    try apply proj_mon.   
                }
                eapply assoc.lem_6_16_simul_subproj in H22;try exact Hinf;try easy;
                try eapply SList_extendLis.
                assert(onth x6 (extendLis x6 (Some (x11, x12)))=Some (x11,x12)) by (rewrite extendExtract;easy).
                
                eapply Forall2R_prop in H22;try exact H25;tac_sanitize.
                eapply simpl
                Search tctxR M.find.
                Search "simul" assoc.issubProj.
            }
        }
    }    

    eapply typ_after_unfold in Hunf as Hsess';try exact Hsess.
    inversion Hsess';subst. 
    
    rename H into Htwf, H0 into Hin, H1 into Hndup, H2 into Hfat.

    eapply lem_6_11c_tctx_comm_invert in Hstep;destr_hyps.
    assert(Hpq_neq: p <> q) by (red;intros;subst;congruence).
    assert(Hinp: InT p M) by (eapply Hin;red; exists (ltt_send q x2);easy).
    assert(Hinq: InT q M) by (eapply Hin;red; exists (ltt_recv p x4);easy).
    eapply canonical_glob_nt in H0 as Hcanon;try exact H2;try exact Hsess;try easy.
    destruct Hcanon as [Hcanon | Hcanon].
    {
        destruct Hcanon as [M' [P [Q Hunf]]].
        eapply typ_after_unfold in Hunf as Hsess';try exact Hsess.
       
        clear x H H1 Htwf Hin Hndup Hfat. 
        inversion Hsess';subst. destruct Hassocable as [g [Hwfg Hassoc]].
        rename H into Htwf, H1 into Hinend, H8 into Hnodup, H9 into Hfat.
        inversion_clear Hfat;subst. inversion_clear H;subst. inversion_clear H8.
        inversion_clear H9. destr_hyps.
        rewrite H0 in H;inversion H;subst.
        rewrite H2 in H8;inversion H8;subst;clear H H8.
        generalize dependent M.
        induction P. 1-2:admit.
        {
            eapply inv_proc_ite in H11 as Hite;try reflexivity;destr_hyps.
            eapply expr_eval_b in H15.
            destruct H15;try easy.
            {
                intros.
                
                assert(Hbet: betaP ((p <-- p_ite e P1 P2) ||| ((q <-- Q) ||| M')) 
                ((p <-- P1 ) ||| ((q <-- Q) ||| M'))) by (constructor;try easy).
                assert(Hunf': unfoldP M ((p <-- p_ite e P1 P2) ||| ((q <-- Q) ||| M'))) by
                eauto with procs.
                assert(Hbet2 : betaP M ((p <-- P1) ||| ((q <-- Q) ||| M'))).
                eapply r_struct;try exact Hbet;try easy;try constructor.
                assert(unfoldP ((p <-- P1) ||| ((q <-- Q) ||| M')) ((p <-- P1) ||| ((q <-- Q) ||| M'))) by constructor.
                admit.
            }
            admit.
        }
        {
            intros.

        }

        rename H11 into Htypp.
        induction P.
        {
            admit.      
        }
        {
            admit.   
        }
        {

        }

        eapply guardP_break in H12. destruct H12 as [Punf [Hpunf Htr]].
        eapply typ_proc_after_betaPr in Htypp as Htyp_unf;try exact Hpunf.
        
        pose proof Htyp_unf as Htyp_unfr.
        dependent induction Htyp_unfr.
        {
            destruct Htr as [Hu | [Hu | [Hu | Hu]]];destr_hyps;subst;try easy.
        }
        {
            destruct Htr as [Hu | [Hu | [Hu | Hu]]];destr_hyps;subst;try easy.
        }
        {

            eapply inv_proc_ite in Htyp_unf as Hinv_ite;try reflexivity;destr_hyps.
            eapply expr_eval_b in H14.
            destruct H14.
            {

            }
            Search typ_expr sbool.
        }
        
    }
    specialize (Hin p). unfold in_not_end in Hin.
*)

Definition live_sess (Mp:session) := forall M p q ell e P' Mr, betaRtc Mp M -> 
    (unfoldP M (p <-- p_send q ell e P' ||| Mr)) -> exists M', betaRtc M M' /\
    exists Mr', unfoldP M' ((p <-- P') ||| Mr').
