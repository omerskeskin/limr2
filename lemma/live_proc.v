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

Definition betaRtc := clos_refl_trans session betaP.
Check p_send.
Check typ_sess.

Check guardP_break.

Definition all_guarded P := forall n, exists m, guardP n m P.

Lemma guard_ite_inv : forall e P Q, all_guarded (p_ite e P Q) -> all_guarded P /\ all_guarded Q. 
Proof.
    intros;split;unfold all_guarded in *;
        intros; specialize (H n); destr_hyps; inversion H;subst;
        try solve [
        exists 0; constructor |  exists m;easy].
Qed.

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

Lemma inv_proc_send : forall M gamma p q xsp, typ_sess M gamma ->
M.find p gamma = Some (ltt_send q xsp) -> exists M' M'' P' e ell,
betaRtc M M' /\ 
unfoldP M' ((p <-- p_send q ell e P')||| M'').
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
        eapply guardP_break in Hguard as Htr;destr_hyps. rename H into Punf.
        eapply typ_proc_after_betaPr in Punf as Htyp';try exact Hproc.
        rename H0 into Htr.
        generalize dependent M.
        pose proof Htyp' as Htyp.
        generalize dependent P. 
        dependent induction Htyp'.
        {
            intros.
            destruct Htr as [Hu | [Hu | [Hu | Hu]]];destr_hyps;subst;easy. 
        }
        {
            intros.
            destruct Htr as [Hu | [Hu | [Hu | Hu]]];destr_hyps;subst;easy. 
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
            eapply IHHtyp'1 with (P:=p1) (M:=((p <-- p1) ||| M')) in Hfindp as IH_use; try easy. 
            admit. right.
        }

        induction Punf.
        assert(typ_proc [] [] )
    }
Theorem sess_fidelity : forall M gamma p q ell gamma', 
typ_sess M gamma -> tctxR gamma (lcomm p q ell) gamma' ->
    exists gamma'' M', tctxR gamma (lcomm p q ell) gamma'' /\ betaRtc M M' /\ typ_sess M' gamma''.
Proof.
    intros * Hsess Hstep.
    inversion Hsess;subst. rename H into Htwf, H0 into Hin, H1 into Hndup, H2 into Hfat.
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
        rename H11 into Htypp.
        eapply guardP_break in H12. destruct H12 as [Punf [Hpunf Htr]].
        eapply typ_proc_after_betaPr in Htypp as Htyp_unf;try exact Hpunf.
        induction Punf.
        {
            admit.   
        }
        {
            admit.
        }
        {

        }
        (*evar (Cs: list (option sort)).
        evar (Ct: list (option ltt)).
        instantiate (Ct:=[]).
        instantiate (Cs:=[]).
        fold Cs in Htypp.
        fold Ct in Htypp.
        clearbody Cs Ct.
        generalize dependent Cs.
        generalize dependent Ct.
        intros.
        
        clear H6 H7 x5 x3 x0 x1 H3 H4 H5.
        rename x2 into xsp, x4 into xsq.
        
        remember (ltt_send q x2) as t_lbl.
        pose proof Htypp as Htypp_rem.

        induction Htypp;try easy.
        {
            
            specialize (H12 1). destr_hyps. 
            inversion H11;subst.
        }
        {
            eapply guardP_break in H12.
            destr_hyps. rename x into Punf.
            destruct H8;subst.
            { 
                eapply typ_proc_after_betaPr in Htypp_rem;try exact H.
                eapply inv_proc_inact in Htypp_rem;subst;try easy.
            }
            destruct H8.
            {
                destr_hyps;subst.
                eapply typ_proc_after_betaPr in Htypp_rem;try exact H.
                eapply inv_proc_ite in Htypp_rem;try reflexivity;destr_hyps;subst.
                eapply IHHtypp  in Hsess as IH_use;try assumption.
                all:try easy.
                Print "~=".
            }   
        }
        (*dep ind*)
        eapply guardP_break in H12. destruct H12 as [Punf [Hpunf Htr]].
        eapply typ_proc_after_betaPr in Htypp as Htyp_unf;try exact Hpunf.
        (*evar (Cs: list (option sort)).
        evar (Ct: list (option ltt)).
        instantiate (Ct:=[]).
        instantiate (Cs:=[]).
        fold Cs in Htyp_unf.
        fold Ct in Htyp_unf.
        clearbody Cs Ct.*)
        pose proof Htyp_unf as Htyp_unfr.
        dependent induction Htyp_unfr.
        {
            destruct Htr as [Hu | [Hu | [Hu | Hu]]];destr_hyps;subst;try easy.
        }
        {
            destruct Htr as [Hu | [Hu | [Hu | Hu]]];destr_hyps;subst;try easy.
        }
        {   
            eapply inv_proc_ite in Htyp_unf;try reflexivity;destr_hyps.
            eapply expr_eval_b in H14.
            destruct H14.
            {
                eapply IHHtyp_unfr1 with (q:=q) (x2:=x2) in H9 ;try easy.   
            }
            Search typ_expr sbool.
        }*)
        
    }
    specialize (Hin p). unfold in_not_end in Hin.

Definition live_sess (Mp:session) := forall M p q ell e P' Mr, betaRtc Mp M -> 
    (unfoldP M (p <-- p_send q ell e P' ||| Mr)) -> exists M', betaRtc M M' /\
    exists Mr', unfoldP M' ((p <-- P') ||| Mr').
