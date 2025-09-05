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

Hint Resolve betaPr_unfold_one :procs.

Definition betaPtrans := clos_trans process  betaPr. 

Check guardP_break.

Inductive is_ite_or_send : process -> Prop :=
    | ite_send_send: forall q ell e P', is_ite_or_send (p_send q ell e P')
    | ite_send_rec: forall P P',  betaPtrans (p_rec P) P' -> is_ite_or_send P' -> is_ite_or_send (p_rec P)
    | ite_send_ite : forall e P1 P2, is_ite_or_send P1 -> is_ite_or_send P2 -> is_ite_or_send (p_ite e P1 P2).

Search (relation _ -> relation _ -> relation _) .

Lemma betaRtc_stronger : forall a b, multi betaP a b -> betaRtc a b.
Proof.
    intros.
    induction H. constructor. eauto with procs.
    econstructor 3;try exact IHmulti. constructor 2. easy.
Qed.

Lemma betaPrtrans_implies_multi : forall a b, betaPtrans a b -> multi betaPr a b.
Proof.
    intros.
    induction H;subst. econstructor 2;try exact H;try constructor.
    eapply transitive_multi;try exact IHclos_trans1;easy.
Qed.

Hint Resolve betaPrtrans_implies_multi :procs.

Theorem is_ite_implies_beta_send : forall M  p  P Tp, 
is_ite_or_send P -> typ_proc [] [] P Tp -> exists q ell e P',
    betaRtc (p <-- P ||| M) (p <-- p_send q ell e P' ||| M).
Proof.
    intros * Hite Htyp. induction Hite.
    {
     exists q, ell ,e, P'.  constructor. eauto with procs.      
    }
    {
        destr_hyps.
        
        eapply typ_proc_after_betaPr in Htyp;try exact H. specialize (IHHite Htyp).
        destr_hyps. 
        
        exists x, x0, x1, x2. econstructor 3;try exact H0. constructor 1. 
        1-2: eauto with procs. 
    }
    {
        eapply typable_implies_wfC in Htyp as Hwfc.   
        eapply inv_proc_ite in Htyp;try reflexivity. destr_hyps.
        assert(typ_proc [] [] P1 Tp). eapply tc_sub;try exact H;try easy.
        
        assert(typ_proc [] [] P2 Tp). eapply tc_sub;try exact H0;try easy.
        specialize (IHHite1 H4).
        specialize (IHHite2 H5).
        eapply expr_eval_b in H3. destruct H3.
        {
            assert(betaP ((p <-- p_ite e P1 P2) ||| M) ((p <-- P1 ) ||| M)) by (constructor;easy).
            destr_hyps. exists x5, x6, x7, x8.
            eapply betaRt_beta in H6.
            econstructor 3; try exact H6. easy.   
        }
        {
         
            assert(betaP ((p <-- p_ite e P1 P2) ||| M) ((p <-- P2) ||| M)) by (constructor;easy).
            destr_hyps. exists x1, x2, x3, x4.
            eapply betaRt_beta in H6.
            econstructor 3; try exact H6. easy.   
        }

    }
Qed.

Lemma betaPr_unique : forall a b c, betaPr a b -> betaPr a c -> b=c.
        intros. inversion H;inversion H0;subst.
        inversion H5;subst.
        eapply substitution_helper.inj_substP in H1;try exact H4;subst;easy.
Qed.

Lemma betaPr_factor : forall a b c, betaPr a b -> betaPtrans a c -> 
(betaPtrans b c  \/ b=c).
Proof.
    intros.
    induction H0;intros;try tauto.
    {
        eapply betaPr_unique in H;try exact H0;subst;tauto.
    }
    {
        specialize (IHclos_trans1 H). destruct IHclos_trans1.
        left. econstructor 2;try exact H0_0. easy.
        subst. left. easy.   
    }
Qed.

Lemma betaPr_linear : forall a b c, betaPtrans a b -> betaPtrans a c -> 
(betaPtrans b c  \/ betaPtrans c b \/ b=c).
Proof.
    intros.
    induction H;intros;try tauto.
    {
        eapply betaPr_factor in H0;try exact H. tauto.
    }
    {
        specialize (IHclos_trans1 H0). destruct IHclos_trans1.
        eapply IHclos_trans2;easy.

        destruct H2;subst. right. left. econstructor 2;try exact H1;easy.
        right. left. easy.   
    }
Qed.

Lemma betaPr_trans_form : forall x y, betaPtrans x y -> exists z, x=p_rec z.
Proof.
    intros. induction H.
    inversion H;subst. exists P;easy.
    destr_hyps;subst. exists x1. easy.
Qed.

Lemma is_ite_or_send_betaPr : forall P Q, is_ite_or_send P -> betaPtrans P Q ->
is_ite_or_send Q.
Proof.
    intros * Hite. generalize dependent Q. 
    induction Hite;intros * Hunf;try solve [inversion Hunf].
    {
        eapply betaPr_trans_form in Hunf;destr_hyps;subst;easy.
    }
    {   
        eapply betaPr_linear in Hunf as Hdil;try exact H.
        destruct Hdil.
        {
         
            eapply IHHite;easy.
        }
        destruct H0;subst.
        eapply betaPr_trans_form in H0 as Ht;destr_hyps;subst.
        econstructor 2;try exact H0;try easy.
        easy.
    }
    {
     eapply betaPr_trans_form in Hunf;destr_hyps;subst;easy.
    }
Qed.

Theorem typ_send_means_ite_or_send :  forall   P gs gt q xsp, 
typ_proc gs gt P (ltt_send q xsp) -> is_ite_or_send P.
Proof.
    induction P;intros.
    { constructor.   
    }
    {
        eapply inv_proc_recv in H;try reflexivity;destr_hyps. pinversion H0;try apply sub_mon.       
    }
    {
        eapply typable_implies_wfC in H as Hwfc.
        eapply inv_proc_ite in H;try reflexivity;destr_hyps.
        
        eapply tc_sub in H;try exact H1;try easy.
        eapply tc_sub in H0;try exact H2;try easy.
        constructor. eapply IHP1;try exact H.
        eapply IHP2;try exact H0.   
    }
    {
        
        eapply typable_implies_wfC in H as Hwfc.
        eapply inv_proc_rec in H;try reflexivity;destr_hyps.
        eapply tc_sub in H;try exact H0;try easy.
        
        

        Lemma is_ite_guarded : forall P Q R, all_guarded (p_rec P) -> 
        substitutionP 0 0 0 R P Q -> 
        is_ite_or_send Q -> is_ite_or_send P.
        Proof.
            intros. 
            generalize dependent Q.
            generalize dependent R.
            induction P;intros.
            { 
                constructor.   
            }
            {
                inversion H0;subst. inversion H1.   
            }
            {
                constructor;
                inversion H0;subst;
                inversion H1;subst.
                eapply IHP1;try exact H10;try easy.
                admit.
                eapply IHP2;try exact H11;try easy.
                admit. 
            }
            {
                econstructor.   
            }
            econstructor;try*)
        econstructor.
        
        eapply IHP in H.
    }
    intros.

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

Definition live_sess (Mp:session) := forall M p q ell e P' Mr, betaRtc Mp M -> 
    (unfoldP M (p <-- p_send q ell e P' ||| Mr)) -> exists M', betaRtc M M' /\
    exists Mr', unfoldP M' ((p <-- P') ||| Mr').
