(* From mathcomp Require Import ssreflect.seq all_ssreflect. *)
From Paco Require Import paco pacotac.
From SST Require Import src.expr src.header src.local CpdtTactics src.lcontext.
From SST Require Import src.global src.projection src.part  src.balanced src.merge src.wfltt src.gttreeh.
From SST Require Import lemma.projection lemma.projection_helper lemma.decidable lemma.correspond.
From SST Require Import src.step lemma.step src.assoc.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Init.Logic.
From Coq Require Import IndefiniteDescription.

Import ListNotations.

(*
Lemma lem_simul_assoc_inv: assoc gamma g ->
    M.find p gamma = Some (ltt_send q xsp) ->
    M.find q gamma = Some (ltt_recv p xsq) ->
    (exists gcs, g= gtt_send p q gcs) \/
    ()
*)

Section AssocCompletenessHelpers.
Variables (gamma: tctx) (g:gtt).
Hypothesis Hwfg : wfgC g.
Hypothesis Hassoc: assoc gamma g.

Lemma assoc_m : forall gamma', M.Equal gamma gamma' -> assoc gamma' g.
Proof.
    intros.
    unfold assoc in *.
    intros;split;intros;
    unfold assoc in Hassoc; specialize (Hassoc p) as Hap; 
    destruct Hap as [Hap0 Hap1];
    [
    apply Hap0 in H0;  destr_hyps;
    unfold M.Equal in H; specialize (H p); exists x
    | eapply Hap1 in H0 ];crush.
Qed.
Check Proper.


Ltac tac_use_assoc Hassoc p Hisparts := 
    let Ha1:=fresh "Hassoc" in let Ha2:=fresh "Hassoc" in 
    let Ha3:=fresh "Hassoc" in
    pose proof Hassoc as Ha3;
    unfold assoc in Ha3;
specialize (Ha3 p); 
    destruct Ha3 as [Ha1 Ha2];
    let Har:=fresh "Hassoc_u" in 
try (specialize (Ha1 Hisparts) as Har;clear Ha2 Ha1);try (specialize (Ha2 Hisparts) as Har;clear Ha1 Ha2).


Lemma assoc_weakening: forall p, (~ isgPartsC p g) 
    -> assoc (M.add p ltt_end gamma) g.
Proof.
    intros * Hparts.
    unfold assoc in *.
    intros.
    destruct (Nat.eq_dec p p0);subst.
    split;crush;autorewrite with mmaps in H0;crush.
    split.
    {
        specialize (Hassoc p0) as Hap0. destruct Hap0 as [Hap01 Hap02].
        intros. apply Hap01 in H. destruct H as [Tp H]. destr_hyps.
        exists Tp. split;autorewrite with mmaps;easy.   
    }
    {
        intros. specialize (Hassoc p0) as Hap0. destruct Hap0 as [Hap01 Hap02].
        eapply Hap02 in H. exact H. autorewrite with mmaps in H0. easy.   
    }
Qed.

Lemma assoc_context_not_in_global_not_in : forall p, M.find p gamma = None ->
    ~isgPartsC p g.
Proof.
    intros * Hisfind.
    destruct (decidable.decidable_isgPartsC g p);try easy.
    unfold assoc in Hassoc. specialize (Hassoc p) as Hap. destruct Hap as [Hap0 Hap1].
    apply Hap0 in H. destr_hyps. crush.
Qed.

Lemma assoc_remove_none : forall p, M.find p gamma= None ->
assoc (M.remove p gamma) g.
Proof.
    intros p Hnone.
    unfold assoc. intros. split;intros;destruct (Nat.eq_dec p0 p);subst.
    {
        unfold assoc in Hassoc. specialize (Hassoc p) as Hap. destruct Hap as [Hap0 Hap1].
        apply Hap0 in H. crush.
    }
    {
        unfold assoc in Hassoc. specialize (Hassoc p0) as Hap. destruct Hap as [Hap0 Hap1].
        apply Hap0 in H. destr_hyps.
        autorewrite with mmaps. exists x. easy.
    }
    {
        autorewrite with mmaps in H0;easy.   
    }
    {
        unfold assoc in Hassoc. specialize (Hassoc p0) as Hap. destruct Hap as [Hap0 Hap1].
        autorewrite with mmaps in H0.
        apply Hap1 with (Tpx:=Tpx) in H;easy.
    }
Qed.

Lemma assoc_remove_end : forall p, M.find p gamma= Some ltt_end ->
assoc (M.remove p gamma) g.
Proof.
    intros p Hnone.
    unfold assoc; split; intros; destruct (Nat.eq_dec p0 p);subst;try easy.
    {
        eapply assoc_inv_find with (g:=g) in Hnone;try easy.
        red in Hnone.
        destr_hyps.
        eapply subtype_end_inv2 in H1;subst.
        eapply pmergeCR_s in H0;easy.
    }
    {
        tac_use_assoc Hassoc p0 H. 
        autorewrite with mmaps. easy.
    }
    {
        tac_use_assoc Hassoc p H. autorewrite with mmaps in H0. crush.   
    }
    {
        tac_use_assoc Hassoc p0 H. autorewrite with mmaps in H0. crush.   
           
    }
Qed.

Lemma assoc_remove_not_part : forall p, ~isgPartsC p g ->
assoc (M.remove p gamma) g.
Proof.
    intros p Hpart.
    unfold assoc; split; intros; destruct (Nat.eq_dec p0 p);subst;try easy.
    {
        tac_use_assoc Hassoc p0 H. destr_hyps. exists x. autorewrite with mmaps. crush.
    }
    {
        autorewrite with mmaps in H0. easy.
    }
    {
        tac_use_assoc Hassoc p0 H. autorewrite with mmaps in H0. crush.   
    }
Qed.
End AssocCompletenessHelpers.

Instance EqMEQ {A: Type} : Equivalence ( @M.Equal A).
Proof. apply MF.Equal_equiv. Qed.

#[export] Instance ASSMEQ {A: Type}: Proper (M.Equal ==> eq ==> (iff)) assoc.
Proof. unfold "==>"; red; intros;subst; split;intros; [ | symmetry in H];

eapply assoc_m with (g:=y0) in H;try easy.
Qed.

Theorem assoc_completeness: forall p q ell gamma gamma' g, assoc gamma g ->
    wfgC g ->
    tctxR gamma (lcomm p q ell) gamma' ->
    exists g', assoc gamma' g' /\ gttstepC g g' p q ell.
Proof.
    intros * Hassoc Hwfg Hred.
    dependent induction Hred.
    {
        clear IHHred1 IHHred2.
        rename H1 into Hdisj1, H2 into Hdisj2.
        admit.
    }
    {   
        rename g0 into gamma, g' into gamma'.
        destruct T.
        
        rewrite MF.not_mem_find in H.
        (*t must be ltt end*)
        {
            assert (Hassoc_gamma: assoc gamma g).
            {
                eapply assoc_remove_end with (p:=p0) in Hassoc;try (autorewrite with mmaps;easy).
                (*follows by setoid rewrite*)
                admit.   
            }
            eapply assoc_remove_end with (p:=p0)in Hassoc;try (autorewrite with mmaps;easy).
            
            eapply assoc_context_not_in_global_not_in with (g:=g) in H;try easy.
            pose proof Hwfg.
            eapply IHHred with (p:=p) (q:=q) (ell:=ell) in H0;try easy.
            destr_hyps.
            exists x.
            split;try easy.
            eapply assoc_weakening;try easy.
            
            eapply not_part_step with (g:=g) (p:=p) (q:=q) (k:=ell);try easy.
            eapply assoc_implies_projectable with (gamma:=gamma);try easy.
        }
        {
            
        }
        exists g0.
        admit.
    }