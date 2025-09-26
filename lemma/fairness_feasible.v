Require Import List String Coq.Arith.PeanoNat Coq.Program.Equality Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
From SST Require Import src.header src.sim src.expr src.process src.local 
src.global src.balanced src.typecheck src.part src.gttreeh src.path_props src.step src.merge src.projection src.session src.lcontext.  
From SST Require Import lemma.inversion lemma.path_assoc lemma.inversion_expr lemma.completeness lemma.substitution_helper lemma.substitution lemma.decidable_helper lemma.decidable lemma.expr lemma.part lemma.step 
lemma.projection_helper lemma.subj_red_prog_fid lemma.projection lemma.subj_red_helpers lemma.soundness 
lemma.liveness_helpers lemma.liveness lemma.live_proc.

Definition has_transition_left M := exists p q ell M', betaP_lbl M (lcomm p q ell) M'.

CoFixpoint repeat_list (og_list : list nat) (cur_ind :nat) :  coseq nat.
Proof.
    refine (match og_list with [] => conil | _ => _ end).
    destruct (List.nth_error (n::l) cur_ind) eqn:Hyg.
    {
        exact (cocons n  (repeat_list (n::l) (S cur_ind))).   
    }
    {
        exact (cocons n (repeat_list (n::l) 1)).   
    }
Defined.

Definition inf_part_list M := repeat_list (flattenT M) 0.


Lemma part_before_unf : forall M M' p,unfoldP M M' ->
InT p M' -> InT p M.
Proof.
    intros. generalize dependent p. induction H;intros;unfold InT in *;simpl;try easy.
    eapply IHunfoldP1; eapply IHunfoldP2;easy.
    simpl in H0. eapply in_swap;easy.
    simpl in H0.  rewrite <- app_assoc. easy.
    simpl in H0. eapply in_app_or in H0. eapply in_or_app. destruct H0;try tauto. left. eapply in_swap. easy.
    simpl in H0. repeat rewrite <- app_assoc. repeat rewrite <- app_assoc in H0. easy.
    rewrite app_nil_r. easy.
    simpl in H0. rewrite app_nil_r in H0. easy.
Qed.

Lemma betaP_lbl_means_part : forall M M' p q ell, betaP_lbl M (lcomm p q ell) M' -> 
InT p M /\ InT q M.
Proof.
    intros. 
    dependent induction H.
    unfold InT;simpl;tauto.
    specialize (IHbetaP_lbl p q ell eq_refl);destr_hyps.
    eapply part_before_unf in H as Ht;try exact H2.
    eapply part_before_unf in H as Ht';try exact H3. tauto.
Qed.

Lemma parts_stream_infinite_helper : forall M n, n < length (flattenT M) ->
alwaysCG (eventually (fun u=> u=repeat_list (flattenT M) n)) (inf_part_list M).
Proof.
    intros.
    induction (flattenT M) eqn:Hfm.
    {
        

        pcofix CIH. pfold.
        rewrite coseq_eq. simpl. rewrite Hfm. constructor. constructor. 
        rewrite coseq_eq. simpl. easy. left.
        pfold. rewrite coseq_eq. simpl.
        right. unfold inf_part_list in CIH.

    
Lemma parts_stream_infinite : forall M p, InT p M ->
alwaysCG (eventually (fun u=> match u with conil => False |  cocons a _ => a= p end)) (inf_part_list M).
Proof.
    intros.
    unfold inf_part_list. 
    destruct (flattenT M) eqn:Hfm.
    {
        red in H;rewrite Hfm in H. eapply in_nil in H;easy.   
    }
    red in H.
    pcofix CIH. pfold.
    rewrite coseq_eq. simpl. constructor.
      
Lemma trans_enable_coheres_stream : forall M  (Hnemp: flattenT M  <> []), has_transition_left M ->
eventually (fun u=> match u with cocons a b => 
    exists q ell M', betaP_lbl M (lcomm a q ell) M' \/
    betaP_lbl M (lcomm q a ell) M'
    | _ => False
    end) (inf_part_list M ).
Proof.
    intros.
    red in H. destr_hyps.
    eapply betaP_lbl_means_part in H as [Hp1 Hp2].
    set (parts_stream:=(inf_part_list M Hnemp)).
    assert(Hev:eventually (fun u=> 
        match u with conil => False | cocons a _ => a= x end) parts_stream ).
    {
        unfold parts_stream. unfold inf_part_list.
        unfold InT in *.
        pose proof Hnemp as Hnemp2.
        rewrite (coseq_eq (repeat_list _ _ _)). simpl.
        assert(exists p ps, flattenT M = p::ps ).
        destruct (flattenT M);try easy. 
    }
Definition get_first_available_trans (parts:coseq nat) M : 
    {z | match z with (M',p,q,ell) => 
    betaP_lbl M (lcomm p q ell) M' end}.
Proof.

    (*if trans involving p then do that else increase and go ahed*)
Admitted.

CoFixpoint fair_scheduler (part_queue : list nat) (M:session) : coseq (session * option label). 
Proof.
    destruct (excluded_middle_informative (has_transition_left M)).
    {
        admit.   
    }
    {
        exact (cocons (M, None) conil).   
    }

