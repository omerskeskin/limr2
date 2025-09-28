Require Import List String Coq.Arith.PeanoNat Coq.Program.Equality Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
Require Import Coq.Init.Wf.
From SST Require Import src.header src.sim src.expr src.process src.local 
src.global src.balanced src.typecheck src.part src.gttreeh src.path_props src.step src.merge src.projection src.session src.lcontext.  
From SST Require Import lemma.inversion lemma.path_assoc lemma.inversion_expr lemma.completeness lemma.substitution_helper lemma.substitution lemma.decidable_helper lemma.decidable lemma.expr lemma.part lemma.step 
lemma.projection_helper lemma.subj_red_prog_fid lemma.projection lemma.subj_red_helpers lemma.soundness 
lemma.liveness_helpers lemma.liveness lemma.live_proc.

From Coq Require Import ClassicalDescription.
From Coq Require Import IndefiniteDescription.

Definition has_transition_left M := exists p q ell M', betaP_lbl M (lcomm p q ell) M'.

CoFixpoint repeat_list (og_list n_list: list nat)  := 
    match og_list with [] => conil 
        | (n::l) => match n_list with [] => cocons n (repeat_list og_list l) 
            | (n'::l') => cocons n' (repeat_list og_list l') end end. 

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

Fixpoint stream_concat_finite (xs:list nat) (c:coseq nat):=
    match xs with | [] => c | (x::xs) => cocons x (stream_concat_finite xs c) end. 

Lemma repeat_list_spec : forall xs ys, xs <> [] -> repeat_list xs ys = stream_concat_finite ys  (repeat_list xs xs).
Proof.
    destruct xs;try easy.
    induction ys;intros. simpl. rewrite coseq_eq. simpl. rewrite coseq_eq at 1. simpl. easy. 
    specialize (IHys  H).
    rewrite coseq_eq at 1. simpl. rewrite coseq_eq. simpl.
    rewrite IHys. easy.
Qed.

Lemma stream_concat_app : forall xs ys c, 
    stream_concat_finite xs (stream_concat_finite ys c)=
    stream_concat_finite (xs++ys) c.
Proof.
    induction xs;intros. reflexivity.
    simpl. rewrite IHxs. easy.
Qed.

Lemma repeat_list_spec_2 : forall xs ys, xs <> [] -> repeat_list xs ys = stream_concat_finite (ys++xs) (repeat_list xs xs).
Proof.
    destruct xs;try easy.
    intros.
    rewrite repeat_list_spec;try easy.
    rewrite repeat_list_spec at 1;try easy.
    rewrite stream_concat_app. easy.
Qed.

Definition inf_part_list M := repeat_list (flattenT M) (flattenT M).

Fixpoint list_to_stream (xs:list nat) := match xs with [] => conil | (x::xs) => cocons x (list_to_stream xs) end. 

Definition is_stream_head (p:nat) c := match c with conil => False | cocons x xs => p = x end.

Definition in_stream p  := eventually (is_stream_head p).

Lemma in_pref_implies_in_stream : forall p xs c, In p xs -> in_stream p (stream_concat_finite xs c).
Proof.
    intros. generalize dependent H. induction xs;intros. inversion H.
    inversion H;subst. red;constructor. red. easy.
     constructor 2. specialize (IHxs H0).
     red in IHxs. easy.
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

Lemma infite_stream_in_helper : forall xs ys p, In p xs ->
in_stream p (repeat_list xs ys).
Proof.
    intros. destruct xs. inversion H. rewrite repeat_list_spec_2;try easy.
    eapply in_pref_implies_in_stream. eapply in_or_app;tauto.
Qed.

Lemma infinite_stream_always_in : forall xs ys p, In p xs ->
alwaysCG (in_stream p) (repeat_list xs ys).
Proof.
    intros. destruct xs. inversion H.
    generalize dependent ys.
    pcofix CIH.
    intros. pfold.
    rewrite repeat_list_spec_2;try easy.
    destruct ys.
    {
        rewrite app_nil_l.
        assert(in_stream p (stream_concat_finite (n :: xs) (repeat_list (n :: xs) (n :: xs)))).
        eapply in_pref_implies_in_stream;try easy.
        simpl. constructor. simpl in H0. easy.    
        right.
        rewrite <- repeat_list_spec;try easy.
    }
    simpl.
    constructor.
    assert(in_stream p (stream_concat_finite (n :: xs) (repeat_list (n :: xs) (n :: xs)))).
        eapply in_pref_implies_in_stream;try easy.
        change (cocons n0
            (stream_concat_finite (ys ++ n :: xs)
            (repeat_list (n :: xs) (n :: xs)))) with 
(stream_concat_finite (n0::ys ++ n::xs) (repeat_list (n :: xs) (n :: xs))).
        eapply in_pref_implies_in_stream.
        rewrite app_comm_cons. eapply in_or_app;tauto.
        right.
        rewrite <-repeat_list_spec;try easy.
Qed.


Lemma parts_stream_infinite_in : forall M p, InT p M ->
alwaysCG (in_stream p) 
(inf_part_list M).
Proof.
    intros.
    red in H. eapply infinite_stream_always_in;easy.
Qed.

Definition is_part_stream M xs := forall p, InT p M -> alwaysCG (in_stream p) xs.

Definition no_trans_involving p M := forall q ell M', 
(~betaP_lbl M (lcomm p q ell) M' /\ ~ betaP_lbl M (lcomm q p ell) M').

Definition trans_involving p M := exists q ell M', 
(betaP_lbl M (lcomm p q ell) M' \/ betaP_lbl M (lcomm q p ell) M').

Definition to_coseq_prop {A:Type} (P:A -> Prop) := fun u=> match u with conil => False | cocons x xs => P x end.

Lemma ev_expansion {A:Type}: forall P (x:A) xs, eventually P (cocons x xs) -> 
    P (cocons x xs) \/ eventually P xs.
Proof.
    intros. dependent induction H;try tauto.
Qed.

Lemma ev_expansion_sig {A:Type}: forall P (x:A) xs, eventually P (cocons x xs) -> 
    {P (cocons x xs)} + {eventually P xs}.
Proof.
    intros. eapply ev_expansion in H. 
    destruct (excluded_middle_informative (P (cocons x xs)));
    destruct (excluded_middle_informative (eventually P xs)). right. exact e.
    left. exact p. right. exact e.
    tauto.
Qed.

Lemma get_first_P_stream P (xs:coseq nat) (Hinv: eventually (to_coseq_prop P) xs) :
    exists c, is_suffix c xs /\ to_coseq_prop P c.
Proof.
    induction Hinv.
    exists xs;split;try easy;constructor.
    destr_hyps.
    exists x0. split;try easy. constructor. easy.
Qed.

Lemma transition_eventually_in_stream : forall M xs,
has_transition_left M -> 
is_part_stream M xs ->
eventually (to_coseq_prop (fun p =>  trans_involving p M)) xs.
Proof.
    intros.
    red in H. destr_hyps. eapply betaP_lbl_means_part in H as Hpt.
    destruct Hpt as [?Hpt ?Hpt].
    red in H0. specialize (H0 _ Hpt).
    pinversion H0;subst. inversion H1;subst. simpl in H2. easy.

    red in H1.
    rewrite eventually_P_iff_P_suffix in H1. destr_hyps.
    rewrite eventually_P_iff_P_suffix. exists x4. split;try easy. 
    destruct x4;try easy.
    simpl. simpl in H3;subst. red. exists x0, x1, x2. tauto.
Qed.

Lemma or_to_plus : forall P P', P \/ P' -> {P} + {P'}.
Proof.
    intros.
    destruct (excluded_middle_informative P);
    destruct (excluded_middle_informative P');try (right;easy).
    left. easy. tauto.
Qed.

Lemma is_part_stream_suf : forall M xs ys, 
    is_suffix xs ys -> is_part_stream M ys -> is_part_stream M xs.
Proof.
    red;intros. 
    eapply always_suffix;try exact H. red in H0. eapply H0;try easy.
Qed.


Ltac indef_destruct H := let tth := type of H in match tth with 
     | ex _  => let nx := fresh "x" in let nh:= fresh "H" in  
    destruct (constructive_indefinite_description _ H) as [nx nh];try indef_destruct nh;clear H end.

Definition get_first_available_trans (parts:coseq nat) M  (Hpn : is_part_stream M parts): 
    has_transition_left M ->
    parts <> conil ->
    {z | match z with (M',p,q,ell,cd) => 
    (*encode the *first* condition here*)
    betaP_lbl M (lcomm p q ell) M' /\ is_part_stream M cd end}.
Proof.
    destruct parts;intros;try easy.
    eapply transition_eventually_in_stream in H as Hin1;try exact Hpn.
    eapply get_first_P_stream in Hin1.
    indef_destruct Hin1. destr_hyps.
    destruct x;simpl in H2;try easy. red in H2.
    indef_destruct H2.
    eapply or_to_plus in H5. destruct H5.
    exists (x2,n0, x0,x1,cocons n0 x). split;try easy. eapply is_part_stream_suf;try exact H1;try easy.
    exists (x2,x0, n0,x1,cocons n0 x). split;try easy. eapply is_part_stream_suf;try exact H1;try easy.
Qed.

(*
Lemma trans_enable_coheres_stream : forall M , has_transition_left M ->
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
*)

Lemma part_after_beta : forall M p q ell M' r, betaP_lbl M (lcomm p q ell) M' -> 
    InT r M ->
    InT r M'.
Proof.
    intros. dependent induction H.
    red in H1. red. easy.
    eapply part_after_unf in H;try exact H2.
    eapply IHbetaP_lbl in H;try reflexivity. 
    eapply part_after_unf;try exact H;try easy. 
Qed.

Lemma part_before_beta : forall M p q ell M' r, betaP_lbl M (lcomm p q ell) M' -> 
    InT r M' ->
    InT r M.
Proof.
    intros. dependent induction H.
    red in H1. red. easy.
    eapply part_before_unf in H0;try exact H2.
    eapply IHbetaP_lbl in H0;try reflexivity. 
    eapply part_before_unf;try exact H;try easy. 
Qed.

CoFixpoint fair_scheduler parts (M:session) (Hpartst: is_part_stream M parts): coseq (session * option label). 
Proof.
    destruct (excluded_middle_informative (has_transition_left M)).
    {
        eapply get_first_available_trans in h as htr;try exact Hpartst.
        destruct htr.
        destruct x as [[[[M' p]  q]ell] cd].
        destr_hyps. 
        assert(Hpa2: is_part_stream M' cd).
        {
            red;intros.
            red in H0. eapply part_before_beta in H;try exact H1.
            eapply H0 in H. easy.
        }
        exact (cocons (M,Some (lcomm p q ell)) (fair_scheduler cd M' Hpa2)).
        red in h. destr_hyps. eapply betaP_lbl_means_part in H. destr_hyps.
        red in Hpartst. eapply Hpartst in H.
        destruct parts;try easy. pinversion H. red in H1. inversion H1;subst.
        simpl in H2. easy.         
    }
    {
        exact (cocons (M, None) conil).   
    }
Defined.

Lemma inf_parts_is_parts_stream : forall M, is_part_stream M (inf_part_list M).
Proof.
    intros;red;intros. eapply parts_stream_infinite_in in H. easy.
Qed.


Lemma fair_scheduler_valid : forall M, 
    proc_valid_pathC (fair_scheduler (inf_part_list M) M (inf_parts_is_parts_stream M)).
Proof.
    pcofix CIH. intros.
    pfold.    
    
        rewrite coseq_eq. simpl.
    destruct (excluded_middle_informative (has_transition_left M)).
    {
        assert(exists pt ps, flattenT M = pt ::ps).
        {
            destruct (flattenT M) eqn:Ht. red in h. destr_hyps. eapply betaP_lbl_means_part in H;destr_hyps.
            red in H. rewrite Ht in H. inversion H.
            exists n,l. easy. 
        }
        
        destr_hyps. 
        
        red in h. destr_hyps. simpl.
        rewrite -> H.
        destruct (betaP_lbl_means_part M x4 x1 x2 x3 b).
        simpl.
        rewrite -> H.
    }
    constructor.

Lemma fair_scheduler_fair : forall M, 
    fair_path_proc (fair_scheduler (inf_part_list M) M (inf_parts_is_parts_stream M)).

