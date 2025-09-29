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



Definition trans_involving_strong p M:= sum {z | 
        match z with (q, ell, M') =>
        betaP_lbl M (lcomm p q ell) M' end}
        {z | 
        match z with (q, ell, M') =>
        betaP_lbl M (lcomm q p ell) M' end}
        .

Lemma transes_neg : forall p M, no_trans_involving p M <-> ~ trans_involving p M.
Proof.
    split;intros.
    red in H. red;intros. red in H0. destr_hyps.
    specialize (H x x0 x1). tauto.
    
    red. intros. red in H. unfold trans_involving in H.
    split;red;intros; eapply H. exists q, ell, M'. tauto.
    exists q, ell, M'. tauto.
Qed.

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
    exists c, is_suffix c xs /\ until (to_coseq_prop (fun x=> ~ P x)) 
    (fun u=> u=c) xs /\
    to_coseq_prop P c.
Proof.
    induction Hinv.
    exists xs;split;try easy. constructor. constructor; try easy. constructor. easy.

    destr_hyps.
    destruct (classic (P x)).
    {
        exists (cocons x xs). split;try easy.
        constructor. constructor; try easy. constructor. easy.   
    }
    exists x0. split;try easy. constructor 2. easy.
    constructor. constructor 2. easy.
    easy. easy.
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

Lemma until_proper_props {A:Type}: forall (P: coseq A -> Prop) P' Q Q', (forall x, P x <-> P' x) ->
(forall x, Q x <-> Q' x) -> forall xs, (until P Q xs) <-> (until P' Q' xs).
Proof.
    intros * Hex1 Hex2.
    split;intros;induction H. constructor. rewrite <- Hex2. easy.
    constructor 2. rewrite <- Hex1. easy. easy.
    constructor. rewrite Hex2. easy. constructor 2. rewrite Hex1. easy. easy.
Qed.

Ltac indef_destruct H := let tth := type of H in match tth with 
     | ex _  => let nx := fresh "x" in let nh:= fresh "H" in  
    destruct (constructive_indefinite_description _ H) as [nx nh];try indef_destruct nh;clear H end.

Lemma until_to_eventually {A:Type}: forall  Q P (xs : coseq A), 
    until Q P xs -> eventually P xs.
Proof.
    intros.
    induction H. constructor;easy.
    constructor 2. easy.
Qed.

Lemma ev_equals_suf {A:Type}: forall (xs ys : coseq A), eventually (fun u=> u= ys) xs -> is_suffix ys xs.
Proof.
    intros.
    induction H;subst. constructor. constructor 2. easy.
Qed.

Definition get_first_available_trans (parts:coseq nat) M  (Hpn : is_part_stream M parts): 
    has_transition_left M ->
    parts <> conil ->
    {cd | until (fun u=> 
            match u with cocons x xs => no_trans_involving x M 
            | conil => False end
            ) (fun u=> match u with cocons x xs => trans_involving x M /\ cd = cocons x xs 
                | conil=>False end) 
            parts /\ 
            (match cd with cocons x xs => trans_involving x M | _ => False end)
            /\ is_suffix cd parts
            }.
Proof.
    destruct parts;intros;try easy.
    eapply transition_eventually_in_stream in H as Hin1;try exact Hpn.
    eapply get_first_P_stream in Hin1.
    indef_destruct Hin1. destr_hyps.
    destruct x;simpl in H2;try easy. simpl in H3. red in H3.
    indef_destruct H3.
    eapply or_to_plus in H6; destruct H6;
    exists (cocons n0 x);split;try split;
    try solve 
    [
        eapply until_proper_props;try exact H2;
        intros; destruct x3; simpl;try  easy;
        try solve [eapply transes_neg];
        split;intros;destr_hyps; 
        [ inversion H4;subst;try easy |
        inversion H3;subst; split;try easy; red; exists x0, x1, x2; tauto]
    | exists x0,x1,x2;tauto
    | eapply ev_equals_suf;eapply until_to_eventually;try exact H2].
Qed.


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

Lemma has_transition_left_means_parts_some : forall M parts, has_transition_left M -> is_part_stream M parts ->
    parts <> conil.
Proof.
    intros.
    red in H. destr_hyps. eapply betaP_lbl_means_part in H. destr_hyps.
        red in H0. eapply H0 in H.
        destruct parts;try easy. pinversion H. red in H2.  inversion H2;subst.
        simpl in H3. easy.
Qed.

CoFixpoint fair_scheduler parts (M:session) (Hpartst: is_part_stream M parts): coseq (session * option label). 
Proof.
    destruct (excluded_middle_informative (has_transition_left M)).
    {
        eapply get_first_available_trans in h as htr;try exact Hpartst;
        try solve [eapply has_transition_left_means_parts_some in Hpartst;try easy].
        destruct htr.
        destruct x;try easy.
        destruct a. destr_hyps.
        red in H0.  indef_destruct H0.
        eapply or_to_plus in H4. destruct H4.
        assert(Hpa2: is_part_stream x2 x).
        {
            red;intros.
            red in H0. eapply part_before_beta in b;try exact H0.
            eapply suffix_tail in H1.
            eapply always_suffix;try exact H1. eapply Hpartst;easy.
        }
        exact (cocons (M,Some (lcomm n x0 x1)) (fair_scheduler x x2 Hpa2)).

        assert(Hpa2: is_part_stream x2 x).
        {
            red;intros.
            red in H0. eapply part_before_beta in b;try exact H0.
            eapply suffix_tail in H1.
            eapply always_suffix;try exact H1. eapply Hpartst;easy.
        }
        exact (cocons (M,Some (lcomm x0 n x1)) (fair_scheduler x x2 Hpa2)).

    }
    {
        exact (cocons (M, None) conil).   
    }
Defined.

Lemma inf_parts_is_parts_stream : forall M, is_part_stream M (inf_part_list M).
Proof.
    intros;red;intros. eapply parts_stream_infinite_in in H. easy.
Qed.


Lemma fair_scheduler_head: forall M xs Ht, exists l tl,
    fair_scheduler xs M Ht = cocons (M,l) tl.
Proof.
    intros.  rewrite (coseq_eq (fair_scheduler xs M Ht)).
    simpl.
    destruct(excluded_middle_informative (has_transition_left M)).
    destruct (get_first_available_trans xs M Ht h
(has_transition_left_means_parts_some M xs h Ht)). destruct x;try easy.
    destruct a. destruct a. 
    destruct (constructive_indefinite_description
(fun q : opt_lbl =>
exists (ell : opt_lbl) (M' : session),
betaP_lbl M (lcomm n q ell) M' \/
betaP_lbl M (lcomm q n ell) M') t).
    destruct (constructive_indefinite_description
(fun ell : opt_lbl =>
exists M' : session,
betaP_lbl M (lcomm n x0 ell) M' \/
betaP_lbl M (lcomm x0 n ell) M') e).
    destruct (constructive_indefinite_description
(betaP_lbl M (lcomm n x0 x1) \1/ betaP_lbl M (lcomm x0 n
x1)) e0).
    destruct (or_to_plus (betaP_lbl M (lcomm n x0 x1) x2)
(betaP_lbl M (lcomm x0 n x1) x2) o).
    simpl. exists (Some (lcomm n x0 x1)), (fair_scheduler x x2
(fun (p : opt_lbl) (H : InT p x2) =>
always_suffix (in_stream p) x xs
(Ht p (part_before_beta M n x0 x1 x2 p b H))
(suffix_tail n xs x i))). easy.
    simpl. exists (Some (lcomm x0 n x1)), (fair_scheduler x x2
(fun (p : opt_lbl) (H : InT p x2) =>
always_suffix (in_stream p) x xs
(Ht p (part_before_beta M x0 n x1 x2 p b H))
(suffix_tail n xs x i))). easy.
    exists None, conil. easy.
Qed.

Lemma fair_scheduler_valid : forall M (Htyp: typable M) inf_pl Hstream_parts, 
    proc_valid_pathC (fair_scheduler inf_pl M (Hstream_parts)).
Proof.
    pcofix CIH. intros.
    pfold.    
    
        rewrite coseq_eq. simpl.
    destruct (excluded_middle_informative (has_transition_left M)).
    {
        destruct (get_first_available_trans inf_pl M Hstream_parts h
            (has_transition_left_means_parts_some M inf_pl
            h Hstream_parts)).
        destruct x;try easy. 
        destruct a;try easy.
        destruct a;try easy.
        destruct (constructive_indefinite_description
        (fun q : opt_lbl =>
        exists (ell : opt_lbl) (M' : session),
        betaP_lbl M (lcomm n q ell) M' \/
        betaP_lbl M (lcomm q n ell) M') t).
        destruct (constructive_indefinite_description
        (fun ell : opt_lbl =>
        exists M' : session,
        betaP_lbl M (lcomm n x0 ell) M' \/
        betaP_lbl M (lcomm x0 n ell) M') e).
        destruct (constructive_indefinite_description
        (betaP_lbl M (lcomm n x0 x1) \1/ betaP_lbl M (lcomm x0 n
        x1)) e0).
        destruct (or_to_plus (betaP_lbl M (lcomm n x0 x1) x2)
        (betaP_lbl M (lcomm x0 n x1) x2) o).
        (*p1*)
        specialize fair_scheduler_head with (M:=x2) (xs:=x) (Ht:= (fun (p : opt_lbl) (H : InT p x2) =>
        always_suffix (in_stream p) x inf_pl
        (Hstream_parts p (part_before_beta M n x0 x1 x2 p b H))
        (suffix_tail n inf_pl x i))) as fsd.
        destr_hyps.
        rewrite H. constructor. 
        {
            right. rewrite <- H. eapply CIH.
            red in Htyp. 
            destr_hyps. eapply sub_red_strong_labelled in b as hbt;try exact H2. destr_hyps.
            exists x9. easy.
        }
        {
            red. split;try easy.
        }    
        specialize fair_scheduler_head with (M:=x2) (xs:=x) (Ht:= (fun (p : opt_lbl) (H : InT p x2) =>
        always_suffix (in_stream p) x inf_pl
        (Hstream_parts p (part_before_beta M x0 n x1 x2 p b H))
        (suffix_tail n inf_pl x i))) as fsd.
        destr_hyps.
        rewrite H. constructor. 
        {
            right. rewrite <- H. eapply CIH.
            red in Htyp. 
            destr_hyps. eapply sub_red_strong_labelled in b as hbt;try exact H2. destr_hyps.
            exists x9. easy.
        }
        {
            red. split;try easy.
        }
    }    
    {
        constructor.   
    }
Qed.

Fixpoint stream_nth {A:Type} n (xs:coseq A) := 
    match xs with conil => None |
    cocons x xs => match n with 0 => Some x
                    | S y => stream_nth y xs end
                end.
     


Definition distance_to_p : forall p M xs, InT p M -> is_part_stream M xs ->
    exists n, stream_nth n xs = Some p /\ until 
        (fun u=>match u with cocons x xs => x <> p | _ => False end)
        (fun u=>match u with cocons x xs => x = p | _ => False end)
        xs.
Proof.
    intros * Hinm Hstream. red in Hstream. 
    eapply Hstream in Hinm.
    assert(Hinst: in_stream p xs). 
    {
        pinversion Hinm;subst;red in H. 
        inversion H;subst. simpl in H0. easy. easy.
    }
    red in Hinst. induction Hinst.
    {
        destruct xs;try easy.
        red in H;subst. exists 0. split;try easy. constructor 1. easy.   
    }
    {
        destruct (Nat.eq_dec x p);subst.
        exists 0. split;simpl;try easy. constructor. easy.
        
        pinversion Hinm;subst. eapply IHHinst in H2. destr_hyps.
        exists (S x0).
        split. simpl. easy. constructor 2;try easy.
        intros.
        eapply Hstream in H. pinversion H;subst;easy.
    }
Qed.



Lemma fair_scheduler_fair : forall M (Htyp:typable M) inf_pl Hplt, 
    fair_path_proc (fair_scheduler inf_pl M Hplt).
Proof.
    pcofix CIH.
    intros. 
    pfold.  
