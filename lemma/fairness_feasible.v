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
From Coq Require Import Lia.

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
(~betaP_lbl M (lcomm p q ell) M').

Definition trans_involving p M := exists q ell M', 
(betaP_lbl M (lcomm p q ell) M').


Lemma transes_neg : forall p M, no_trans_involving p M <-> ~ trans_involving p M.
Proof.
    split;intros.
    red in H. red;intros. red in H0. destr_hyps.
    specialize (H x x0 x1). tauto.
    
    red. intros. red in H. unfold trans_involving in H.

    red;intros; eapply H. exists q, ell, M'. tauto.
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
        assert(Hpa2: is_part_stream x2 x).
        {
            red;intros.
            red in H0. eapply part_before_beta in H4;try exact H0.
            eapply suffix_tail in H1.
            eapply always_suffix;try exact H1. eapply Hpartst;easy.
        }
        exact (cocons (M,Some (lcomm n x0 x1)) (fair_scheduler x x2 Hpa2)).
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
    betaP_lbl M (lcomm n q ell) M') t).
    destruct (constructive_indefinite_description
    (fun ell : opt_lbl =>
    exists M' : session, betaP_lbl M (lcomm n x0 ell) M') e).
    destruct (constructive_indefinite_description (betaP_lbl M
    (lcomm n x0 x1)) e0).
    exists (Some (lcomm n x0 x1)), (fair_scheduler x x2
    (fun (p : opt_lbl) (H : InT p x2) =>
    always_suffix (in_stream p) x xs
    (Ht p (part_before_beta M n x0 x1 x2 p b H))
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
        betaP_lbl M (lcomm n q ell) M') t).
        destruct (constructive_indefinite_description
        (fun ell : opt_lbl =>
        exists M' : session,
        betaP_lbl M (lcomm n x0 ell) M') e).
        destruct (constructive_indefinite_description
        (betaP_lbl M (lcomm n x0 x1)) e0).
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
    }    
    {
        constructor.   
    }
Qed.

Fixpoint stream_nth {A:Type} n (xs:coseq A) := 
    match xs with conil => None |
    cocons x xs => match n with 0 => Some (cocons  x xs)
                    | S y => stream_nth y xs end
                end.
     

                
Definition until_indexed {A:Type} P Q n (xs : coseq A) := Q (stream_nth n xs) /\ forall i, i < n -> P (stream_nth i xs).

Definition distance_to_p : forall p M xs, InT p M -> is_part_stream M xs ->
    exists n, until_indexed 
        (fun u=>match u with Some (cocons x xs) => x <> p | _ => False end)
        (fun u=>match u with Some (cocons x xs)  => x = p | _ => False end)
        n
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
        red in H;subst. exists 0. split;try easy.    
    }
    {
        destruct (Nat.eq_dec x p);subst.
        exists 0. split;simpl;try easy.
        
        pinversion Hinm;subst. eapply IHHinst in H2. destr_hyps.
        exists (S x0). red in H. destr_hyps. 
        split;try easy. intros. destruct i; simpl;try easy.
        eapply H0;lia. 
        
        intros.
        eapply Hstream in H. pinversion H;subst;easy.
    }
Qed.


(*
Definition distance_to_p_comp : forall p M xs, InT p M -> is_part_stream M xs ->
    {n | stream_nth n xs = Some p /\ until 
        (fun u=>match u with cocons x xs => x <> p | _ => False end)
        (fun u=>match u with cocons x xs => x = p | _ => False end)
        xs}.
Proof.
    intros. eapply distance_to_p in H0;try easy;try exact H. 
    indef_destruct H0. exists x. easy.
Qed.*)

Lemma betaP_lbl_trans_enabled_after_distinct : forall M gamma Mpq Mst p q ell ell' s t,
    typ_sess M gamma -> p <> s -> q <> t ->  betaP_lbl M (lcomm p q ell) Mpq -> 
    betaP_lbl M (lcomm s t ell') Mst -> exists M' ell'', 
    betaP_lbl Mst (lcomm p q ell'') M'.
Proof.
    intros * Htyp Hps Hqt  Hbetpq Hbetst.
    assert(Hpt:  p <> t).
    {
        eapply sub_red_strong_labelled in Hbetpq as Hsubpq;try exact Htyp.
        eapply sub_red_strong_labelled in Hbetst as Hsubst;try exact Htyp.
        
        destruct Hsubpq as [gamma_pq [Hsesspq Htcpq]].
        destruct Hsubst as [gamma_st [Hsessst Htcst]].
        destruct (Nat.eq_dec p t);try easy;subst.
        eapply tctx_comm_invert in Htcpq, Htcst. destr_hyps.
        congruence.         
    }
    assert(Hqs: q <> s).
    {
        eapply sub_red_strong_labelled in Hbetpq as Hsubpq;try exact Htyp.
        eapply sub_red_strong_labelled in Hbetst as Hsubst;try exact Htyp.
        
        destruct Hsubpq as [gamma_pq [Hsesspq Htcpq]].
        destruct Hsubst as [gamma_st [Hsessst Htcst]].
        destruct (Nat.eq_dec q s);try easy;subst.
        eapply tctx_comm_invert in Htcpq, Htcst. destr_hyps.
        congruence. 
    }
    eapply sub_red_strong_labelled in Hbetpq as Hsubpq;try exact Htyp.
    eapply sub_red_strong_labelled in Hbetst as Hsubst;try exact Htyp.
    
    destruct Hsubpq as [gamma_pq [Hsesspq Htcpq]].
    destruct Hsubst as [gamma_st [Hsessst Htcst]].
    pose proof Htcpq as Hctpq'.
    pose proof Htcst as Htcst'.
    eapply tctx_comm_invert in Htcpq, Htcst.
    destr_hyps.
    assert(exists ellt gamma', tctxR gamma_st (lcomm p q ellt) gamma').
    {
        eapply red_relevance with (r:=p) in Htcst' as Hredr1;
        eapply red_relevance with (r:=q) in Htcst' as Hredr2;
         try solve [red;intros Hfl;destruct Hfl;subst;easy].
         evar (ellt : opt_lbl). evar (gamma':tctx).
         exists ellt, gamma'. 
        eapply simple_red_comm with (xp:=x7) (xq:=x9);try exact H11;try exact H9;try congruence.   
    }
    destr_hyps.
    eapply sess_fidelity in H13;try exact Hsessst. destr_hyps. exists x14, x15.
    easy.
Qed.

Lemma until_mono {A:Type}: forall P P' Q Q' (xs:coseq A), 
    (forall a, P a -> P' a) -> (forall a, Q a -> Q' a) ->
    until P Q xs -> until P' Q' xs.
Proof.
    intros. induction H1. constructor. eapply H0;easy.
    constructor 2. eapply H;easy. easy.
Qed.  

Lemma stream_nth_conil {A:Type}: forall m, stream_nth m (conil: coseq A) = None.
Proof.
    intros.
    simpl.
    destruct m;simpl;easy.
Qed.

Lemma until_to_until_indexed {A:Type}: forall P Q (xs : coseq A), 
    until P Q xs -> 
    ~ Q conil ->
    exists n',
    until_indexed
    (fun u=> match u with Some r => P r | _ => False end) 
    (fun u=>match u with Some r => Q r | _ => False end) n' xs.
Proof.
    intros * H Hqc.
    induction H. exists 0. red;split;simpl;intros;try lia. 
    destruct xs;try easy.
    destr_hyps.
    destruct (classic (Q (cocons x xs))).
    exists 0. split;simpl;try easy.
    exists (S x0).
    unfold until_indexed in *;destr_hyps.
    split. simpl. easy. intros.
    destruct i. simpl. easy.
    simpl. eapply H3. lia.
Qed.

Lemma stream_nth_sum : forall n m (xs : coseq nat), stream_nth m 
    ((fun u=> match u with Some x => x | _ => conil end)(stream_nth n xs)) = stream_nth (m+n) xs.
Proof.
    induction n;intros.
    assert(m+0=m) by  lia.
    destruct xs;simpl;try congruence.

    destruct xs. simpl. repeat rewrite stream_nth_conil. easy.
    rewrite <- plus_n_Sm.
    simpl.
    eapply IHn.
Qed.


Lemma suffix_index_lift : forall n xs sh ss, ((fun u : option (coseq opt_lbl) =>
    match u with
    | Some r => r = cocons sh ss
    | None => False
    end)) (stream_nth n xs) ->  
    forall m, stream_nth (n+m) xs = stream_nth m (cocons sh ss).
Proof.
    intros * Hsuf *.
    simpl in Hsuf.
    rewrite Nat.add_comm.
    rewrite <- stream_nth_sum.
    destruct (stream_nth n xs) eqn:Hyg;simpl. subst;easy.
    easy.
Qed.

 Lemma until_progress {A:Type}: forall P (xs : coseq A) h tl, until P (fun u=> u= cocons h tl) xs ->
                        P (cocons h tl) -> until P (fun u=>u=tl) xs.
                        Proof.
                            intros * Hun Hph.
                            induction Hun;subst. constructor 2;try easy. constructor 1. easy.
                            constructor 2;try easy.
                        Qed.    


Lemma fair_scheduler_fair_helper : forall p q ell M M' (Htyp:typable M) inf_pl Hplt,
    betaP_lbl M (lcomm p q ell) M' -> exists ell', eventually 
    (head_trans_proc p q ell') 
    (fair_scheduler inf_pl M Hplt).
Proof.
    intros * Htyp * Htrans.
    assert(Hinp : InT p M). eapply betaP_lbl_means_part in Htrans;tauto.
    eapply distance_to_p in Hinp as Hdist;try exact Hplt.
    destruct Hdist as [n Hdist].
    generalize dependent inf_pl.
    generalize dependent M'.
    
    generalize dependent M.
    revert p q ell.
    induction n  as [n IH] using (lt_wf_ind).
    {
        destruct n.
        {
            intros.
            rewrite (coseq_eq (fair_scheduler _  _ _)). simpl.  
            destruct (excluded_middle_informative (has_transition_left M)). 
            destruct (get_first_available_trans inf_pl M Hplt h (has_transition_left_means_parts_some M inf_pl h Hplt)).
            destruct x;try easy.
            destruct a;destruct a;try easy.
            
            destruct (constructive_indefinite_description
            (fun q0 : opt_lbl =>
            exists (ell0 : opt_lbl) (M'0 : session),
            betaP_lbl M (lcomm n q0 ell0) M'0) t).
            destruct (constructive_indefinite_description
            (fun ell0 : opt_lbl =>
            exists M'0 : session, betaP_lbl M (lcomm n x0 ell0)
            M'0) e).
            destruct (constructive_indefinite_description
            (betaP_lbl M (lcomm n x0 x1)) e0). 
            destruct u. 
            {
                destruct xs;try easy.
                destr_hyps. inversion H2;subst. 
                assert(Hnp: n0=p). red in Hdist;destr_hyps. simpl in H3;easy.
                subst.
                destruct Htyp as [gamma Htyp].
                eapply betaP_lbl_send_unique in b as Hbt ;try exact Htrans;try exact Htyp;subst.
                exists x1. constructor. simpl. tauto.
            }
            {
                destr_hyps. red in Hdist;destr_hyps. simpl in H2;subst.
                red in H. eapply H in Htrans. easy.   
            }
            exfalso;eapply n. red. exists p,q,ell,M'. easy.
        }
        {
            intros.
             rewrite (coseq_eq (fair_scheduler _  _ _)). simpl.  
            destruct (excluded_middle_informative (has_transition_left M)). 
            {
                destruct (get_first_available_trans inf_pl M Hplt h (has_transition_left_means_parts_some M inf_pl h Hplt)).
                destruct x;try easy.
                destruct a;destruct a;try easy.
                
                destruct (constructive_indefinite_description
                (fun q0 : opt_lbl =>
                exists (ell0 : opt_lbl) (M'0 : session),
                betaP_lbl M (lcomm n0 q0 ell0) M'0) t).
                destruct (constructive_indefinite_description
                (fun ell0 : opt_lbl =>
                exists M'0 : session, betaP_lbl M (lcomm n0 x0 ell0)
                M'0) e).
                destruct (constructive_indefinite_description
                (betaP_lbl M (lcomm n0 x0 x1)) e0).
                destruct (Nat.eq_dec n0 p).
                {
                    subst. destruct Htyp as [gamma Htyp]. eapply betaP_lbl_send_unique in b as Htr;
                    try exact Htrans;try exact Htyp;subst.  exists x1. constructor. simpl.
                    tauto.   
                }
                {
                    assert(Hhelp : exists n', (S n') <= (S n)  /\
                   until_indexed 
                    (fun u=>match u with Some (cocons x xs) => x <> p | _ => False end)
                    (fun u=>match u with Some (cocons x xs) => x = p | _ => False end)
                    (S n') (cocons n0 x)).
                    {
                        eapply is_part_stream_suf in i as Hit;try exact Hplt.

                        eapply distance_to_p with (p:=p) in Hit;try easy.
                        destruct Hit as [sn' [Hits1 Hits2]].
                        destruct sn'. simpl in Hits1;congruence.
                        exists sn'.
                        split;try easy. 
                        assert(Hnop : until (fun u=> match u with cocons x xs => x <> p | _ => False end) 
                        (fun u=> u=cocons n0 x) inf_pl).
                        {
                            eapply until_mono;try exact u;
                            intros;simpl. destruct a;try easy. red;intros;subst. red in H.
                            eapply H;try exact Htrans. simpl in H. destruct a;try easy.
                        }
                       
                        eapply until_to_until_indexed in Hnop as 
                        Hnop_ind;destr_hyps;try easy.
                        rename x3 into xsuf.
                        assert(Hnop2 :  until_indexed
                        (fun u : option (coseq opt_lbl) =>
                        match u with
                        | Some (cocons x _) => x <> p
                        | _ => False
                        end)
                        (fun u : option (coseq opt_lbl) =>
                        match u with
                        | Some r => r =  x
                        | None => False
                        end) (S xsuf) inf_pl).
                        {
                            
                            red in H;destr_hyps.
                            assert(stream_nth (S xsuf) inf_pl = Some x).
                            {
                                assert(Hr': S xsuf = 1+xsuf) by lia.
                                rewrite Hr'.
                                rewrite <- stream_nth_sum. destruct (stream_nth xsuf inf_pl);try easy;subst.
                                simpl.
                                destruct x;try easy.    
                                assert(is_suffix conil inf_pl).
                                eapply suffix_tail;try exact i.
                                
                                eapply is_part_stream_suf in Hplt;try exact H.
                                red in Hplt.
                                specialize (Hplt _ Hinp).
                                pinversion Hplt. red in H3.
                                inversion H3;subst. easy.
                            }
                            split;simpl.
                            destruct inf_pl;try easy. simpl in H3. rewrite H3. easy.
                            intros.
                            rewrite Nat.lt_succ_r in H4.
                            destruct H4. destruct (stream_nth i0 inf_pl);try easy;subst.
                            easy.
                            eapply H2. lia.   
                        }

                        assert(Hsmall1: (S xsuf) <= S n).
                        {
                            specialize (Nat.lt_trichotomy (S xsuf) (S n)) as Htr.
                            destruct Htr as [Htr | [Htr | Htr]];try lia.
                            destruct Hdist as [Hd1 Hd2].
                            red in H, Hnop2;destr_hyps.
                            eapply H3 in Htr as Hsa.

                            destruct (stream_nth ( S n) inf_pl) eqn:Hyg;simpl;try easy.
                            destruct c;simpl;try easy.
                        }
                        assert (Hr: (S xsuf) + (S n - S xsuf) = S n) by lia.
                        assert(xsuf + (S sn') <= S n).
                        {
                            
                            specialize (Nat.lt_trichotomy (S sn' +  xsuf) (S n)) as Htr.
                            destruct Htr as [Htr | [Htr | Htr]];try lia.
                            move Hdist at bottom.
                            destruct Hdist as [Hd1 Hd2].
                            rewrite <- Hr in Hd1.
                            
                            rewrite <- Nat.add_comm in Hd1.
                            rewrite <- stream_nth_sum in Hd1.       
                            move Hnop2 at bottom. red in Hnop2;destr_hyps.
                            destruct(stream_nth (S xsuf) inf_pl) eqn:Hyg;try easy;subst.
                            assert(Hs2: S n - xsuf < S sn') by lia.
                            eapply Hits2 in Hs2.
                            assert(S n - xsuf = S (n-xsuf)) by lia.
                            rewrite H2 in Hs2. simpl in Hs2.
                            assert(S n - S xsuf = n- xsuf) by lia.
                            rewrite H4 in Hd1. 
                            destruct (stream_nth (n-xsuf) x) eqn:Hyg';try easy.
                            destruct c;try easy.
   
                        }
                        lia.
                    }
                    destr_hyps.
                    destruct Htyp as [gamma Htyp].
                    assert(Htrans2: exists M'' ellt, betaP_lbl x2 (lcomm p q ellt) M'').
                    {
                        destruct (Nat.eq_dec q x0);subst.
                        eapply betaP_lbl_recv_unique in Htrans;try exact b;try exact Htyp;try easy.
                        
                        eapply betaP_lbl_trans_enabled_after_distinct in b as Hbt;try exact Htrans;try exact Htyp;try easy.
                    }
                    destruct Htrans2 as [M'' [ell' Htrans2]].

                    eapply IH with (m:=  x3) (inf_pl := x) in  Htrans2 as [ellt IH_use];try lia.
                    exists ellt. constructor 2. exact IH_use.
                    eapply sub_red_strong_labelled in b as Hbt;try exact Htyp. destr_hyps.
                    exists x7. easy.
                    eapply part_after_beta;try exact b. 
                    eapply betaP_lbl_means_part in Htrans;easy.
                    red in H2;destr_hyps.
                    split;try easy.
                    intros.
                    specialize (H3 (S i0)). simpl in H3. eapply H3. lia.
                } 
            }
            {
                red in n0. exfalso;eapply n0. red. exists p, q, ell, M';easy.   
            }
        }
    }
Qed.


Lemma fair_scheduler_fair : forall M (Htyp:typable M) inf_pl Hplt, 
    fair_path_proc (fair_scheduler inf_pl M Hplt).
Proof.
    pcofix CIH.
    intros. 
    pfold.
    remember (fair_scheduler inf_pl M Hplt) as fair_sc.
    pose proof Heqfair_sc as Heqf2.
    rewrite (coseq_eq);simpl. rewrite Heqfair_sc.
    rewrite coseq_eq in Heqfair_sc. simpl in *.
       
    destruct (excluded_middle_informative (has_transition_left M)).
    destruct (get_first_available_trans inf_pl M Hplt h
    (has_transition_left_means_parts_some M inf_pl h Hplt)).
    destruct x;try solve [destr_hyps;easy]. destruct a;try easy. destruct a;try easy.
    
    destruct (constructive_indefinite_description
    (fun q : opt_lbl =>
    exists (ell : opt_lbl) (M' : session),
    betaP_lbl M (lcomm n q ell) M') t);try easy.
    destruct (constructive_indefinite_description
    (fun ell : opt_lbl =>
    exists M' : session, betaP_lbl M (lcomm n x0 ell) M') e).
        destruct (constructive_indefinite_description
    (betaP_lbl M (lcomm n x0 x1))). constructor. red.
    intros. simpl in H. destr_hyps.
    rewrite <- Heqfair_sc. rewrite Heqf2.
    eapply fair_scheduler_fair_helper;try exact H;try easy.
    right. eapply CIH.
    destruct Htyp as [gamma Htyp].
    eapply sub_red_strong_labelled in b as Hbt;try exact Htyp. destr_hyps.
    exists x3. easy.
    constructor. red. intros.
    simpl in H. destr_hyps. exfalso;eapply n. exists p,q,ell, x. easy.
    constructor. pfold. constructor. red. intros. easy.
Qed.

Lemma fairness_feasible_proof : fairness_feasible.
Proof. red. intros. red.  

    specialize (inf_parts_is_parts_stream M) as Hr.

    specialize (fair_scheduler_head M (inf_part_list M) Hr) as Hteq.
    destr_hyps.
    exists x,(fair_scheduler (inf_part_list M) M Hr).
    split;[|split].
    rewrite H0. simpl. easy.
    eapply fair_scheduler_valid. easy.
    eapply fair_scheduler_fair. easy.
Qed.

Lemma typable_sess_live: forall M, typable M -> live_sess M.
Proof.
    intros. red in H;destr_hyps.
    eapply extends_to_fair_implies_live in H;try easy.
    eapply fairness_feasible_proof.
Qed.

