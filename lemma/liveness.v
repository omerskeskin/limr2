(* From mathcomp Require Import ssreflect.seq all_ssreflect. *)
From Paco Require Import paco pacotac.
From SST Require Import src.expr src.header src.local CpdtTactics src.lcontext.
From SST Require Import src.global src.projection src.part  src.balanced src.merge src.wfltt src.gttreeh.
From SST Require Import lemma.projection lemma.projection_helper lemma.decidable lemma.liveness_helpers lemma.soundness.
From SST Require Import src.step lemma.step src.assoc lemma.completeness lemma.path_assoc lemma.multigrafting src.ltth src.path_props.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Init.Logic Lia.
From Coq Require Import IndefiniteDescription.


Import ListNotations.

Definition head_proj_is_recv p q:=(
    fun (pt:global_path) => match pt with 
        | cocons (hd,l) tl => exists xs, 
        projectionC hd p (ltt_recv q xs)   
        | _ => False end
        ).

Definition head_proj_is_send p q:=(
    fun (pt:global_path) => match pt with 
        | cocons (hd,l) tl => exists xs, 
        projectionC hd p (ltt_send q xs)   
        | _ => False end
        ).


Lemma weak_untilC_to_until {T:Type} A B (xs: coseq T): weak_untilC A B xs -> 
    eventually B xs -> until A B xs.
Proof.
        intros. generalize dependent H. induction H0.
        {
            intros. constructor 1;easy.   
        }
        {
            intros.
            pinversion H;subst. constructor 1;easy.

            constructor 2;try easy. eapply IHeventually;easy.   
        }
Qed.


Lemma part_after_step_r_redux: forall g g' p q  ell r, wfgC g -> 
    projectableA g ->
    gttstepC g g' p q ell -> r <> p -> r <> q -> isgPartsC r g -> isgPartsC r g'.
    Proof.
        intros * Hwfg Hprojable Hstep Hne1 Hne2 Hisparts.
        specialize (Hprojable r) as Hprojr;destr_hyps. 
        eapply part_after_step_r;try exact Hisparts;try exact Hstep;try exact H;try easy.
        eapply wfgC_after_step;try exact Hstep;try easy.
    Qed.


Definition trans_involves_p l r :=
    match l with 
        | lsend p q _ _ => p=r \/ q=r  
        | lrecv p q _ _ => p=r \/ q=r
        | lcomm p q  _ => p=r \/ q=r
    end.

Definition head_trans_not_involving_p {A:Type} p (xs:coseq (A * option label)) := match xs with 
    | conil => True
    | cocons (g,Some l) xs =>  (trans_involves_p l p -> False) 
    | _ => True end.

Lemma typ_after_step_r_redux : forall (G G' : gtt) (p q s l : opt_lbl)
                    (T : ltt),
                    wfgC G -> projectableA G ->
                    gttstepC G G' p q l ->
                    s <> q ->
                    s <> p ->
                    projectionC G s T ->
                    exists T' : ltt, projectionC G' s T' /\ T = T'.
                Proof.
                    intros.
                    eapply proj_cont_pq_step in H1 as Hlocals;try easy.
                    destr_hyps.
                    eapply typ_after_step_3_helper with (G:=G) (p:=p) (q:=q) (l:=l) (L1:=x) (L2:=x0);
                    try exact H7;try exact H8; try easy.
                    eapply wfgC_after_step in H1;try easy.
                Qed.
            
Ltac subtac_tail_solve:=
                match goal with [ H: ?ct (cocons _ ?a) |- ?ct ?a] => pinversion H;subst;tauto end.
                
Ltac subtac_tail_valid:=
                match goal with [ H: global_valid_pathC (cocons _ ?a) |- global_valid_pathC ?a] =>
                 pinversion H;subst;try easy;try apply valid_path_mon;try (pfold;constructor) end.
                            

Lemma no_trans_until_heads_match_send : forall p q xs, fair_path_global xs ->
global_valid_pathC xs -> 
wfg_global_path xs -> 
head_proj_is_send p q xs -> weak_untilC (head_trans_not_involving_p p) 
(head_proj_is_recv q p) xs.
Proof.
    intros * Hfair Hvalid Hwfgp Hprojp.
    generalize dependent xs.
    pcofix CIH.
    destruct xs.
    {
        intros;red in Hprojp;easy.   
    }
    {
        generalize dependent xs.
        intros.        
        destruct p0 as [g l].
        assert(Hwfg : wfgC g)
        by  (eapply wfg_global_path_head;try exact Hwfgp).
        
        assert(Hprojable : projectableA g) 
        by (pinversion Hwfgp;subst; red in H1;tauto).
        destruct l.
        {
            pinversion Hvalid;try apply valid_path_mon;subst.
            destruct l;try easy.
            rename n into s, n0 into t, n1 into ell.
            pfold.
            destruct (Nat.eq_dec s p);
            destruct (Nat.eq_dec t p);subst;try tauto;red in H3.
            {
                pinversion H3;try apply step_mon;subst;tauto.
            }
            {
                eapply proj_cont_pq_step in H3 as Hlocals;try easy.
                red in Hprojp. destruct Hprojp as [xsp Hprojp].
                destr_hyps.
                eapply proj_inj in H;try exact Hprojp;try easy.
                inversion H;subst.
                constructor 1. simpl. exists x1. easy.
            }
            {
                eapply proj_cont_pq_step in H3 as Hlocals;try easy.
                red in Hprojp. destruct Hprojp as [xsp Hprojp].
                destr_hyps.
                eapply proj_inj in H0;try exact Hprojp;try easy.
            }
            {
                constructor 2. simpl;destruct (Nat.eq_dec s p);destruct (Nat.eq_dec t p);try tauto.
                
                right. 
                eapply CIH;try solve subtac_tail_solve.
                pfold. inversion Hvalid;subst. destruct H2. punfold H;try apply valid_path_mon;try easy. 
                inversion H.
                                red in Hprojp. destruct Hprojp as [xsp Hprojp].
                eapply typ_after_step_r_redux in H3;try exact Hprojp;try easy;subst.

                red.
                exists xsp. destr_hyps;subst;tauto.
            }
        }
        {
            pinversion Hvalid;try apply valid_path_mon;subst.
            pfold.
            constructor 2; try easy.
            left. pfold. constructor 3 . simpl;easy. 
        }   
    }
Qed.

Lemma no_trans_until_heads_match_recv : forall p q xs, fair_path_global xs ->
global_valid_pathC xs -> 
wfg_global_path xs -> 
head_proj_is_recv p q xs -> weak_untilC (head_trans_not_involving_p p) 
(head_proj_is_send q p) xs.
Proof.
    intros * Hfair Hvalid Hwfgp Hprojp.
    generalize dependent xs.
    pcofix CIH.
    destruct xs.
    {
        intros;red in Hprojp;easy.   
    }
    {
        generalize dependent xs.
        intros.        
        destruct p0 as [g l].
        assert(Hwfg : wfgC g)
        by  (eapply wfg_global_path_head;try exact Hwfgp).
        
        assert(Hprojable : projectableA g) 
        by (pinversion Hwfgp;subst; red in H1;tauto).
        destruct l.
        {
            pinversion Hvalid;try apply valid_path_mon;subst.
            destruct l;try easy.
            rename n into s, n0 into t, n1 into ell.
            pfold.
            destruct (Nat.eq_dec s p);
            destruct (Nat.eq_dec t p);subst;try tauto;red in H3.
            {
                pinversion H3;try apply step_mon;subst;tauto.
            }
            {
                eapply proj_cont_pq_step in H3 as Hlocals;try easy.
                red in Hprojp. destruct Hprojp as [xsp Hprojp].
                destr_hyps.
                eapply proj_inj in H;try exact Hprojp;try easy.
                
            }
            {
                
                eapply proj_cont_pq_step in H3 as Hlocals;try easy.
                red in Hprojp. destruct Hprojp as [xsp Hprojp].
                destr_hyps.
                eapply proj_inj in H0;try exact Hprojp;try easy.
                inversion H0;subst.
                constructor 1. simpl. exists x0. easy.
            }
            {
                constructor 2. simpl;destruct (Nat.eq_dec s p);destruct (Nat.eq_dec t p);try tauto.
                
                right. 
                eapply CIH;try solve subtac_tail_solve.
                pfold. inversion Hvalid;subst. destruct H2. punfold H;try apply valid_path_mon;try easy. 
                inversion H.
                                red in Hprojp. destruct Hprojp as [xsp Hprojp].
                eapply typ_after_step_r_redux in H3;try exact Hprojp;try easy;subst.

                red.
                exists xsp. destr_hyps;subst;tauto.
            }
        }
        {
            pinversion Hvalid;try apply valid_path_mon;subst.
            pfold.
            constructor 2; try easy.
            left. pfold. constructor 3 . simpl;easy. 
        }   
    }
Qed.


Inductive gttstepH : gtth -> part -> part -> 
nat -> gtth ->  Prop :=
    | stepH_hol : forall m n p q ell, gttstepH (gtth_hol n) p q ell (gtth_hol m)
    | stepH_send : forall ell p q srt ghs gh',
    p <> q ->
    onth ell ghs = Some (srt, gh') -> gttstepH (gtth_send p q ghs) p q ell gh' 
    | stepH_cont : forall ell p q s t ghs ghs' ,
    s <> p -> 
    s <> q ->
    t <> p ->
    t <> q ->
    p <> q ->
    Forall2
(fun u v : option (sort * gtth) =>
u = None /\ v = None \/
(exists (s0 : sort) gh gh',
u = Some (s0, gh) /\ v = Some (s0, gh') /\ gttstepH gh  p q ell gh'))
ghs ghs' ->
    gttstepH (gtth_send s t ghs)
    p q ell 
    (gtth_send s t ghs')
    | stepH_eq : forall a b b' c p q ell, gtth_eq a b ->
gtth_eq b' c -> gttstepH b p q ell b' -> gttstepH a p q ell c.

Lemma typ_p_gtth_unique : forall gx gs gx' gs' r g, typ_p_gtth gs gx r g -> 
typ_p_gtth gs' gx' r g -> gtth_eq gx gx'.
Proof.
    induction gx using gtth_ind_ref.
    {
        intros * Htyp1 Htyp2.
        destruct Htyp1 as [?Htyp [?Htyp ?Htyp]].   
        destruct Htyp2 as [?Htyp' [?Htyp' ?Htyp']].
        destruct gx'. constructor.

        inversion Htyp';subst.
        inversion Htyp;subst.
        eapply Forall_prop in Htyp1;try exact H1.
        destruct Htyp1;try easy.
        destr_hyps.
        destruct H ;[| destruct H];inversion H;subst;subtac_triv_isparts_false.
    }
    {
        intros * Htyp1 Htyp2.
        
        destruct Htyp1 as [?Htyp [?Htyp ?Htyp]].   
        destruct Htyp2 as [?Htyp' [?Htyp' ?Htyp']].
        inversion Htyp;subst.
        destruct gx'. 
        {
            inversion Htyp';subst.
            eapply Forall_prop in Htyp'1;try exact H2.
            destruct Htyp'1;try easy.
            destr_hyps.
            destruct H0;[|destruct H0];inversion H0;subst;subtac_triv_isparts_false.   
        }
        inversion Htyp';subst.
        constructor.
        eapply Forall2_forall. eapply Forall2_length in H6,H10. lia.
        intros.
        destruct (onth k xs) eqn:Hyg.
        {
            right. eapply Forall_prop in H;try exact Hyg. destruct H;try easy.
            destr_hyps. inversion H;subst. clear H.
            eapply Forall2_prop_r in H6;try exact Hyg;tac_sanitize.
            eapply Forall2_prop_l in H10;try exact H2;tac_sanitize.
            exists x0, x3, x1.
            repeat split;try easy.
            eapply H0 with (gs:=gs) (r:=r) (g:=x5) (gs':=gs');repeat split;try easy.
            intros. apply Htyp0. 
            econstructor;try exact Hyg;try easy;red;intros;subst; subtac_triv_isparts_false.
            intros. apply Htyp'0. 
            econstructor;try exact H1;try easy; red;intros;subst; subtac_triv_isparts_false.
        
        }
        {
            left. split;try easy.    
            destruct (onth k l) eqn:Hyg'.
            eapply Forall2_prop_r in H10;try exact Hyg';tac_sanitize.
            eapply Forall2_prop_l in H6;try exact H2; tac_sanitize.
            rewrite Hyg in H1;easy.
            easy.
        }   
    }
Qed.

Lemma gtth_eq_refl : forall gx, gtth_eq gx gx.
            Proof.
                induction gx using gtth_ind_ref.
                {
                    constructor.   
                }
                {
                    constructor. eapply Forall2_forall;try easy;intros.
                    destruct (onth k xs) eqn: Hyg;try tauto.
                    right. destruct p0. exists s, g, g. repeat split;try tauto.
                    eapply Forall_prop in H;try exact Hyg. destruct H;try easy.
                    destr_hyps. inversion H;subst;easy.   
                }
            Qed.

Lemma gttstepH_consistent: forall gx gs r p q ell g g' gx' gs', 
    r <> p ->
    r <> q ->
    wfgC g ->
    typ_p_gtth gs gx r g -> 
    wfgC g' ->
    gttstepC g g' p q ell ->
    typ_p_gtth gs' gx' r g' -> 
     gttstepH gx  p q ell gx'.
Proof.
    induction gx using gtth_ind_ref.
    {
        intros * Hner1 Hner2 Hwfg Htyp  Hwfg' Hstep Htyp'.
        destruct gx';try constructor.
        destruct Htyp as [?Htyp [?Htyp ?Htyp]].
        inversion Htyp;subst.
        eapply Forall_prop in Htyp1;try exact H1. destruct Htyp1;try easy.
        destr_hyps.
        destruct H;[|destruct H];inversion H;subst;
        try solve
        [
            pinversion Hstep;try apply step_mon;subst;try easy;
            destruct Htyp' as [?Htyp' [?Htyp' ?Htyp']];
            inversion Htyp';subst;
            subtac_triv_isparts_false |
            inversion H;subst;
            eapply no_step_from_end in Hstep;try easy
        ].
    }
    {
        intros * Hner1 Hner2 Hwfg Htyp  Hwfg' Hstep Htyp' .
        destruct Htyp as [?Htyp [?Htyp ?Htyp]].
        destruct Htyp' as [?Htyp' [?Htyp' ?Htyp']].
        inversion Htyp;subst.
        rename xs into ghs, ys into gcs.
        pinversion Hstep;subst;try easy;try apply step_mon.
        {
            symmetry in H10.
            eapply Forall2_prop_l in H6;try exact H10;tac_sanitize.
            assert(typ_p_gtth gs x1 r x2).
            {
                repeat split;try easy. intros. eapply Htyp0. econstructor;try exact H1;try easy.   
            }
            Search gtth_eq.
            
            assert (typ_p_gtth gs' gx' r x2) by (repeat split;easy).
            eapply typ_p_gtth_unique in H0;try exact H2.
            apply gtth_eq_sym in H0.
            econstructor 4;try exact H0. apply gtth_eq_refl. 
            econstructor 2 with (srt:=x0);try easy.
        }
        {
            destruct gx'. 
            {
                inversion Htyp';subst.
                eapply Forall_prop in Htyp'1;try exact H2.
                destruct Htyp'1;try easy.
                destr_hyps.
                destruct H0;[|destruct H0];
                inversion H0;subst;subtac_triv_isparts_false.   
            }
            inversion Htyp';subst. constructor;try easy.
            eapply Forall2_forall. eapply Forall2_length in H16,H18, H6;lia. 
            intros.
            destruct (onth k ghs) eqn:Hyg.
            {
                right.
                eapply Forall2_prop_r in H6;try exact Hyg;tac_sanitize.
                eapply Forall2_prop_r in H16;try exact H2;tac_sanitize.
                eapply Forall2_prop_l in H18;try exact H12;tac_sanitize.
                exists x0, x1, x2.
                repeat split;try easy.
                eapply Forall_prop in H;try exact Hyg;destruct H;try easy.
                destr_hyps;inversion H;subst.
                eapply H0 with (g:=x4) (r:=r) (gs:=gs) (gs':=gs') (g':=x6);try easy;
                try solve subtac_wfg_by_onth.
                repeat split;try easy. intros. eapply Htyp0. 
                econstructor;try exact Hyg;try easy;
                red;intros;subst;subtac_triv_isparts_false.
                destruct H13;try easy.
                repeat split;try easy.
               
                intros. eapply Htyp'0. 
                econstructor;try exact H1;try easy;
                red;intros;subst;subtac_triv_isparts_false.
            }  
            {
                left. split;try easy.
                destruct (onth k l) eqn:Hyg';try easy.
                eapply Forall2_prop_r in H18;try exact Hyg';tac_sanitize.
                eapply Forall2_prop_l in H16;try exact H2;tac_sanitize.  
                eapply Forall2_prop_l in H6;try exact H1;tac_sanitize.
                rewrite Hyg in H6;easy. 
            }
        }
    }
Qed. 

Lemma gtth_height_eq_by_forall2 : forall gxs p q p' q' gxs',
Forall2 (fun u v => u=None /\ v=None \/ 
exists s g g', u=Some (s,g) /\ v= Some (s,g') /\ gtth_height g = gtth_height g') gxs gxs' ->
gtth_height (gtth_send p q gxs) = gtth_height (gtth_send p' q' gxs').
Proof.
    induction gxs.
    intros. inversion H;subst;crush.
    intros. inversion H;subst.
    destruct a. destruct H2;try easy. destr_hyps. inversion H0;subst;clear H0.
    rewrite gtth_height_unfold_once_some.
    rewrite gtth_height_unfold_once_some.
    
    specialize (IHgxs p q p' q' _ H4). rewrite IHgxs. rewrite H2. simpl. lia.

    destruct H2;destr_hyps;subst. do 2 
    (rewrite gtth_height_unfold_once_none). 
    specialize (IHgxs p q p' q' _ H4). lia.
    inversion H0.
Qed.

Lemma gtth_eq_mon_gtth_height: forall gx gx', gtth_eq gx gx' -> gtth_height gx =gtth_height gx'.
Proof.
    induction gx using gtth_ind_ref;
    intros * Heq.
    {
        inversion Heq;subst;try easy.   
    }
    {
        inversion Heq;subst. 
        eapply gtth_height_eq_by_forall2.
        eapply Forall2_forall. eapply Forall2_length in H4;try easy.
        intros.
        destruct (onth k xs) eqn:Hyg. right.
        eapply Forall2_prop_r in H4;try exact Hyg;tac_sanitize. 
        exists x0, x1, x2. repeat split;try easy.
        eapply Forall_prop in H;try exact Hyg. destruct H;try easy.
        destr_hyps. inversion H;subst. eapply H0;easy.
        destruct (onth k ys) eqn:Hyg';try tauto.
        right. eapply Forall2_prop_l in H4;try exact Hyg';tac_sanitize. rewrite Hyg in H1;try easy.       
    }
Qed.    


Section gttstepH_ind_ref.

Variable P : gtth -> nat -> nat -> nat -> gtth  -> Prop.
Hypotheses P_base: forall n m p q ell, P (gtth_hol n) p q ell (gtth_hol m).
Hypotheses P_onth : forall p q xs n s g, 
onth n xs = Some (s,g) -> P (gtth_send p q xs) p q n g.

Hypothesis P_send_cont : forall p q s t ell xs ys,
    p <> s -> 
    p <> t ->
    q <> s ->
    q <> t ->
    s <> t ->
List.Forall2 (fun u v => (u = None /\ v = None) \/ 
(exists sr g g', u = Some(sr, g) /\ v = Some(sr, g') /\ P g s t ell g')) xs ys -> 
P (gtth_send p q xs) s t ell (gtth_send p q ys).
  
Hypothesis P_eq: forall a b b' c s t ell, gtth_eq a b -> gtth_eq b' c -> P b s t ell b' -> P a s t ell c.
Check stepH_cont.
Fixpoint gttstepH_ind_ref p q ell G G' (Hstep : gttstepH  G p q ell G') {struct Hstep} : P G p q ell G'.
  Proof.
    refine (match Hstep with
      | stepH_hol a b p q ell=> P_base b  a p q ell
      | stepH_send ell p q srt ghs gh' Hpeq Honth => P_onth p q ghs ell srt gh' Honth
      | stepH_cont ell s t p q ghs ghs' Hneq1 Hneq2 Hneq3 Hneq4 Hneq5 _ => P_send_cont p q s t ell ghs ghs'  Hneq1 Hneq2 Hneq3 Hneq4 Hneq5 _
      | stepH_eq a b b' c p q ell Heq1 Heq2 _ => _ 
    end); try easy.
    {
        revert f. eapply Forall2_mono.
        intros.
        destruct H;destr_hyps;subst. left;tauto.

        right. exists x0, x1, x2. repeat split;try easy.
        eapply gttstepH_ind_ref;try exact H1.
    }
    {
        eapply P_eq;try exact Heq1;try exact Heq2. eapply gttstepH_ind_ref;try exact g.
    }
    Guarded.
  Qed.

End gttstepH_ind_ref.

Lemma gtth_height_le_by_forall2 : forall  xs p q s t ys ,  
        Forall2
(fun u v : option (sort * gtth) =>
u = None /\ v = None \/
(exists (s : sort) (g g' : gtth),
u = Some (s, g) /\
v = Some (s, g') /\ gtth_height g' <= gtth_height g))
xs ys -> gtth_height (gtth_send p q ys) <= gtth_height (gtth_send s t xs).
    Proof.
        induction xs. intros. inversion H;subst;simpl;lia.
        intros. inversion H;subst.
        destruct H2.
        {
            destr_hyps;subst.
            do 2 rewrite gtth_height_unfold_once_none. specialize (IHxs p q s t _ H4). lia.   
        }
        {
            destr_hyps;subst.
            do 2 rewrite gtth_height_unfold_once_some. specialize (IHxs p q s t _ H4). lia.   
            
        }
        
    Qed.

Lemma gtth_height_lt_by_forall2 : forall  xs p q s t ys ,  
SList xs ->
        Forall2
(fun u v : option (sort * gtth) =>
u = None /\ v = None \/
(exists (s : sort) (g g' : gtth),
u = Some (s, g) /\
v = Some (s, g') /\ gtth_height g' < gtth_height g))
xs ys -> gtth_height (gtth_send p q ys) < gtth_height (gtth_send s t xs).
    Proof.
        induction xs; intros * Hslist Hfa2. inversion Hslist.
        inversion Hfa2;subst.
        assert (Hslist_y: SList (y::l')).
        {
            eapply SList_by_Forall2;try exact Hslist.
            eapply Forall2_mono;try exact Hfa2;intros. simpl in H.
            destruct H;try tauto. destr_hyps;subst.
            right. exists (x0, x1), (x0,x2). tauto.
        }
        destruct H1.
        {
            destr_hyps;subst.
            do 2 rewrite gtth_height_unfold_once_none. 
            simpl in Hslist_y, Hslist.
            specialize (IHxs p q s t _ Hslist H3). lia.   
        }
        {
            destr_hyps;subst.
            do 2 rewrite gtth_height_unfold_once_some.
            destruct xs.
            {
                inversion H3;subst;simpl;lia.   
            }
            assert (Hsres: SList (o::xs)).
            {
                simpl in Hslist. easy.   
            }
            
            specialize (IHxs p q s t _ Hsres H3). lia.   
            
        }
        
    Qed.


Lemma gttstepH_height_le: forall   p q ell gx gx', gttstepH gx p q ell gx' ->
    gtth_height gx' <= gtth_height gx.
Proof.
    eapply gttstepH_ind_ref.
    {
        intros. simpl;lia.   
    }
    {
        intros.   
        apply gtth_height_ge_children with (k:=gtth_height g) (p:=p) (q:=q) in H;lia. 
    }
    {
        intros.
        eapply gtth_height_le_by_forall2;try exact H. revert H4;eapply Forall2_mono;crush.
    }
    {
        intros.
        eapply gtth_eq_sym in H0.
        erewrite gtth_eq_mon_gtth_height;try exact H0.
        assert (gtth_height a =gtth_height b) by
        (
        eapply gtth_eq_mon_gtth_height in H;easy).
        eapply gtth_eq_mon_gtth_height in H0. lia.
    }
Qed.


Lemma graft_height_after_step: forall gs gx gs' gx' p g' g s t ell, 
p <> s ->
p <> t ->
wfgC g ->
projectableA g ->
isgPartsC p g ->
typ_p_gtth gs gx p g ->
usedCtx gs gx -> gttstepC g g' s t ell ->
typ_p_gtth gs' gx' p g' ->
usedCtx gs' gx' -> (gtth_height gx' <= gtth_height gx).
Proof.
    intros * Hps Hpt Hwfg Hprojable Hispartsp Htypg Husedp Hstep
    Htypg' Husedq.

    eapply gttstepH_consistent in Hstep; try exact Htypg;try exact Htypg';try easy.
    eapply gttstepH_height_le in Hstep;try easy.
    eapply wfgC_after_step;try exact Hstep;try easy.
Qed.

Definition head_proj_is p lt (xs:global_path) := match xs with | conil => False
    | cocons (g,l) xs => projectionC g p lt end.

Definition head_proj_is_nil_true p lt (xs:global_path) := match xs with 
| conil => True
    | cocons (g,l) xs => projectionC g p lt end.

Lemma no_trans_implies_same_proj_send : forall xs p q lcs,
fair_path_global xs ->
global_valid_pathC xs -> 
wfg_global_path xs -> 
head_proj_is p (ltt_send q lcs) xs ->
until (head_trans_not_involving_p p) (head_proj_is_recv q p) xs ->
eventually ( head_proj_is p (ltt_send q lcs) /1\ head_proj_is_recv q p) xs.
Proof.
    intros * Hfair Hvalid Hwfgp Hprojp Huntil.

    induction Huntil.
    {
        constructor. tauto.   
    }
    {
        constructor 2.
        eapply IHHuntil;try solve subtac_tail_solve;
        pinversion Hvalid;try apply valid_path_mon;subst; try solve [easy |pfold; constructor].
        
        red in Hprojp.
        inversion Huntil;subst;tauto.

        destruct l;red in H3;try easy.
        rename y into g, x0 into g'.
        red in H;red in Hprojp. 
        
        simpl in H.
        destruct (Nat.eq_dec n p);
        destruct (Nat.eq_dec n0 p);subst;try tauto.
        assert(Hwfg : wfgC g)
        by  (eapply wfg_global_path_head;try exact Hwfgp).
        
        assert(Hprojable : projectableA g) 
        by (pinversion Hwfgp;subst; red in H4;tauto).
        eapply typ_after_step_r_redux in H3;try exact Hprojp;try easy.
        red. destr_hyps. subst. easy.
    }
Qed.


Lemma no_trans_implies_same_proj_recv : forall xs p lcs q,
fair_path_global xs ->
global_valid_pathC xs -> 
wfg_global_path xs -> 
head_proj_is p (ltt_recv q lcs) xs ->
until (head_trans_not_involving_p p) (head_proj_is_send q p) xs ->
eventually ( head_proj_is p (ltt_recv q lcs) /1\ head_proj_is_send q p) xs.
Proof.
    intros * Hfair Hvalid Hwfgp Hprojp Huntil.

    induction Huntil.
    {
        constructor. tauto.   
    }
    {
        constructor 2.
        eapply IHHuntil;try solve subtac_tail_solve;
        pinversion Hvalid;try apply valid_path_mon;subst; try solve [easy |pfold; constructor].
        red in Hprojp.
        inversion Huntil;subst;tauto.
        destruct l;red in H3;try easy.
        rename y into g, x0 into g'.
        red in H;red in Hprojp. 
        simpl in H.
        destruct (Nat.eq_dec n p);
        destruct (Nat.eq_dec n0 p);subst;try tauto.
        assert(Hwfg : wfgC g)
        by  (eapply wfg_global_path_head;try exact Hwfgp).
        
        assert(Hprojable : projectableA g) 
        by (pinversion Hwfgp;subst; red in H4;tauto).
        eapply typ_after_step_r_redux in H3;try exact Hprojp;try easy.
        red. destr_hyps.  subst. easy.
    }
Qed.

Lemma eventually_P_always_PQ_eventually_Q {A:Type} (P: coseq A -> Prop) Q: forall xs, eventually P xs -> alwaysCG (fun u=>
P u -> eventually Q u) xs -> eventually Q xs .
Proof.
    intros. generalize dependent H0. induction H.
    {
        intros. pinversion H0;subst; eapply H1;easy.   
    }
    {
        intros.
        pinversion H0;subst. constructor 2. eapply IHeventually. easy.    
    }
Qed.

Print live_path_inner_global.

Print fair_path_inner_global.

Lemma matching_proj_enables_step : forall g p q xp xq, wfgC g ->
projectionC g p (ltt_send q xp)  ->
projectionC g q (ltt_recv p xq)  ->
exists g' ell, gttstepC g g' p q ell.
Proof.
    intros * Hwfg Hprojp Hprojq .
    assert (Hwflp: wflttC (ltt_send q xp)).
    {
        eapply projection_implies_wf;try exact Hprojp;try easy.   
    }
    assert (Hwflq: wflttC (ltt_recv p xq)).
    {
        eapply projection_implies_wf;try exact Hprojq;try easy.   
    }
    eapply lem_6_16_simul_subproj with (p:=p) (q:=q) (xp:=xp) (xq:=xq) in Hwfg as Hsim;try easy.
    eapply wfltt_slist_send in Hwflp. eapply slist_implies_some in Hwflp. destr_hyps.
    eapply Forall2R_prop in Hsim;try exact H;tac_sanitize.
    eapply typ_after_step_step in Hprojp as Htypstep;try exact Hprojp;try exact Hprojq;try exact H;try exact H2;try easy.
    destr_hyps. exists x0, x. easy.
    eapply projection_implies_part_send;try exact Hprojp.
    exists (ltt_send q xp);
    split;try easy;eapply stRefl.
    exists (ltt_recv p xq);
    split;try easy;eapply stRefl.
    eapply wfltt_slist_send in Hwflp;try easy.
    eapply wfltt_slist_recv in Hwflq;try easy.
Qed.

Lemma matching_head_proj_to_comm: forall p q xs, global_valid_pathC xs -> wfg_global_path xs -> fair_path_global xs ->
eventually (head_proj_is_send p q /1\ head_proj_is_recv q p) xs -> 
eventually (headComm_global p q) xs.
Proof.
    intros * Hvalid Hwfgp Hfair Hev. revert Hvalid Hwfgp Hfair.
    induction Hev.
    {
        intros. red in Hfair. unfold  fair_path_inner_global in Hfair.
        pinversion Hfair;subst;

        [destruct H; inversion H |].
        
        destruct x as [g l].
        assert(Hwfg: wfgC g) by
        (pinversion Hwfgp;subst;red in H4;tauto).
        destruct H as [Hprojp Hprojq].
        red in Hprojp, Hprojq.
        destr_hyps.
        eapply matching_proj_enables_step in H2;try exact H;try easy.
        destruct H2 as [g' [ell Hstep]].
        eapply H0 with (n:=ell).  simpl. 
        red. exists g';easy.    
    }
    {
        intros.
        constructor 2. eapply IHHev;try subtac_tail_solve.
        pinversion Hvalid;subst;try apply valid_path_mon. pfold;constructor.
        easy.   
    }
Qed. 

Inductive is_suffix {A:Type}: coseq A -> coseq A -> Prop :=
    | suffix_refl : forall xs, is_suffix xs xs
    | suffix_cons : forall a xs ys, is_suffix xs ys -> is_suffix xs (cocons a ys).




Lemma suffix_trans {A:Type}: forall (xs: coseq A) ys zs,is_suffix xs ys -> is_suffix zs xs -> is_suffix zs ys.
Proof.
    intros.
    
    generalize dependent zs.
    induction H.
    intros;easy.

    intros. constructor. eapply IHis_suffix. easy.
Qed.

Lemma always_P_implies_P_suffix {A:Type} (P: coseq A -> Prop): forall xs, 
alwaysCG P xs -> forall ys,
is_suffix ys xs -> alwaysCG P ys.
Proof.
    intros.
    revert H; induction H0.
    intros. easy.
    intros. eapply IHis_suffix. pinversion H;try easy.
Qed.


Lemma always_P_iff_P_suffix {A:Type} (P: coseq A -> Prop): forall xs, 
alwaysCG P xs <-> forall ys,
is_suffix ys xs -> P ys.
Proof.
    split.
    intros.
    revert H; induction H0.
    intros. pinversion H;subst;easy.

    intros. eapply IHis_suffix. pinversion H;try easy.

    
    generalize dependent xs. pcofix CIH.
    intros. destruct xs. pfold. constructor.
    specialize (H0 conil (suffix_refl conil));easy. 
    
    pfold. constructor. specialize (H0 (cocons a xs) (suffix_refl _));easy.
    right. eapply CIH. 
    intros. eapply H0. eapply suffix_trans with (xs:=xs); try easy. constructor;constructor.
Qed.

Definition eventually_P_iff_P_suffix {A:Type} (P: coseq A -> Prop): forall xs, 
eventually P xs <-> exists ys,
is_suffix ys xs /\ P ys.
Proof.
    intros;split;intros.
    induction H.
    exists xs;split;[constructor | easy].
    destr_hyps. exists x0. split;[constructor | ];crush.
    destruct H as [ys [Hsuf Hp]].
    induction Hsuf;
    [constructor 1 | constructor 2];crush.
Qed.


Lemma eventually_idemp {A:Type}: forall (P : coseq A -> Prop) xs, 
eventually P xs <-> eventually (eventually P) xs.
Proof.
    split;intros.
    constructor. easy.
    induction H;try easy.

    constructor 2. easy.
Qed.

(*incorporate the label*)
(*
Definition head_proj_eventually_takes_step p (xs : global_path) := 
    match xs with 
    | cocons (g,l) xs' => forall Tp, projectionC g p Tp ->
        (
            (forall q lcs, Tp=ltt_send q lcs ->
        exists k s Tp', onth k lcs=Some (s,Tp') /\ eventually 
        (fun u => match u with 
            | cocons (g,Some (lcomm a b ell)) (cocons (g',_) _) => 
            a=p /\ b=q /\ ell =k /\ projectionC g p Tp'
            | _ => False
        end) (cocons (g,l) xs') ) 
        /\  

        (forall q lcs, Tp= (ltt_recv q lcs) ->
        exists k s Tp', onth k lcs=Some (s,Tp') /\ eventually 
        (fun u => match u with 
            | cocons (g,Some (lcomm a b ell)) (cocons (g',_) _) => 
            a=q /\ b=p /\ ell =k /\ projectionC g p Tp'
            | _ => False
        end) (cocons (g,l) xs') ))
    | _ => True end.
*)

Print headComm_global.

Definition head_proj_eventually_takes_step p (xs : global_path) := 
    match xs with 
    | cocons (g,l) xs' => forall Tp, projectionC g p Tp ->
        (
            (forall q lcs, Tp=ltt_send q lcs ->
        eventually 
        (headComm_global p q) (cocons (g,l) xs') ) 
        /\  

        (forall q lcs, Tp= (ltt_recv q lcs) ->
        eventually 
        (headComm_global q p) (cocons (g,l) xs') ))
    | _ => True end.

Lemma always_idemp {A:Type}: forall P (xs : coseq A), alwaysCG P xs <-> alwaysCG (alwaysCG P) xs.
Proof.
    split.
    {
        generalize dependent xs.
        pcofix CIH.
        intros.
        destruct xs. pfold. constructor. easy.    
        intros; 
        pfold; constructor; try easy; right; eapply CIH; pinversion H0;subst;easy.
    }
    {
        generalize dependent xs.
        pcofix CIH.
        intros. destruct xs;pfold;constructor. pinversion H0;subst. pinversion H;subst;easy.
        pinversion H0;subst;pinversion H2;subst;try easy.
        right. eapply CIH. pinversion H0;subst;easy.   
    }
Qed. 

Lemma valid_suffix_valid_global : forall xs ys, global_valid_pathC xs -> is_suffix ys xs -> global_valid_pathC ys.
Proof.
    intros. induction H0;try easy. eapply IHis_suffix. pinversion H;subst;try apply valid_path_mon.
    pfold;constructor. easy.
Qed. 

Definition head_grafting_proper_prefix p q (xs:global_path) := match xs with 
    | conil => True
    | cocons (g,l) xs => exists ctx_p gs_p ctx_q gs_q, typ_p_gtth  gs_p ctx_p p g /\
        typ_p_gtth gs_q ctx_q  q g /\ usedCtx gs_p ctx_p /\ usedCtx gs_q ctx_q /\ is_tree_proper_prefix ctx_p ctx_q end.
    
Definition head_grafting_eq p q (xs:global_path) := match xs with 
    | conil => False
    | cocons (g,l) xs => exists ctx_p gs_p ctx_q gs_q, typ_p_gtth  gs_p ctx_p p g /\
        typ_p_gtth gs_q ctx_q  q g /\ usedCtx gs_p ctx_p /\ usedCtx gs_q ctx_q 
        /\ gtth_eq ctx_p ctx_q end.

Definition all_fair_paths P:= forall xs, fair_path_global xs -> 
global_valid_pathC xs ->  wfg_global_path xs -> P xs.

Lemma head_gtt_send_not_fair : forall p q xs, wfgC (gtt_send p q xs) ->
fair_path_global (cocons (gtt_send p q xs, None) conil) -> False.
Proof.
    intros.
    pinversion H0;subst.
    red in H3.
    eapply wfgC_triv in H as [?Hwftr ?Hwftr]. eapply slist_implies_some in Hwftr0. destr_hyps.

    specialize (H3 p q x).
    assert (to_path_prop (global_comm_enabled p q x) False
(cocons (gtt_send p q xs, None) conil)).
    simpl. red. destruct x0. exists g. pfold. econstructor; try exact (eq_sym H);try easy.
    specialize (H3 H1).
    inversion H3;subst;try easy. inversion H5;subst;easy.
Qed.

Lemma forall_to_always {A:Type} (P:coseq A -> Prop) : forall ys, (forall xs, P xs) ->  alwaysCG P ys.
Proof.
    pcofix CIH.
    intros.
    pfold. destruct ys. constructor. eapply H0.
    constructor. eapply H0. right. eapply CIH. easy.
Qed.

Definition head_part p (xs : global_path) := match xs with conil => False | cocons (g,_) _ => isgPartsC p g end.
Lemma grafting_contains_prefix : forall  ctx_p p gs_p ctx_q gs_q q g,
    typ_p_gtth gs_q ctx_q q g ->
    usedCtx gs_q ctx_q ->
    typ_p_gtth gs_p ctx_p p g ->
    usedCtx gs_p ctx_p ->
    is_tree_proper_prefix ctx_q ctx_p ->
    ishParts q ctx_p.
    Proof.
        induction ctx_p using gtth_ind_ref.
        {
            intros * Hgraftq Husedq Hgraftp Husedp Hpref.
            inversion Hpref.   
        }
        {
            intros * Hgraftq Husedq Hgraftp Husedp Hpref.
            rename q into r, q0 into q, p into s, p0 into p.
            destruct Hgraftq as [?Hgraftq [?Hgraftq ?Hgraftq]].
                destruct Hgraftp as [?Hgraftp [?Hgraftp ?Hgraftp]].
                
            inversion Hpref;subst.
            {
                inversion Hgraftp;subst.
                inversion Hgraftq;subst.
                eapply Forall_prop in Hgraftq1;try exact H2.
                destruct Hgraftq1;try easy.
                destruct H0 as [q0 [lsg [?Htr | [?Htr | ?Htr]]]];
                try solve [
                    inversion Htr;subst; try eapply ha_sendp;try eapply ha_sendq].
                
            }
            {
                inversion Hgraftp;subst.
                eapply slist_implies_some in H6;destr_hyps.
                eapply Forall_prop in H;try exact H0;tac_sanitize.
                eapply ha_sendr;try exact H0;
                rename x into n, xs into ghs_p, xs0 into ghs_q, x1 into sr, x2 into gh.
                1-2:red;intros;subst;subtac_triv_isparts_false.
                eapply Forall2_prop_l in H2;try exact H0;tac_sanitize.
                eapply Forall2_prop_r in H7;try exact H0;tac_sanitize.
                inversion Hgraftq;subst.
                eapply Forall2_prop_l in H11;try exact H5;tac_sanitize.
                rewrite H2 in H3;inversion H3;subst.

                inversion Husedp;subst. 
                eapply Forall2_prop_l in H13;try exact H0;tac_sanitize.

                
                inversion Husedq;subst. 
                eapply Forall2_prop_l in H15;try exact H2;tac_sanitize.
                
                eapply H1 with (p:=p) (gs_q:=x0) (ctx_q:=x7) (g:=x6) (gs_p:=x1);try easy.
                repeat split;
                eapply mergeCtx_onth_subset in H3;try exact H13.
                eapply decidable_helper.typh_with_less;try exact H3;try easy.
                intros. apply Hgraftq0. eapply ha_sendr;try exact H2;try easy.
                1-2:red;intros;subst;subtac_triv_isparts_false.
                eapply Forall_subset;try exact H3;try tauto.
                
                repeat split;
                eapply mergeCtx_onth_subset in H11;try exact H7.
                eapply decidable_helper.typh_with_less;try exact H11;try easy.
                intros. apply Hgraftp0. eapply ha_sendr;try exact H0;try easy.
                1-2:red;intros;subst;subtac_triv_isparts_false.
                eapply Forall_subset;try exact H11;try tauto.
            }
        }
    Qed.

Lemma forall_to_always2 P : (forall xs, fair_path_global xs -> global_valid_pathC xs -> 
wfg_global_path xs -> P xs) -> (forall xs, fair_path_global xs -> global_valid_pathC xs -> 
wfg_global_path xs -> alwaysCG P xs).
Proof.
    intros * Hassum. pcofix CIH. 
    intros xs Hfair Hvalid Hwfgp.
    destruct xs. pfold; constructor; eapply Hassum;try pfold;try constructor;crush;constructor;easy.
    
    pfold; constructor. eapply Hassum;easy. right. 
    eapply CIH;try solve [subtac_tail_solve | subtac_tail_valid].
Qed.

Lemma always_suffix {A:Type}: forall (P : coseq A -> Prop) ys xs, alwaysCG P xs -> is_suffix ys xs -> alwaysCG P ys.
Proof.
    intros.
    induction H0;try easy. eapply IHis_suffix. pinversion H;subst;easy.
Qed.

Definition head_grafting_is p ctx_p gs_p (xs:global_path) := match xs with conil => False
    | cocons (g,l) xs => typ_p_gtth gs_p ctx_p p g /\ usedCtx gs_p ctx_p end.

Definition head_trans_involving_p r (xs:global_path) := match xs with 
    | cocons (_,Some (lcomm p q ell)) _ => p=r \/ q=r
    | _ => False end.

Definition head_grafting_height_le p hgt_bound (u:global_path) := match u with 
    | cocons (g,l) xs => exists ctx'_p gs'_p, typ_p_gtth  gs'_p ctx'_p p g /\ usedCtx gs'_p ctx'_p /\
    gtth_height ctx'_p <= hgt_bound
    | _ => True end.

Definition head_grafting_contains p q (u:global_path) := match u with 
    | cocons (g,l) xs => exists ctx'_p gs'_p, 
    typ_p_gtth gs'_p ctx'_p p g /\ usedCtx gs'_p ctx'_p /\
    ishParts q ctx'_p
    | _ => True end.

Lemma until_suf {A:Type} (P:coseq A -> Prop) (Q: coseq A -> Prop) :
    forall xs, until P Q xs -> Q xs \/ 
    exists a xsuf, is_suffix (cocons a xsuf) xs /\ P (cocons a xsuf) /\ 
    Q xsuf.
Proof.
    intros.
    induction H;try tauto.
    right. destruct IHuntil. exists x, xs. repeat split;try tauto. constructor.
    destr_hyps.
    exists x0, x1. repeat split;try tauto. constructor. easy.
Qed.

Lemma suffix_tail {A:Type}: forall (a:A) xs ys, is_suffix (cocons a ys) xs ->
is_suffix ys xs.
Proof.
    intros.
    dependent induction H. constructor. constructor.
    specialize (IHis_suffix a ys eq_refl).
    constructor. easy.
Qed.

Search ishParts onth.



Lemma gtth_eq_preserves_ishparts1 : forall gx gx' r, gtth_eq gx gx' -> 
ishParts r gx -> ishParts r gx'.
Proof.
    induction gx using gtth_ind_ref;intros.
    {
        inversion H0;try easy.
    }
    {
        inversion H0;subst.
        inversion H1;subst;try constructor.
        eapply Forall2_prop_r in H6;try exact H9;tac_sanitize.
        eapply Forall_prop in H;try exact H9;tac_sanitize.
        econstructor;try exact H4;try easy. eapply H2;easy.
    }
Qed.

Lemma gtth_eq_preserves_ishparts : forall gx gx' r, gtth_eq gx gx' -> 
ishParts r gx <-> ishParts r gx'.
Proof.
    split;intros;[| eapply gtth_eq_sym in H ]; 
    eapply gtth_eq_preserves_ishparts1;try exact H;try easy.
Qed.

Lemma gtth_eq_preserves_wfgtth1 : forall a b, gtth_eq a b -> wfgtth a -> wfgtth b.
Proof. induction a using gtth_ind_ref.
    {
        intros. inversion H;subst;constructor.   
    }
    {
        intros;inversion H0;subst.  inversion H1;subst. constructor.
        eapply SList_by_Forall2;try exact H4. eapply Forall2_mono;try exact H6.
        intros. simpl in H2. destruct H2;try tauto;destr_hyps. right. 
        exists (x0,x1), (x0,x2). tauto.

        eapply Forall_forall;intros;destruct x;try tauto;right;eapply in_some_implies_onth in H2;destr_hyps.
        eapply  Forall2_prop_l in H6;try exact H2;tac_sanitize. exists x1, x3;split;try tauto.
        eapply Forall_prop in H;try exact H5;tac_sanitize. eapply H3; try exact H8;try easy.

        eapply Forall_prop in H7;try exact H5;tac_sanitize;easy.
    }
Qed.

Lemma gtth_eq_preserves_wfgtth : forall a b, gtth_eq a b -> (wfgtth a <-> wfgtth b).
Proof. 
    split;intros;[| eapply gtth_eq_sym in H ]; 
    eapply gtth_eq_preserves_wfgtth1;try exact H;try easy.
Qed.

(*
Lemma gtth_eq_preserves_gtth_normal1 : forall p gx gx', gtth_eq gx gx' -> gtth_normal_p p gx -> gtth_normal_p p gx'.
Proof.
    intros p.
    induction gx using gtth_ind_ref;intros.
    {
        inversion H;subst. constructor. easy.   
    }
    {
        inversion H0;subst.
        inversion H1;subst.
        {
            constructor 1;intros;eapply H2; eapply gtth_eq_preserves_ishparts;try exact H0;try easy.   
        }
        {
            constructor 2;try easy; eapply gtth_eq_preserves_ishparts with (r:=p) in H0; try exact H4. 
            rewrite <- H0;easy.

            eapply Forall_forall;intros. destruct x;try tauto; eapply in_some_implies_onth in H2;destr_hyps;try tauto.
            right.
            eapply Forall2_prop_l in H6;try exact H2;tac_sanitize.
            eapply Forall_prop in H;try exact H4;tac_sanitize.
            inversion H1;subst;try easy.
            exists x0, x3. repeat split;try tauto;
            [
            apply gtth_eq_sym in H10;
            rewrite gtth_eq_preserves_ishparts;try exact H10
            | eapply H3;try easy];
            
            eapply Forall_prop in H15;try exact H4;destruct H15;destr_hyps;try easy;inversion H;subst;try easy.
            destruct H11;subst;try easy.
        }
        {
            destruct H4;subst;try easy;try constructor 3;try tauto.
            eapply Forall_forall;intros;destruct x;try tauto;eapply in_some_implies_onth in H2;destr_hyps;try tauto.
            right.
            eapply Forall2_prop_l in H6;try exact H2;tac_sanitize.
            eapply Forall_prop in H;try exact H4;tac_sanitize.
            exists x0, x3. repeat split;try tauto.
            eapply H3;try easy. inversion H1;subst;try easy. eapply Forall_prop in H7;try exact H4.
            destruct H7;try easy. destr_hyps. inversion H5;subst;try easy.
            destruct H8;subst;try easy;
            try solve [
            eapply Forall_prop in H10;try exact H4;destruct H10;try easy;
            destr_hyps;inversion H5;subst;easy].

            eapply Forall_prop in H10;try exact H4; destruct H10;try easy.
            destr_hyps;inversion H;subst;easy.


            eapply Forall_forall;intros;destruct x;try tauto;eapply in_some_implies_onth in H2;destr_hyps;try tauto.
            right.
            eapply Forall2_prop_l in H6;try exact H2;tac_sanitize.
            eapply Forall_prop in H;try exact H4;tac_sanitize.
            exists x0, x3. repeat split;try tauto.
            eapply H3;try easy. inversion H1;subst;try easy. eapply Forall_prop in H7;try exact H4.
            destruct H7;try easy. destr_hyps. inversion H5;subst;try easy.
            destruct H8;subst;try easy;
            try solve [
            eapply Forall_prop in H10;try exact H4;destruct H10;try easy;
            destr_hyps;inversion H5;subst;easy].

            eapply Forall_prop in H10;try exact H4; destruct H10;try easy.
            destr_hyps;inversion H;subst;easy.
            
        }
    }
Qed.
*)

Lemma multigraft_prefix_means_ispart: forall gx_p gs_p gx_q gs_q p q g, 
typ_p_gtth gs_p gx_p p g -> typ_p_gtth gs_q gx_q q g -> 
is_tree_proper_prefix gx_q gx_p ->
ishParts q gx_p.
Proof.
    induction gx_p using gtth_ind_ref;intros * Htypp Htypq Hpref;
    
        destruct Htypq as [?Htypq [?Htypq ?Htypq]];
        destruct Htypp as [?Htypp [?Htypp ?Htypp]].
    {
        inversion Hpref.
    }
    {
        rename H into IH.
        inversion Hpref;subst.
        inversion Htypq;subst.
        eapply Forall_prop in Htypq1;try exact H1;destruct Htypq1;try easy.
        destr_hyps. destruct H;[|destruct H]; inversion H;subst;inversion Htypp;subst;
        try constructor.
        assert(Hqn: q0 <> p) by (red;intros;subst;subtac_triv_isparts_false).

        assert(Hqn0: q0 <>q) by (red;intros;subst;subtac_triv_isparts_false).


        assert(Hpn: p0 <> p) by (red;intros;subst;subtac_triv_isparts_false).

        assert(Hpn0: p0 <>q) by (red;intros;subst;subtac_triv_isparts_false).

        inversion Htypp;subst.
        eapply slist_implies_some in H5;destr_hyps;rename x into ell.
        eapply Forall2_prop_r in H6;try exact H;tac_sanitize.
        eapply Forall_prop in IH;try exact H;tac_sanitize.
        inversion Htypq;subst.
        eapply Forall2_prop_l in H10;try exact H3;tac_sanitize.
        econstructor 3;try exact H;try easy.
        eapply H2 with (gs_p:=gs_p) (gs_q:=gs_q) (p:=p0) (gx_q:=x4) (g:=x5);
        eapply Forall2_prop_r in H1;try exact H5;tac_sanitize;rewrite H in H6;
        inversion H6;subst;try easy;repeat split;try easy;
        intros; 
        [eapply Htypp0 | eapply Htypq0]; econstructor;try exact H;try exact H5;try easy.
    }
Qed.

Lemma multigraft_gtth_eq_means_notpart : forall gx_p gs_p gx_q gs_q p q g, 
typ_p_gtth gs_p gx_p p g -> typ_p_gtth gs_q gx_q q g -> 
gtth_eq gx_q gx_p ->
ishParts q gx_p -> False.
Proof.
    intros * Htypp Htypq Heq Hishparts.
    
    eapply gtth_eq_preserves_ishparts in Hishparts;try exact Heq.
    red in Htypq;tauto.
Qed.

Variant gtth_normal_l (p:part): gtth -> Prop :=
    | gtth_normal_l_not_part: forall gx, (ishParts p gx -> False) -> gtth_normal_l p gx
    | gtth_normal_l_head : forall xs s t, (s=p \/ t=p) -> 
    gtth_normal_l p (gtth_send s t xs) 
    | gtth_normal_l_child: forall s t xs, s <> p -> t <> p -> 
    Forall (fun u=>u=None \/ exists s g, u=Some (s,g) /\ ishParts p g) xs -> gtth_normal_l p (gtth_send s t xs).
    

Inductive gtth_normal_p (p:part) : gtth -> Prop := 
    | gtth_normal_hol : forall n, gtth_normal_p p (gtth_hol n)
    | gtth_normal_send : forall s t gxs, gtth_normal_l p (gtth_send s t gxs) ->
    Forall (fun u=> u=None \/ exists s g, u=Some (s,g) /\ gtth_normal_p p g) gxs ->
    gtth_normal_p p (gtth_send s t gxs).


Lemma eventually_suffix2 {A:Type}: forall (P : coseq A -> Prop) xs ys, 
eventually P ys -> is_suffix ys xs -> eventually P xs.
Proof.
    intros * Hev.
    induction Hev. intros. rewrite eventually_P_iff_P_suffix. exists xs0;easy.

    intros. eapply IHHev. eapply suffix_tail;try exact H.
Qed.

Lemma gtth_eq_preserves_gtth_normal_l : forall p gx gx', gtth_eq gx gx' 
-> gtth_normal_l p gx -> gtth_normal_l p gx'.
Proof.
    intros * Heq Hnorm.
    inversion Hnorm;subst. constructor. intros. eapply gtth_eq_preserves_ishparts in H0;try exact Heq;tauto.

    destruct H;subst;inversion Heq;subst;constructor 2;tauto.

    inversion Heq;subst.
    constructor 3;try easy. eapply Forall_forall;intros;destruct x;try tauto.
    eapply in_some_implies_onth in H2;destr_hyps.
    right. eapply Forall2_prop_l in H6;try exact H2;tac_sanitize.
    eapply Forall_prop in H1;try exact H4;tac_sanitize.
    exists x0, x3. split;try tauto. eapply gtth_eq_preserves_ishparts;try exact H3.
    eapply gtth_eq_sym;try easy.
Qed.


Lemma gtth_eq_preserves_gtth_normal1 :  forall p gx gx', gtth_eq gx gx' 
-> gtth_normal_p p gx -> gtth_normal_p p gx'.
Proof.
    intros p. induction gx using gtth_ind_ref.
    {
        intros. inversion H;subst. constructor.   
    }
    {
        intros * Heq Hnormal.
        inversion Heq;subst. constructor.
        inversion Hnormal;subst.   
        eapply gtth_eq_preserves_gtth_normal_l;try exact H2;try easy.
        eapply Forall_forall;intros;destruct x;try tauto;destr_hyps;right.
        eapply in_some_implies_onth in H0;try easy;destr_hyps.
        eapply Forall2_prop_l in H4;try exact H0;tac_sanitize.
        eapply Forall_prop in H;try exact H2;tac_sanitize.
        exists x0, x3;split;try easy.
        eapply H1;try easy.
        inversion Hnormal;subst.
        eapply Forall_prop in H7;try exact H2;tac_sanitize; easy.
    }
Qed.

Lemma gtth_eq_preserves_gtth_normal :  forall p gx gx', gtth_eq gx gx' -> gtth_normal_p p gx <-> gtth_normal_p p gx'.
Proof.
    intros;split;intros;eapply gtth_eq_preserves_gtth_normal1;try exact H0;
    try easy;eapply gtth_eq_sym;try easy.
Qed.

Lemma gtth_normal_l_gtth_eq : forall gx_p gx_q  g gs_p gs_q p q,
typ_p_gtth gs_p gx_p p g ->
usedCtx gs_p gx_p ->
typ_p_gtth gs_q gx_q q g ->
usedCtx gs_q gx_q ->
gtth_eq gx_p gx_q ->
gtth_normal_l q gx_p.
Proof.
    intros.
    apply gtth_eq_sym in H3.
    constructor 1;intros.
    eapply multigraft_gtth_eq_means_notpart in H3;try exact H;try exact H1;try easy.
Qed.

Lemma gtth_normal_l_gtth_prefix: forall gx_p gx_q  g gs_p gs_q p q,
wfgC g -> projectableA g ->
typ_p_gtth gs_p gx_p p g ->
typ_p_gtth gs_q gx_q q g ->
is_tree_proper_prefix gx_q gx_p ->
gtth_normal_l q gx_p.
Proof.
    induction gx_p using gtth_ind_ref;
        intros * Hwfg Hprojable  Htypp  Htypq  Hpref.
    {
        inversion Hpref.   
    }
    {
        rename p into s, q into t, p0 into p, q0 into q.
        eapply multigraft_prefix_means_ispart in Hpref as Hishparts; try exact Htypp;
        try exact Htypq.
        pose proof Htypp as Htypp'.
        pose proof Htypq as Htypq'.
        destruct Htypp as [?Htypp [?Htypp ?Htypp]].
        destruct Htypq as [?Htypq [?Htypq ?Htypq]].
        destruct (Nat.eq_dec q s);
        destruct (Nat.eq_dec q t);subst.
        {
            inversion Htypp;subst; eapply wfgC_triv in Hwfg;try easy.   
        }
        {
            constructor 2;tauto.   
        }
        {
            constructor 2;tauto.   
        }
        {
            constructor 3;try easy.
            eapply Forall_forall;intros. destruct x;try tauto;right;eapply in_some_implies_onth in H0;destr_hyps.
            inversion Htypp;subst.

            inversion Htypq;subst.
            {
                eapply Forall_prop in Htypq1;try exact H1;destruct Htypq1;try easy;destr_hyps.
                destruct H2;[| destruct H2];inversion H2;subst;try easy.    
            }
            rename xs0 into xsq, xs into xsp.
            eapply Forall2_prop_r in H7;try exact H0;tac_sanitize.
            exists x1, x2;split;try easy.
            eapply Forall_prop in H;try exact H0. destruct H;try easy;destr_hyps.
            inversion H;subst;clear H.
            eapply Forall2_prop_l in H9;try exact H3;tac_sanitize.
            inversion Hpref;subst.
            eapply Forall2_prop_r in H7;try exact H2;tac_sanitize.
            rewrite H0 in H9;inversion H9;subst;clear H9.
            assert (Htypp2: typ_p_gtth gs_p x7 p x6).
            {
                repeat split;try easy;intros;
                            eapply Htypp0;econstructor 3;try exact H0;try easy;red;
                            intros;subst;subtac_triv_isparts_false. 
            }

            assert (Htypq2: typ_p_gtth gs_q x3 q x6).
            {
                repeat split;try easy;intros;
                            eapply Htypq0;econstructor 3;try exact H2;try easy;red;
                            intros;subst;subtac_triv_isparts_false. 

            }
            eapply H1 with (q:=q) (p:=p) (g:=x6) (gs_p:=gs_p) (gs_q:=gs_q) in H10 as Ih_used;try easy;
            subtac_onth_solver.
            eapply multigraft_prefix_means_ispart in H10;try exact Htypp2;try exact Htypq2;try easy.
        }

    }
Qed.


Lemma not_part_means_normal : forall p gx, (~ ishParts p gx) -> gtth_normal_p p gx.
Proof.
    intros p. induction gx using gtth_ind_ref;intros.
    constructor.
    rename H into IH, H0 into H.
    destruct (Nat.eq_dec p p0);
    destruct (Nat.eq_dec p q);subst;try easy;
    try solve [exfalso;eapply H;try constructor].
    econstructor 2;
    [constructor; easy |].

    eapply Forall_forall;intros;destruct x;try tauto.
    eapply in_some_implies_onth in H0;destr_hyps.
    eapply Forall_prop in IH;try exact H0;destruct IH;try easy;destr_hyps.
    inversion H1;subst;right. exists x0, x1. split;try tauto.
    eapply H2.
    red;intros. eapply H. econstructor 3;try exact H0;try easy.
Qed.

Lemma gtth_normal_by_typ: forall gx_p gs_p  p q g xsp, 
wfgC g ->
projectableA g ->
(projectionC g p (ltt_send q xsp) \/ projectionC g p (ltt_recv q xsp)) ->
typ_p_gtth gs_p gx_p p g ->
usedCtx gs_p gx_p ->
gtth_normal_p q gx_p.
Proof.
    induction gx_p using gtth_ind_ref;
        intros * Hwfg Hprojable Hprojp Htypp Husedp.
    {
        constructor.     
    }
    {
        rename p into s, q into t, p0 into p, q0 into q.

        destruct Hprojp as [Hprojp | Hprojp].
        {
            pose proof Htypp as Htypp'. destruct Htypp' as [?Htypp [?Htypp ?Htypp]].
            inversion Htypp0;subst.
            assert (Hispartsq:isgPartsC q (gtt_send s t ys)) by 
                (eapply proj_contains_q_implies_part_send in Hprojp;try easy).
                eapply balanced_to_tree in Hispartsq;try easy.
                destruct Hispartsq as [gx_q [gs_q [?Htypq [?Htypq [?Htypq Husedq]]]]].
                assert (Htyp_q: typ_p_gtth gs_q gx_q q (gtt_send s t ys)) by (repeat split;try easy).
                specialize (Hprojable q) as Hprojq. destruct Hprojq as [Tq Hprojq].
                eapply multigrafting_lemma_send with (p:=p) (q:=q) in Hprojp as Hmg;
                try exact Htypp; try exact Htyp_q;try exact Hprojq;
                try easy.
            destruct Hmg.
            {
                constructor. eapply gtth_normal_l_gtth_prefix with (p:=p);
                try exact Htypp;try exact Htyp_q;try easy.
                assert (Hneq1: s <> p) by (red;intros;subst;subtac_triv_isparts_false).
                assert (Hneq2: t <> p) by (red;intros;subst;subtac_triv_isparts_false).
                eapply Forall_forall;intros;destruct x;try tauto;right.
                eapply in_some_implies_onth in H1;destr_hyps.
                eapply  Forall_prop in H;try exact H1.
                destruct H;try easy;destr_hyps;inversion H;subst;clear H.
                exists x0, x1. split;try tauto.
                eapply Forall2_prop_r in H6;try exact H1;tac_sanitize.
                inversion Husedp;subst.
                eapply Forall2_prop_l in H10;try exact H1;tac_sanitize.
                eapply mergeCtx_onth_subset in H3;try exact H8.
                eapply H2 with (g:=x5) (xsp:=xsp) (gs_p:=x1) (p:=p);try easy; subtac_onth_solver.
                pinversion Hprojp;subst;try apply proj_mon;try easy.
                eapply Forall2_prop_r in H17;try exact H4;tac_sanitize.
                destruct H15;try easy. eapply merge_inv_ss in H10;try exact H18;subst;tauto.

                repeat split;try easy.
                eapply decidable_helper.typh_with_less;try exact H6;try easy.
                intros.
                eapply Htypp1. econstructor 3;try exact H1;try easy.
                eapply Forall_subset;try exact H3;try easy;tauto.
            }
            {
                eapply gtth_eq_sym in H0.
                assert (Hnishparts: ~ ishParts q (gtth_send s t xs)) by 
                (
                red;intros;eapply multigraft_gtth_eq_means_notpart in H0; try exact Htypp;try exact Htyp_q;
                try easy).

                assert (Hneq1: s <> p) by (red;intros;subst;subtac_triv_isparts_false).
                assert (Hneq2: t <> p) by (red;intros;subst;subtac_triv_isparts_false).
                constructor. constructor;try easy.
                
                eapply Forall_forall;intros;destruct x;try tauto;eapply in_some_implies_onth in H1;destr_hyps.
                right. eapply Forall_prop in H;try exact H1;destruct H;try easy.
                destr_hyps.
                inversion H;subst;clear H.
                exists x0, x1. split;try tauto.

                inversion Husedp;subst.
                eapply Forall2_prop_r in H6;try exact H1;tac_sanitize.
                eapply Forall2_prop_l in H9;try exact H1;tac_sanitize.
                eapply mergeCtx_onth_subset in H7;try exact H3.
                eapply H2 with (g:=x5) (xsp:=xsp) (gs_p:=x1) (p:=p);try easy; subtac_onth_solver.
                pinversion Hprojp;subst;try apply proj_mon;try easy.
                eapply Forall2_prop_r in H17;try exact H4;tac_sanitize.
                destruct H15;try easy. eapply merge_inv_ss in H10;try exact H18;subst;tauto.

                repeat split;try easy.
                eapply decidable_helper.typh_with_less;try exact H6;try easy.
                intros.
                eapply Htypp1. econstructor 3;try exact H1;try easy.
                eapply Forall_subset;try exact H7;try easy;tauto.
                
            }
            
        }
        {
            pose proof Htypp as Htypp'. destruct Htypp' as [?Htypp [?Htypp ?Htypp]].
            inversion Htypp0;subst.
            assert (Hispartsq:isgPartsC q (gtt_send s t ys)) by 
                (eapply proj_contains_q_implies_part_recv in Hprojp;try easy).
                eapply balanced_to_tree in Hispartsq;try easy.
                destruct Hispartsq as [gx_q [gs_q [?Htypq [?Htypq [?Htypq Husedq]]]]].
                assert (Htyp_q: typ_p_gtth gs_q gx_q q (gtt_send s t ys)) by (repeat split;try easy).
                specialize (Hprojable q) as Hprojq. destruct Hprojq as [Tq Hprojq].
                eapply multigrafting_lemma_recv with (p:=p) (q:=q) in Hprojp as Hmg;
                try exact Htypp; try exact Htyp_q;try exact Hprojq;
                try easy.
            destruct Hmg.
            {
                constructor. eapply gtth_normal_l_gtth_prefix with (p:=p);
                try exact Htypp;try exact Htyp_q;try easy.
                assert (Hneq1: s <> p) by (red;intros;subst;subtac_triv_isparts_false).
                assert (Hneq2: t <> p) by (red;intros;subst;subtac_triv_isparts_false).
                eapply Forall_forall;intros;destruct x;try tauto;right.
                eapply in_some_implies_onth in H1;destr_hyps.
                eapply  Forall_prop in H;try exact H1.
                destruct H;try easy;destr_hyps;inversion H;subst;clear H.
                exists x0, x1. split;try tauto.
                eapply Forall2_prop_r in H6;try exact H1;tac_sanitize.
                inversion Husedp;subst.
                eapply Forall2_prop_l in H10;try exact H1;tac_sanitize.
                eapply mergeCtx_onth_subset in H3;try exact H8.
                eapply H2 with (g:=x5) (xsp:=xsp) (gs_p:=x1) (p:=p);try easy; subtac_onth_solver.
                pinversion Hprojp;subst;try apply proj_mon;try easy.
                eapply Forall2_prop_r in H17;try exact H4;tac_sanitize.
                destruct H15;try easy. eapply merge_inv_ss in H10;try exact H18;subst;tauto.

                repeat split;try easy.
                eapply decidable_helper.typh_with_less;try exact H6;try easy.
                intros.
                eapply Htypp1. econstructor 3;try exact H1;try easy.
                eapply Forall_subset;try exact H3;try easy;tauto.
            }
            {
                eapply gtth_eq_sym in H0.
                assert (Hnishparts: ~ ishParts q (gtth_send s t xs)) by 
                (
                red;intros;eapply multigraft_gtth_eq_means_notpart in H0; try exact Htypp;try exact Htyp_q;
                try easy).

                assert (Hneq1: s <> p) by (red;intros;subst;subtac_triv_isparts_false).
                assert (Hneq2: t <> p) by (red;intros;subst;subtac_triv_isparts_false).
                constructor. constructor;try easy.
                
                eapply Forall_forall;intros;destruct x;try tauto;eapply in_some_implies_onth in H1;destr_hyps.
                right. eapply Forall_prop in H;try exact H1;destruct H;try easy.
                destr_hyps.
                inversion H;subst;clear H.
                exists x0, x1. split;try tauto.

                inversion Husedp;subst.
                eapply Forall2_prop_r in H6;try exact H1;tac_sanitize.
                eapply Forall2_prop_l in H9;try exact H1;tac_sanitize.
                eapply mergeCtx_onth_subset in H7;try exact H3.
                eapply H2 with (g:=x5) (xsp:=xsp) (gs_p:=x1) (p:=p);try easy; subtac_onth_solver.
                pinversion Hprojp;subst;try apply proj_mon;try easy.
                eapply Forall2_prop_r in H17;try exact H4;tac_sanitize.
                destruct H15;try easy. eapply merge_inv_ss in H10;try exact H18;subst;tauto.

                repeat split;try easy.
                eapply decidable_helper.typh_with_less;try exact H6;try easy.
                intros.
                eapply Htypp1. econstructor 3;try exact H1;try easy.
                eapply Forall_subset;try exact H7;try easy;tauto.
                
            }
            
        }
        
    }
Qed.

Lemma q_still_in_gttstepH : forall q gx s t ell gx',  gttstepH gx s t ell gx' ->
wfgtth gx ->
ishParts q gx ->
gtth_normal_p q gx ->
s <> q -> t <> q -> ishParts q gx' .
Proof.
    intros q.
    set (P gx s t (ell : nat) gx' := 
    wfgtth gx ->
ishParts q gx ->
gtth_normal_p q gx ->
s <> q -> t <> q -> ishParts q gx').
    assert (forall s t ell gx  gx', gttstepH gx s t ell gx' -> P gx s t ell gx').
    {
        eapply gttstepH_ind_ref;unfold P in *.
        {
            intros. inversion H0.
        }
        {
            intros * Honth  Hwfgth Hispartsq Hnormal Hneq1 Hneq2.
            inversion Hnormal;subst;try tauto.
            eapply Forall_prop in H3;try exact Honth. destruct H3;try easy. destr_hyps.

            inversion H;subst;clear H.
            inversion H1;subst;try easy. destruct H2;subst;try tauto.
            eapply Forall_prop in H6;try exact Honth;destruct H6;try easy. destr_hyps. inversion H;subst;easy.
        }
        {
            
            intros * _ . intros * Hneq1 Hneq2 Hneq3 Hneq4 Hneq5 Hfa2  Hwfgth Hispartsq Hnormal Hneq6 Hneq7.
            destruct (Nat.eq_dec q p);destruct (Nat.eq_dec q0 q);subst;try easy;try solve [constructor].

            inversion Hwfgth;subst.
            eapply slist_implies_some in H1;destr_hyps. destruct x0. 
            rename x into ell, s0 into sr, g into gh, H into Honth, H3 into Hwfa. 
            eapply Forall2_prop_r in Hfa2;try exact Honth;tac_sanitize.
            econstructor 3;try exact H1;try easy. eapply H2;try easy.
            eapply Forall_prop in Hwfa;try exact Honth;destruct Hwfa;destr_hyps;inversion H;try easy.
            inversion Hnormal;subst;try easy.
            inversion H3;subst;try easy. destruct H0;subst;try tauto.
            eapply Forall_prop in H8;try exact Honth;destruct H8;try easy;destr_hyps; inversion H;subst;try easy.

            inversion Hnormal;subst.
            eapply Forall_prop in H5;try exact Honth;destruct H5;try easy;destr_hyps; inversion H;subst;try easy.
        }
        {
            intros * _ Heq1 Heq2 IH Hwfgth Hparts Hnormal Hneq1 Hneq2.
            apply gtth_eq_sym in Heq2.
            rewrite gtth_eq_preserves_ishparts;try exact Heq2. eapply IH;try easy.
            1-3:
            apply gtth_eq_sym in Heq1.
            erewrite gtth_eq_preserves_wfgtth;try exact Heq1;try easy.

            erewrite gtth_eq_preserves_ishparts;try exact Heq1;try easy.

            erewrite gtth_eq_preserves_gtth_normal;try exact Heq1;try easy.
        }
    }
    intros. specialize (H s t ell gx gx' H0). unfold P in H. eapply H;try easy.
Qed.
    

Lemma q_still_in_grafting_after_step : forall ctx_p gs_p ctx'_p gs'_p p q s ell t g g',
wfgC g -> projectableA g ->
typ_p_gtth gs_p ctx_p  p g ->
gtth_normal_p q ctx_p ->
ishParts q ctx_p -> gttstepC g g' s t ell -> s <> q -> t <> q -> t <> p -> s <> p ->
 typ_p_gtth gs'_p ctx'_p  p g' -> ishParts q ctx'_p.
Proof.
    intros * Hwfg Hprojable Hgraftp Hnorm Hishparts Hstep ?Hneq ?Hneq ?Hneq ?Hneq Hgraftp'.
    
    eapply gttstepH_consistent in Hstep as Hgstep;try exact Hgraftp;try exact Hgraftp';try easy;
    try solve [eapply wfgC_after_step in Hstep;try easy].
    eapply q_still_in_gttstepH;try exact Hgstep;try easy.
    red in Hgraftp;destr_hyps. eapply typ_gtth_means_wfgtth in H;try easy.
Qed.

Lemma gttstepH_height_strict_l  : forall ell  s t gx gx', 
    gttstepH gx s t ell gx' -> 
    wfgtth gx ->
    (forall q,
    (q=s \/ q=t) ->
    ishParts q gx ->
    gtth_normal_p q gx ->
    gtth_height gx' < gtth_height gx).
Proof.
    set (P gx (s t ell : nat) gx' := 
    wfgtth gx ->
    forall q, q=s \/ q=t -> ishParts q gx -> gtth_normal_p q gx ->
     gtth_height gx' < gtth_height gx).
    assert (forall s t ell gx  gx', gttstepH gx s t ell gx' -> P gx s t ell gx').
    {
        eapply gttstepH_ind_ref;unfold P in *.
        { 
            intros * _ Hwfgth  * Heq Hishparts Hnormal. inversion Hishparts.
        }
        {
            intros * Honth Hwfgth  * Heq Hishparts Hnormal.
            eapply gtth_height_ge_children with (k:= gtth_height g) (p:=p) (q:=q) in Honth;lia.   
        }
        {
            intros * _ * Hneq1 Hneq2 Hneq3 Hneq4 Hneq5 Hfa2 Hwfgth r Heq Hishparts Hnorm.
            eapply gtth_height_lt_by_forall2;[inversion Hwfgth;easy | ].
            eapply Forall2_forall; try solve [apply Forall2_length in Hfa2;try easy].
            intros.
            destruct (onth k xs) eqn:Honthxs.
            {
                right. eapply Forall2_prop_r in Hfa2;try exact Honthxs;tac_sanitize.
                exists x0, x1, x2. repeat split;try tauto.
                eapply H2 with (q:=r);try easy.
                {
                    inversion Hwfgth;subst;eapply Forall_prop in H5;try exact Honthxs;destruct H5;try easy.
                    destr_hyps. inversion H;subst;try easy.
                }
                {
                    inversion Hnorm;subst. inversion H3;subst;try easy.
                    destruct H0;subst;tauto.
                    eapply Forall_prop in H8;try exact Honthxs;destruct H8;try easy.
                    destr_hyps. inversion H;subst;try easy. 
                }   
                {
                    inversion Hnorm;subst. 
                    eapply Forall_prop in H5;try exact Honthxs;tac_sanitize;easy.
                }
            }
            {
                left. destruct (onth k ys) eqn:Hyg;try tauto. 
                eapply Forall2_prop_l in Hfa2;try exact Hyg;tac_sanitize.
                rewrite H0 in Honthxs. easy.
                   
            }
                
        }
        {
            intros * _ Heq1 Heq2 IH Hwfg q Heq Hishparts Hnorm.
            eapply gtth_eq_sym in Heq1.
            eapply gtth_eq_preserves_wfgtth in Hwfg as Hwfgb;try exact Heq1.
            specialize (IH Hwfgb).
            eapply gtth_eq_mon_gtth_height in Heq1 as Hgeq1.
            
            eapply gtth_eq_mon_gtth_height in Heq2 as Hgeq2.
            rewrite <- Hgeq2. rewrite <- Hgeq1.
            
            eapply IH with (q:=q);try easy.
            eapply gtth_eq_preserves_ishparts;try exact Heq1;try easy.
            eapply gtth_eq_preserves_gtth_normal;try exact Heq1;try easy.
        }
    }
    intros.
    specialize (H s t ell gx gx'). unfold P in *. eapply H with (q:=q);try easy.
Qed.
    
Lemma graft_height_decreases_strictly : 
                 forall (gs : list (option gtt)) (gx : gtth) (p : opt_lbl) q 
                (g' g : gtt) (s t ell : opt_lbl) gx' gs',
                wfgC g ->
                projectableA g ->
                p <> s ->
                p <> t ->
                (q=s \/ q=t) ->
                ishParts q gx ->
                gtth_normal_p q gx ->
                typ_p_gtth gs gx p g ->
                gttstepC g g' s t ell ->
                typ_p_gtth gs' gx' p g' ->
                gtth_height gx' < gtth_height gx.
Proof.
    intros * Hwfg Hprojable Hneq1 Hneq2 Heq Hishparts Hnorm Htypp Hstep Htypp'.
    assert (Hwfg' : wfgC g') by (eapply wfgC_after_step in Hstep;try easy).
    eapply gttstepH_consistent in Hstep;try exact Htypp;try exact Htypp';try easy.
    eapply gttstepH_height_strict_l;try exact Hstep;try exact Heq;try easy.
    red in Htypp. destr_hyps.
    eapply typ_gtth_means_wfgtth;try exact H.
Qed.


Definition head_helper_prop p q hgt_bound (u :global_path) :=   match u with 
    | cocons (g,l) xs => exists ctx'_p gs'_p, typ_p_gtth  gs'_p ctx'_p p g /\ usedCtx gs'_p ctx'_p /\
    gtth_height ctx'_p <= hgt_bound /\ ishParts q ctx'_p
    | _ => True end.


Lemma head_trans_preconds :  forall ctx_p p lcs q gs_p xs hgt_bound, 
fair_path_global xs -> 
global_valid_pathC xs ->  wfg_global_path  xs ->
head_grafting_is p ctx_p gs_p xs -> 
ishParts q ctx_p ->
head_proj_is p (ltt_recv q lcs) xs ->
gtth_height ctx_p <= hgt_bound ->
weak_untilC (    
head_helper_prop p q hgt_bound /1\ head_trans_not_involving_p p /1\
head_trans_not_involving_p q /1\ head_proj_is_nil_true p (ltt_recv q lcs)
)
(head_trans_involving_p q) xs.
Proof.
    intros * Hfair Hvalid Hwfgp Hgraft Hishparts Hprojp Hle.
    generalize dependent gs_p.
    generalize dependent ctx_p.
    generalize dependent xs.
    pcofix CIH.
    
    destruct xs.
    {
        intros. red in Hprojp. easy.
    }
    {
        intros.
        destruct p0 as [g l].
        assert(Hwfg : wfgC g) by
        (eapply wfg_global_path_head;try exact Hwfgp).
        assert(Hprojable : projectableA g) 
        by (pinversion Hwfgp;subst; red in H1;tauto).   
        destruct l.
        {
            pose proof Hvalid as Hvalid'.
            pinversion Hvalid;try apply valid_path_mon;subst.
            destruct l;try easy.
            rename n into s, n0 into t, n1 into ell.
            pfold.
            destruct (Nat.eq_dec s q);
            destruct (Nat.eq_dec t q);subst;try tauto;red in H3;
            try solve [
                pinversion H3;try apply step_mon;tauto |
                constructor 1;simpl;tauto].

            destruct (Nat.eq_dec s p);
            destruct (Nat.eq_dec t p);subst;try tauto;red in H3.
            {
                pinversion H3;try apply step_mon;tauto.   
            }
            {
                eapply proj_cont_pq_step in H3 as Hlocals;try easy.
                red in Hprojp. 
                destr_hyps.
                eapply proj_inj in H;try exact Hprojp;try easy.
            }
            {
                
                eapply proj_cont_pq_step in H3 as Hlocals;try easy.
                red in Hprojp. 
                destr_hyps.
                eapply proj_inj in H0;try exact Hprojp;try easy.
                inversion H0;subst.
                constructor 1. simpl. tauto. 
            }
            {
            simpl in Hgraft;destruct Hgraft as [?Hgraft ?Hgraft];                rename x into g'.
            constructor 2.
            split;[split | ];[split | |];simpl;
            try solve [
            exists ctx_p, gs_p;tauto |
            intros;
            destruct H;subst;tauto | simpl in Hprojp;easy].

                
                right.
                assert (Hispartsp :isgPartsC p g).
                {
                    simpl in Hprojp; eapply proj_contains_q_implies_part_recv in Hprojp;try easy.   
                }
                
                assert (Hispartsq :isgPartsC q g).
                {
                    simpl in Hprojp; eapply proj_contains_q_implies_part_recv in Hprojp;try easy.   
                }
                eapply part_after_step_r_redux in H3 as Hispartsp';try exact Hispartsp;try easy.
                assert (Hwfg' : wfgC g') by (eapply wfgC_after_step in H3;try easy).
                eapply balanced_to_tree in Hispartsp' as Hgraftp';try easy.
                destruct Hgraftp' as [ctx_p' [gs_p'  [?Hgraftp' [?Hgraftp' [?Hgraftp' ?Hgraftp']]]]]. 
                
                assert(Htypp': typ_p_gtth gs_p' ctx_p' p g') by (red;tauto).
                eapply graft_height_after_step in H3 as Hgraftn; try exact Hgraft;
                try exact Htypp';try easy.
                 
                eapply CIH with (ctx_p:=ctx_p') (gs_p:=gs_p');try solve 
                [subtac_tail_solve | subtac_tail_valid].
                simpl.
                simpl in Hprojp.
                eapply typ_after_step_r_redux in H3;try exact Hprojp;try easy. destr_hyps;subst;easy.
                assert(Hnormal: gtth_normal_p q ctx_p).
                {
                    eapply gtth_normal_by_typ;try exact Hgraft;try easy.
                    simpl in Hprojp. right. exact Hprojp.   
                }
                eapply q_still_in_grafting_after_step;try exact H3;try exact Hgraft;try exact H;try easy.
                all:crush.                
            }
        }
        {
            pinversion Hvalid;try apply valid_path_mon;subst.
            pfold.
            constructor 2; try easy.
            split;[split |];[split | |];simpl;try solve
            [exists ctx_p, gs_p;crush];try easy.
            
            left. pfold. constructor 3. easy.    
        }
    }
Qed.

Lemma local_step_hneq_helper_1: forall ctx_p gs_p p q g g' ell, 
    wfgC g -> typ_p_gtth gs_p ctx_p p g ->
    ishParts q ctx_p ->  gttstepC g g' p q ell -> False.
Proof.
    induction ctx_p using gtth_ind_ref;
    intros * Hwfg Htypp Hishparts Hstep;try solve [inversion Hishparts].
    pinversion Hstep;subst;try apply step_mon.
    {
        destruct Htypp as [?Htypp [?Htypp ?Htypp]].
        inversion Htypp;subst.
        subtac_triv_isparts_false.   
    }
    {
            destruct Htypp as [?Htypp [?Htypp ?Htypp]].
        inversion Htypp;subst.
        inversion Hishparts;subst;try easy.
        eapply Forall2_prop_r in H16;try exact H15;tac_sanitize.
        eapply Forall2_prop_r in H7;try exact H10;tac_sanitize.
        eapply Forall_prop in H;try exact H15;tac_sanitize.
        destruct H16;try easy.
        eapply H7 with (gs_p:=gs_p);try exact H;try easy.
        subtac_wfg_by_onth.
        repeat split;try easy.
        intros;eapply Htypp0. econstructor 3;try exact H15;try easy. 
    }
Qed.

Lemma local_step_hneq_helper_2: forall ctx_p gs_p p q g g' ell, 
    wfgC g -> typ_p_gtth gs_p ctx_p p g ->
    ishParts q ctx_p ->  gttstepC g g' q p ell -> False.
Proof.
    induction ctx_p using gtth_ind_ref;
    intros * Hwfg Htypp Hishparts Hstep;try solve [inversion Hishparts].
    pinversion Hstep;subst;try apply step_mon.
    {
        destruct Htypp as [?Htypp [?Htypp ?Htypp]].
        inversion Htypp;subst.
        subtac_triv_isparts_false.   
    }
    {
        destruct Htypp as [?Htypp [?Htypp ?Htypp]].
        inversion Htypp;subst.
        inversion Hishparts;subst;try easy.
        eapply Forall2_prop_r in H16;try exact H15;tac_sanitize.
        eapply Forall2_prop_r in H7;try exact H10;tac_sanitize.
        eapply Forall_prop in H;try exact H15;tac_sanitize.
        destruct H16;try easy.
        eapply H7 with (gs_p:=gs_p);try exact H;try easy.
        subtac_wfg_by_onth.
        repeat split;try easy.
        intros;eapply Htypp0. econstructor 3;try exact H15;try easy. 
    }
Qed.

Lemma forall_local_step : forall ctx_p p gs_p xs, 
fair_path_global xs -> 
global_valid_pathC xs ->  wfg_global_path  xs ->
head_grafting_is p ctx_p gs_p xs -> 
 (head_proj_eventually_takes_step p) xs .
Proof.
    induction ctx_p using gtth_ind_by_height.
    Print head_proj_eventually_takes_step.
    
    rename H into IH.

    
    intros * Hfair Hvalid Hwfgp Hgraft. destruct xs;try easy.
    
    destruct p0 as [g l].
    red in Hgraft. destr_hyps. red in H. destr_hyps. 
    rename H into Hgraft_p, H1 into Hishparts, H2 into Hgraft_pfa, H0 into Hused.

    assert (Hwfg : wfgC g) by (eapply wfg_global_path_head;try exact Hwfgp;easy); 
    assert (Hprojable : projectableA g) by
    (eapply projable_global_path_head; try exact Hwfgp;easy).
    specialize (Hprojable p) as Hprojp. destruct Hprojp as [Tp Hprojp].
    assert(Hgraftp_p : typ_p_gtth gs_p ctx_p p g) by (red;crush).
    destruct Tp.
    {
        intros;split;intros;subst;try eapply proj_inj in H;try exact Hprojp;easy.   
    }
    {
        rename n into q, l0 into lcs.
        assert (Hispartsq:isgPartsC q g) by (eapply proj_contains_q_implies_part_recv in Hprojp;easy).
        specialize (Hprojable q) as Hprojq. destruct Hprojq as [Tq Hprojq].
        eapply balanced_to_tree in Hispartsq as Hgraftq; try easy.
        destruct Hgraftq as [ctx_q [gs_q [?Htypq [?Htypq [?Htypq ?Htypq]]]]];try easy.
        assert(Htyp_q : typ_p_gtth gs_q ctx_q q g) by (red;crush).
        eapply multigrafting_lemma_recv with (p:=p) (q:=q) (xs:=lcs) (Tq:=Tq) in 
        Hwfg as Hmg; 
        try exact Htyp_q;try exact Hgraftp_p;try easy.
        destruct Hmg.
        {
            destruct Tq.
            {
                exfalso; eapply pmergeCR_s;try exact Hprojq;easy.
            }
            {
                rename n into r, l0 into lcqs.
                assert(Hnt: eventually (headComm_global r q) (cocons (g,l) xs)).
                {
                    eapply IH with (gh':=ctx_q) (gs_p:=gs_q) (p:=q) in Hfair as IH_use;try easy.
                    red in IH_use.
                    specialize (IH_use _ Hprojq). eapply IH_use. reflexivity.

                    eapply proper_prefix_height_le;try easy.
                    eapply typ_gtth_means_wfgtth;try exact Htypq.
                    eapply typ_gtth_means_wfgtth;try exact Hgraft_p.
                }
                assert(Hnt' : eventually (head_trans_involving_p q) (cocons (g,l) xs)).
                {
                    eapply eventually_P_iff_P_suffix in Hnt as Hnt_suf.
                    destruct Hnt_suf as [xsuf [?Hntsuf ?Hntsuf]].
                    red in Hntsuf0.
                    destruct xsuf;try easy.
                    destruct p0;destruct o;try easy. destruct l0;try easy.
                    destruct Hntsuf0;subst.
                    rewrite eventually_P_iff_P_suffix. 
                    exists (cocons (g0, Some (lcomm n n0 n1)) xsuf).
                    split;try easy. simpl;tauto.
                }
                eapply head_trans_preconds with (ctx_p:=ctx_p)
                (gs_p:=gs_p) (p:=p) (q:=q) (lcs:=lcs) in Hfair as Hwft;try easy;
                try solve [simpl; exists lcs; easy |
                eapply grafting_contains_prefix;try exact H;
                try exact Hgraftp_p;try exact Htyp_q;try easy].
                eapply weak_untilC_to_until in Hwft;try exact Hnt;try easy. 

              
                assert(Hev' : 
                eventually (head_helper_prop p q (gtth_height ctx_p) /1\     
                 head_proj_is p (ltt_recv q lcs) /1\             
                 head_trans_involving_p q) (cocons (g,l) xs)).
                 {
                    eapply until_suf in Hwft as Hunt_suf.
                    destruct Hunt_suf.
                    {
                        constructor 1. split;try easy. simpl;split;try easy. 
                        exists ctx_p, gs_p. crush.
                        eapply grafting_contains_prefix;try exact H; try exact Htyp_q;
                        try exact Hgraftp_p;try easy.       
                    }
                    {
                        destruct H0 as [unthead [untsuf Hsuf]].
                        destruct Hsuf as [?Hsuf [?Hsuf ?Hsuf_t] ].
                        destruct Hsuf0 as [[?Hsuf  ?Hsuf] ?Hsuf].
                        rewrite eventually_P_iff_P_suffix. exists untsuf.
                        repeat split.
                        {
                            eapply suffix_tail;try exact Hsuf.
                        }
                        {
                            assert(Hvalid_suf: global_valid_pathC (cocons unthead untsuf)).
                            {
                                eapply valid_suffix_valid_global;try exact Hvalid;try easy.   
                            }
                            pinversion Hvalid_suf;subst;try apply valid_path_mon.
                            simpl in Hsuf_t;try easy.
                            red in H3;destruct l0;try easy.
                            rename n into s, n0 into t, n1 into ell.
                            simpl in Hsuf0, Hsuf1, Hsuf2.
                            simpl.
                            destr_hyps.
                            rename x1 into gs'_p, x0 into ctx'_p.
                            assert (Hwfgy: wfgC y /\ projectableA y).
                            {
                                eapply always_P_implies_P_suffix in Hwfgp;try exact Hsuf.
                                pinversion Hwfgp;subst. simpl in H9. easy.   
                            }
                            destruct Hwfgy as [Hwfgy Hprojabley].
                            Ltac triv_ineq_solver := red;intros;subst;tauto.
                            assert (Hispartsy : isgPartsC p y).
                            {
                                eapply proj_contains_q_implies_part_recv in Hsuf2;try easy.
                            }
                            assert (Hispartsp': isgPartsC p x).
                            {
                                eapply part_after_step_r_redux with (r:=p) in H3;try solve 
                                [triv_ineq_solver | easy].
                            }
                            assert (Hwfgx: wfgC x) by (eapply wfgC_after_step in H3;try easy).
                            eapply balanced_to_tree in Hispartsp';try easy.
                            destruct Hispartsp' as [ctx''_p [gs''_p [?Hgraftp'' [?Hgraftp'' [?Hgraftp'' ?Hgraftp'']]]]].
                            assert (Hgraft_p'': typ_p_gtth gs''_p ctx''_p p x) by (red;tauto).
                            eapply graft_height_after_step in H3  as Hgstep;try exact H0;try exact Hgraft_p'';
                            try solve [easy | triv_ineq_solver].
                            exists ctx''_p, gs''_p.
                            repeat split;try solve [tauto | lia].

                            eapply q_still_in_grafting_after_step; try exact H0;
                            try exact Hgraft_p'';try exact H3;try solve [triv_ineq_solver | easy].
                            assert(Hnorm: gtth_normal_p q ctx'_p).
                            {
                                eapply gtth_normal_by_typ with (xsp:=lcs);try exact H0;try easy;try tauto.   
                            }
                            easy.
                        }
                        {
                            assert(Hvalid_suf: global_valid_pathC (cocons unthead untsuf)).
                            {
                                eapply valid_suffix_valid_global;try exact Hvalid;try easy.   
                            }
                            simpl.
                            destruct Hsuf0 as [?Hsuf ?Hsuf].
                            destruct unthead.
                            simpl in Hsuf0, Hsuf1, Hsuf2, Hsuf3.
                            destruct o;try easy;
                            try solve [
                                pinversion Hvalid_suf;try apply valid_path_mon;
                                subst; simpl in Hsuf_t;easy].
                                destruct l0;
                                try solve [
                                pinversion Hvalid_suf;try apply valid_path_mon;
                                subst; simpl in Hsuf_t;easy].
                            pinversion Hvalid_suf;try apply valid_path_mon;subst.
                            red in H4.
                            simpl. eapply typ_after_step_r_redux in H4;try exact Hsuf2;try easy.
                            destr_hyps;subst;easy.
                            1-2:
                            red in Hwfgp;
                            rewrite always_P_iff_P_suffix in Hwfgp;
                            specialize (Hwfgp _ Hsuf);simpl in Hwfgp;tauto.
                            1-2:simpl in Hsuf3, Hsuf1;red;intros;subst;tauto.
                        }
                        {
                            easy.   
                        }
                    }
                 }

                 rewrite eventually_P_iff_P_suffix in Hev'. destr_hyps.
                 rename x into xsuf.
                 assert (Hvalid' : global_valid_pathC xsuf) by
                 (eapply valid_suffix_valid_global;try exact H0;try easy).
                 pose proof H2 as Hht.
                 pinversion Hvalid';try apply valid_path_mon;subst;simpl in H2;try easy.
                 destruct l0;try easy. red in H5.
                 
                simpl in H1. destr_hyps.
                rename H0 into Hsuf, x0 into ctx_p', x1 into gs_p', H5 into Hstep.


                assert (Hwfgy: wfgC y /\ projectableA y).
                {
                    eapply always_P_implies_P_suffix in Hwfgp;
                    try exact Hsuf.
                    pinversion Hwfgp;subst. simpl in H9. easy.   
                }
                destruct Hwfgy as [Hwfgy Hprojabley].
                simpl in H3. rename H3 into Hprojyp.
                assert (Hispartsy : isgPartsC p y).
                {
                    eapply proj_contains_q_implies_part_recv in Hprojyp;try easy.
                }
                
                assert(Hpneq1 : p <> n).
                {
                    red;intros; symmetry in H0;subst.
                    destruct H2;subst.
                    red in H1. destr_hyps;tauto.            
                    eapply local_step_hneq_helper_1 in Hstep;try exact H1;try easy.
                }
                
                assert(Hpneq2 : p <> n0).
                {   
                    red;intros;symmetry in H0;subst.
                    destruct H2;subst.
                    eapply local_step_hneq_helper_2 in Hstep;try exact H1;try easy.

                    red in H1. destr_hyps. tauto.   
                }


                assert (Hispartsp': isgPartsC p x).
                {
                    eapply part_after_step_r_redux with (r:=p) in Hstep;try solve 
                    [triv_ineq_solver | easy].
                }
                assert (Hwfgx: wfgC x) by (eapply wfgC_after_step in Hstep;try easy).

                eapply balanced_to_tree in Hispartsp';try easy.
                destruct Hispartsp' as [ctx''_p [gs''_p [?Hgraftp'' [?Hgraftp'' [?Hgraftp'' ?Hgraftp'']]]]].
                assert (Hgraft_p'': typ_p_gtth gs''_p ctx''_p p x) by (red;tauto).
                assert (Hnormq: gtth_normal_p q ctx_p').
                {
                    eapply gtth_normal_by_typ with (q:=q) (xsp:=lcs) in H1;try easy;try tauto.
                }

                eapply graft_height_decreases_strictly with (q:=q) 
                in Hstep as Hnew_height; try exact H1;try exact Hgraft_p'';try easy;try solve [
                    destruct H2;subst;tauto
                ].
                
                assert (Hsuf2: is_suffix (cocons (x, l') xs0) (cocons (g, l) xs)) by
                (eapply suffix_tail; try exact Hsuf).
                
                assert(head_grafting_is p ctx''_p gs''_p (cocons (x, l') xs0)).
                {
                    simpl. tauto.   
                }
                
                eapply IH in H0; try easy;rename H0 into Hev3.
                assert (Hprojinv: projectionC x p (ltt_recv q lcs)).
                {
                    simpl in Hprojyp.
                    eapply typ_after_step_r_redux in Hstep;try exact Hprojyp;destr_hyps;subst;try easy.
                }
                simpl in Hev3.
                specialize (Hev3 _ Hprojinv).
                destruct Hev3 as [Hsend Hrec].
                specialize (Hrec _ _ eq_refl) as Himp.
                simpl;intros.
                eapply proj_inj in H0;try exact Hprojp;subst;try easy.
                split;intros;try easy.
                inversion H0;subst.
                

                + eapply eventually_suffix2;try exact Himp;try easy.
                + lia.
                + eapply always_suffix;try exact Hfair;try easy.
                
                + eapply always_suffix;try exact Hwfgp;try easy.
            }
            admit.
        }
        {
            intros;split;intros;subst;eapply proj_inj in Hprojp as Hprjinj;try exact H0;try easy.
            inversion Hprjinj;subst;clear Hprjinj;clear H0.
            eapply multigrafting_lemma_1_recv with (xs:=lcs) (Tq:=Tq) (p:=p) (q:=q) in Hgraftp_p as 
            Hprojq2;try exact Hgraft_p;
            try exact Htyp_q;try easy.
            destruct Hprojq2;subst.
            pinversion Hfair;subst.
            eapply matching_proj_enables_step in Hprojp as Hstep;try exact Hprojq;try easy.
            destruct Hstep as [g' [ell Hstep]].
            eapply projection_step_label in Hstep as Hslabel;try exact Hprojp;try exact Hprojq;try easy.
            destruct Hslabel as [s [s' [Tq' [Tp' [?Hslabel ?Hslabel]]]]].
            red in H2.
            eapply H2 with (n:=ell). simpl. exists g'. easy.
        }
    }
    admit.
Admitted.
    

Lemma liveness_global : forall g, wfgC g -> projectableA g -> live_type_global g.
Proof.
    intros * Hwfg Hprojable.
    red;intros;red;intros;red;intros.
    rewrite always_P_iff_P_suffix. intros.
    assert (Hys_valid: global_valid_pathC ys) by admit.
    destruct ys. red. intros;simpl;tauto.
    destruct p as [g'' l'].
    red;intros;split;intros;simpl in H3.
    {
        destr_hyps.     
        eapply forall_local_step with (p:=p) in Hys_valid as Hloc_step.
        simpl in Hloc_step.
        1-3:admit.
        eapply proj_contains_q_implies_part_send in H3;destr_hyps.
        simpl.