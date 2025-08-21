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
    | stepH_hol : forall n m p q ell, 
    gttstepH (gtth_hol n)  p q ell (gtth_hol m) 
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
    (gtth_send s t ghs').
(*non-constructive
Lemma gttstepH_consistent: forall gx gs r p q ell g g' gx' gs', 
    r <> p ->
    r <> q ->
    wfgC g ->
    typ_p_gtth gs gx r g -> 
    usedCtx gs gx ->
    wfgC g' ->
    gttstepC g g' p q ell ->
    typ_p_gtth gs' gx' r g' -> 
    usedCtx gs' gx' -> gttstepH gx  p q ell gx'.
Proof.
    induction gx using gtth_ind_ref.
    {
        intros * Hner1 Hner2 Hwfg Htyp Hused Hwfg' Hstep Htyp' Hused'.
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
        intros * Hner1 Hner2 Hwfg Htyp Hused Hwfg' Hstep Htyp' Hused'.
        destruct Htyp as [?Htyp [?Htyp ?Htyp]].
        destruct Htyp' as [?Htyp' [?Htyp' ?Htyp']].
        inversion Htyp;subst.
        rename xs into ghs, ys into gcs.
        pinversion Hstep;subst;try easy;try apply step_mon.
        {
            symmetry in H10.
            eapply Forall2_prop_l in H6;try exact H10;tac_sanitize.
            econstructor 2;try easy.

        }
    } 
*)    

Lemma Forall3_prop1 {A:Type} {B:Type} {C:Type}: forall P ell (xs : list (option A))
(ys : list (option B)) 
(zs : list (option C)) a, onth ell xs= Some a -> Forall3 P xs ys zs ->
exists b c, onth ell ys = b /\ onth ell zs = c /\ P (Some a) b c.
Proof.
    intros P ell xs.
    revert ell.
    induction xs.
    {  
        intros. rewrite onth_nil in H. easy.
    }
    {
        intros.
        destruct ell.
        {
            simpl in H;subst.
            inversion H0;subst. exists b ,c. repeat split;simpl;easy.
        }
        {
            simpl in H.
            inversion H0;subst.
            eapply IHxs in H7;try exact H.
            destruct H7 as [b' [c' [Honb [Honc Pbc]]]].
            exists b', c'.
            repeat split;simpl;try easy.   
        }
    }
Qed.


Lemma Forall3_prop2 {A:Type} {B:Type} {C:Type}: forall P ell (xs : list (option A))
(ys : list (option B)) 
(zs : list (option C)) b, onth ell ys= Some b -> Forall3 P xs ys zs ->
exists a c, onth ell xs = a /\ onth ell zs = c /\ P a (Some b) c.
Proof.
    intros P ell xs ys.
    revert ell xs.
    induction ys.
    {  
        intros. rewrite onth_nil in H. easy.
    }
    {
        intros.
        destruct ell.
        {
            simpl in H;subst.
            inversion H0;subst. exists a ,c. repeat split;simpl;easy.
        }
        {
            simpl in H.
            inversion H0;subst.
            eapply IHys in H7;try exact H.
            destruct H7 as [b' [c' [Honb [Honc Pbc]]]].
            exists b', c'.
            repeat split;simpl;try easy.   
        }
    }
Qed.

Lemma Forall3_prop3 {A:Type} {B:Type} {C:Type}: forall P ell (xs : list (option A))
(ys : list (option B)) 
(zs : list (option C)) c, onth ell zs= Some c -> Forall3 P xs ys zs ->
exists a b, onth ell xs = a /\ onth ell ys = b /\ P a b (Some c).
Proof.
    intros P ell xs ys zs.
    revert ell xs ys.
    induction zs.
    {  
        intros. rewrite onth_nil in H. easy.
    }
    {
        intros.
        destruct ell.
        {
            simpl in H;subst.
            inversion H0;subst. exists a ,b. repeat split;simpl;easy.
        }
        {
            simpl in H.
            inversion H0;subst.
            eapply IHzs in H7;try exact H.
            destruct H7 as [b' [c' [Honb [Honc Pbc]]]].
            exists b', c'.
            repeat split;simpl;try easy.   
        }
    }
Qed.


                Lemma Forall3_length {A B C : Type}: forall P (xs : list (option A)) 
                (ys : list (option B)) (zs : list (option C)), Forall3 P xs ys zs -> Datatypes.length xs = Datatypes.length ys /\
                Datatypes.length ys = Datatypes.length zs.
                Proof.
                    intros P;
                    induction xs;intros;inversion H;subst;[simpl | split;eapply IHxs in H6;destr_hyps;simpl];lia.
                Qed.

(*constructive*)
 Lemma gttstepH_consistent: forall gx gs r p q ell g g', 
    r <> p ->
    r <> q ->
    wfgC g ->
    projectableA g ->
    typ_p_gtth gs gx r g -> 
    usedCtx gs gx ->
    wfgC g' ->
    gttstepC g g' p q ell ->
    exists gs' gx',
    typ_p_gtth gs' gx' r g' /\ 
    usedCtx gs' gx' /\ gttstepH gx  p q ell gx'.
Proof.
    induction gx using gtth_ind_ref.
    {
        intros * Hner1 Hner2 Hwfg Hprojable Htyp Hused Hwfg' Hstep.
        assert(Hispartsr: isgPartsC r g).
        {
            destruct Htyp as [?Htyp [?Htyp ?Htyp]].
            inversion Htyp;subst;
            eapply Forall_prop in Htyp1;try exact H1;
            destruct Htyp1;try easy;destr_hyps.
            destruct H;[| destruct H];inversion H;subst;try solve [
            try eapply decidable_helper.triv_pt_p; try eapply decidable_helper.triv_pt_q;
            easy]. eapply no_step_from_end in Hstep;try easy.
        }
        eapply part_after_step_r_redux in Hstep as Hprt;try exact Hispartsr;try easy.
        eapply balanced_to_tree in Hprt;try easy.
        destr_hyps.
        exists x0 , x.
        repeat split;try easy.
        rename x into gx', x0 into gs'.
        destruct gx';try constructor.

        destruct Htyp as [?Htyp [?Htyp ?Htyp]].
        inversion Htyp;subst.
        eapply Forall_prop in Htyp1;try exact H5. destruct Htyp1;try easy.
        destr_hyps.
        destruct H3;[|destruct H3];inversion H3;subst;
        try solve
        [
            pinversion Hstep;try apply step_mon;subst;try easy;
            inversion H;subst;
            subtac_triv_isparts_false |
            inversion H;subst;
            eapply no_step_from_end in Hstep;try easy
        ].
    }
    {
        intros * Hner1 Hner2 Hwfg Hprojable Htyp Hused Hwfg' Hstep .
        destruct Htyp as [?Htyp [?Htyp ?Htyp]].
        inversion Htyp;subst.
        rename xs into ghs, ys into gcs.
        pinversion Hstep;subst;try easy;try apply step_mon.
        {
            symmetry in H10.
            eapply Forall2_prop_l in H6;try exact H10;tac_sanitize.
            inversion Hused;subst.
            eapply Forall2_prop_l in H8;try exact H1;tac_sanitize.
            eapply mergeCtx_onth_subset in H6;try exact H2.
            eapply decidable_helper.typh_with_less in H3 as Htyp2;try exact H7;try easy.
            exists x3, x5.
            repeat split;try easy.
            intros. eapply Htyp0. eapply ha_sendr;try exact H1;try easy.
            eapply Forall_subset;try exact H6;try easy;try tauto.
            econstructor 2;try easy;try exact H1.   
        }
        {
            rename ys into gcs'.
            eapply decidable_helper.ctx_back in Htyp as Hgss.
            destr_hyps.
            rename H0 into Hgss3,x into gss, H1 into Hishmerge.
            assert(create_ghs: forall ghs_sbs gcs'_sbs
        
        (Hsubset: Forall2 (fun u v=> u=None /\ v=None \/ (exists k, onth k ghs=u /\ onth k gcs' =v)) 
        ghs_sbs gcs'_sbs),
        
        exists ghs' gss' gs', 
        (isMergeCtx gs' gss' \/ (gs'=[] /\ gss' =[])) /\
         Forall3
        (fun (u : option (list (option gtt)))
        (v : option (sort * gtth))
        (w : option (sort * gtt)) =>
        u = None /\ v = None /\ w = None \/
        (exists
        (ct : list (option gtt)) (s0 : sort) (g : gtth) (g' : gtt),
        u = Some ct /\
        v = Some (s0, g) /\
        w = Some (s0, g') /\
        typ_gtth ct g g' /\ usedCtx ct g)) gss' ghs' gcs'_sbs 
        /\
        Forall (fun u=> u=None \/ exists s g, u=Some (s,g) /\ (ishParts r g -> False)) ghs' 
        /\
        Forall
(fun u : option gtt =>
u = None \/
(exists (q1 : opt_lbl) (lsg : list (option (sort * gtt))),
u = Some (gtt_send r q1 lsg) \/
u = Some (gtt_send q1 r lsg) \/ u = Some gtt_end)) gs'
        /\
        Forall2 (fun u v => u=None /\ v=None \/ 
        (exists s g g', u=Some (s,g) /\ v=Some (s,g') /\ gttstepH g p0 q0 ell g')) ghs_sbs ghs').
            {
                induction ghs_sbs.
                intros. 
                {
                    exists [], [], [].
                    inversion Hsubset;subst.
                    repeat split;try tauto;try constructor.
                }
                intros.
                destruct a.
                destruct p1 as [s gh].
                
                assert(exists n,  onth n ghs = Some (s,gh)).
                {
                    assert(Hzero: onth 0 (Some (s,gh)::ghs_sbs)=(Some (s,gh))) by crush.
                    eapply Forall2_prop_r   in Hsubset;try exact Hzero.
                    destr_hyps. destruct H1;try easy.
                    destruct H1 as [k [Honthk_ghs Honthk_gcs']].
                    exists k;easy.
                }
                Search Forall3.
                destruct H0 as [n Honth_ghs].
                eapply Forall2_prop_r in H6;try exact Honth_ghs;tac_sanitize.
                rename x0 into s, x1 into gh, x2 into gc, H2 into Honth_gcs.
                eapply Forall_prop in H;try exact Honth_ghs.
                destruct H;try easy.
                destr_hyps.
                symmetry in H;inversion H;subst;clear H.
                eapply Forall2_prop_r in H16;try exact Honth_gcs;tac_sanitize.
                rename x0 into s, x1 into gc, x2 into gc'.
                destruct H11;try easy.
                eapply Forall3_prop2 in Hgss3;try exact Honth_ghs;tac_sanitize.
                rewrite Honth_gcs in H14;symmetry in H14;inversion H14;subst.
                rename x1 into gs_n, x2 into s, x3 into gh; clear H14.  
                eapply H0 with (r:=r) (gs:=gs_n) in H;try easy;
                try solve [subtac_wfg_by_onth | subtac_projable_by_onth |

                repeat split;try easy;try solve [subtac_ishparts_by_onth |
                    eapply mergeCtx_onth_subset in Hishmerge;try exact H12;
                    eapply Forall_subset;try exact Hishmerge;try easy;tauto]
                ].

                inversion Hsubset;subst.
                destruct H13;try easy. clear H1.
                specialize (IHghs_sbs _ H18). 
                destruct IHghs_sbs as [ghs'_r [gss'_r [gs'_r ]]].
                destruct H as [gs' [gh' [?Htyp' [?Htyp' ?Htyp]]]].
                
                exists (Some (s,gh')::ghs'_r), (Some (gs') :: gss'_r).
                assert (exists gs'_m, isMergeCtx gs'_m (Some gs' :: gss'_r)).
                {
                 Search isMergeCtx.   
                 (* isMergeCtx gs'_m (Some gs' :: gss'_r)
                 given ismergectx gs gss
                 gs' derived from gs_n
                 *)
                }
                evar (gmerge: list (option gtt)).
                exists gmerge.
                (*
                repeat split. admit.
                constructor;try tauto.
                right. exists gs', s, gh', gc'.
                repeat split;try easy. admit.
                unfold typ_p_gtth in Htyp';try tauto.
                constructor. right. exists s, gh'. split;try easy. red in Htyp';tauto.
                tauto. admit.
                constructor;try easy. right.*)
            }
            assert (Hsubs : Forall2
(fun (u : option (sort * gtth))
(v : option (sort * gtt)) =>
u = None /\ v = None \/
(exists k : opt_lbl, onth k ghs = u /\
onth k gcs' = v)) ghs
gcs'). admit.

            specialize (create_ghs _ _ Hsubs).
            destruct create_ghs as [ghs' [gss [gs' [Hishmerge [Hfa3 [Hfa [Hfa_shape Hfa2]]]]]]].
            exists gs', (gtth_send p q ghs').

            repeat split.
            {
                constructor.
                admit.
                eapply Forall2_forall. 
                eapply Forall2_length in Hfa2, Hsubs;lia.
                intros.
                destruct (onth k ghs') eqn:Hyg.
                {
                    right.
                    eapply Forall3_prop2 in Hfa3;try exact Hyg;tac_sanitize.
                    exists x2, x3, x4.
                    repeat split;try easy.
                    eapply decidable_helper.typh_with_more;try exact H13.
                    eapply mergeCtx_onth_subset;try exact Hishmerge;try easy;try exact H2.
                }
                {
                    left.
                    repeat split;try easy.
                    destruct (onth k gcs') eqn:Hyg';try easy.
                    eapply Forall3_prop3 in Hfa3;try exact Hyg'; tac_sanitize.
                    rewrite Hyg in H11;easy.   
                } 
            }
            {
                intros.
                inversion H0;subst;try easy;
                try 
                subtac_triv_isparts_false.
                eapply Forall_prop in Hfa;try exact H17.
                destruct Hfa;try easy;destr_hyps. 
                inversion H1;subst;tauto.
            }
            {
                easy.
            }
            {
                econstructor;try exact Hishmerge.
                eapply Forall2_forall.
                eapply Forall3_length in Hfa3. lia.
                intros.
                destruct (onth k ghs') eqn:Hyg.
                {
                    right.
                    eapply Forall3_prop2 in Hfa3;try exact Hyg;tac_sanitize.
                    exists x1, x2, x3.
                    repeat split;try easy.
                }
                {
                    destruct (onth k gss) eqn:Hyg'. 
                    eapply Forall3_prop1 in Hfa3;try exact Hyg';tac_sanitize.
                    rewrite Hyg in H11;try easy.
                    tauto.   
                }
            }
            {
                constructor;try easy.
            }   
        }
    } 
  
(*
Lemma graft_height_after_step: forall gs gx p g' g s t ell, 
p <> s ->
p <> t ->
typ_p_gtth gs gx p g ->
usedCtx gs gx -> gttstepC g g' s t ell ->
exists  gx' gs',
typ_p_gtth gs' gx' p g' /\
usedCtx gs' gx' /\ (gtth_height gx' <= gtth_height gx).
Proof.
    intros * Hps Hpt [?Htypg [?Htypg ?Htypg]] Husedp Hstep.
    generalize dependent gs. revert Hps Hpt Hstep. 
    generalize dependent g'.
    generalize dependent g.
    generalize dependent gx.
    induction gx using gtth_ind_ref.
    {
        intros.
        inversion Htypg;subst.
        exists (gtth_hol n). exists (extendLis n (Some g')). 
        repeat split;try easy.
        constructor. rewrite extendExtract;easy.
        eapply Forall_forall.
        intros.
        destruct x;try tauto. right.

        apply in_some_implies_onth in H. destr_hyps.
        
        eapply extend_onth_inv in H as ?Ht;subst. rewrite extendExtract in H.
        inversion H;subst.
        eapply Forall_prop in Htypg1;try exact H1;tac_sanitize.
        destruct H0 as [?Htr | [?Htr | ?Htr]];
        inversion Htr;subst;
        pinversion Hstep;try apply step_mon;subst;try tauto;
        exists x, ys;tauto.
        constructor.
    }
    {
        intros.   
        pinversion Hstep;try apply step_mon;subst.
        {
            apply eq_sym in H1.
            inversion Htypg;subst.
            rename xs0 into gcs, xs into ghs.
            eapply Forall2_prop_l in H10;try exact H1;tac_sanitize.
            rename x1 into gh', x2 into g', x0 into s0.

            inversion Husedp;subst.
            eapply Forall2_prop_l in H10;try exact H3;tac_sanitize.
            rename x1 into s0, x2 into gx'.
            exists gx',x0.
            repeat split;
            eapply mergeCtx_onth_subset in H8;try exact H4;
            eapply decidable_helper.typh_with_less in H6;try exact H9;try tauto.
            rename x0 into gs'.
            intros. eapply Htypg0. econstructor 3;try exact H3;try easy.
            eapply Forall_subset with (gs:=gs);try tauto.
            Search gtth_height.
            eapply gtth_height_ge_children  with (p:=s) (q:=t) (k :=gtth_height gx') in H3 as Hge;crush.
            
        }
        {
            inversion Htypg;subst.
            rename xs into ghs, xs0 into gcs.
            evar (gx':list (option (sort * gtth))). evar  (gs':list (list (option gtt))).
            Search isMergeCtx.
            exists  
             assert(create_ghs' : forall ghs1,
             (Hsubset: Forall (fun u=> u=None \/ exists k, onth k ghs=u) ghs1), 
        }
    }
Admitted.
*)

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
    intros * Hps Hpt Hwfg Hprojable Hispartsp [?Htypg [?Htypg ?Htypg]] Husedp Hstep
    [?Htypg' [?Htypg' ?Htypg']] Husedq.
    
    
    eapply part_after_step_r_redux in Hstep as Hisparts';try exact Hispartsp;try easy.
    assert (wfgC g') by (eapply wfgC_after_step;try exact Hstep;try easy).
    eapply balanced_to_tree in Hisparts';try easy. 
        
    generalize dependent gs. revert Hps Hpt Hstep. 
    generalize dependent g'.
    generalize dependent g.
    generalize dependent gx.
    induction gx using gtth_ind_ref.
    {
        intros.
        inversion Htypg;subst.
        exists (gtth_hol n). exists (extendLis n (Some g')). 
        repeat split;try easy.
        constructor. rewrite extendExtract;easy.
        eapply Forall_forall.
        intros.
        destruct x;try tauto. right.

        apply in_some_implies_onth in H. destr_hyps.
        
        eapply extend_onth_inv in H as ?Ht;subst. rewrite extendExtract in H.
        inversion H;subst.
        eapply Forall_prop in Htypg1;try exact H1;tac_sanitize.
        destruct H0 as [?Htr | [?Htr | ?Htr]];
        inversion Htr;subst;
        pinversion Hstep;try apply step_mon;subst;try tauto;
        exists x, ys;tauto.
        constructor.
    }
    {
        intros.   
        pinversion Hstep;try apply step_mon;subst.
        {
            apply eq_sym in H1.
            inversion Htypg;subst.
            rename xs0 into gcs, xs into ghs.
            eapply Forall2_prop_l in H10;try exact H1;tac_sanitize.
            rename x1 into gh', x2 into g', x0 into s0.

            inversion Husedp;subst.
            eapply Forall2_prop_l in H10;try exact H3;tac_sanitize.
            rename x1 into s0, x2 into gx'.
            exists gx',x0.
            repeat split;
            eapply mergeCtx_onth_subset in H8;try exact H4;
            eapply decidable_helper.typh_with_less in H6;try exact H9;try tauto.
            rename x0 into gs'.
            intros. eapply Htypg0. econstructor 3;try exact H3;try easy.
            eapply Forall_subset with (gs:=gs);try tauto.
            Search gtth_height.
            eapply gtth_height_ge_children  with (p:=s) (q:=t) (k :=gtth_height gx') in H3 as Hge;crush.
            
        }
        {
            inversion Htypg;subst.
            rename xs into ghs, xs0 into gcs.
            evar (gx':list (option (sort * gtth))). evar  (gs':list (list (option gtt))).
            Search isMergeCtx.
            exists  
             assert(create_ghs' : forall ghs1,
             (Hsubset: Forall (fun u=> u=None \/ exists k, onth k ghs=u) ghs1), 
        }
    }
Admitted.

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

Lemma graft_height_decreases_strictly : 
                 forall (gs : list (option gtt)) (gx : gtth) (p : opt_lbl) q 
                (g' g : gtt) (s t ell : opt_lbl),
                p <> s ->
                p <> t ->
                (q=s \/ q=t) ->
                ishParts q gx ->
                typ_p_gtth gs gx p g ->
                usedCtx gs gx ->
                gttstepC g g' s t ell ->
                exists (gx' : gtth) (gs' : list (option gtt)),
                typ_p_gtth gs' gx' p g' /\
                usedCtx gs' gx' /\ gtth_height gx' < gtth_height gx.
                Proof.
                Admitted.

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

Lemma q_still_in_grafting_after_step : forall ctx_p gs_p ctx'_p gs'_p p q s ell t g g',
typ_p_gtth gs_p ctx_p  p g ->
ishParts q ctx_p -> gttstepC g g' s t ell -> s <> q -> t <> q -> t <> p -> s <> p ->
 typ_p_gtth gs'_p ctx'_p  p g' -> ishParts q ctx'_p.
Proof.
    intros * Hgraftp Hishparts Hstep ?Hneq ?Hneq ?Hneq ?Hneq Hgraftp'.
Admitted.

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
                eapply graft_height_after_step in H3 as Hgraftn; try exact Hgraft;try easy.
                destr_hyps.
                 
                eapply CIH with (ctx_p:=x) (gs_p:=x0);try solve 
                [subtac_tail_solve | subtac_tail_valid].
                simpl.
                simpl in Hprojp.
                eapply typ_after_step_r_redux in H3;try exact Hprojp;try easy. destr_hyps;subst;easy.
                
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
                            eapply graft_height_after_step in H3  as Hgstep;try exact H0;try easy.
                            destr_hyps. exists  x0, x1;split;try tauto;split;try tauto.
                            split;[crush |]. 
                            eapply q_still_in_grafting_after_step;try exact H0;try exact Hgstep;
                            try exact H7;try exact H3;try easy.
                            all:red;intros;subst;tauto.
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
                
                assert(Hpneq1 : p <> n).
                {
                    red;intros; symmetry in H9;subst.
                    destruct H2;subst.
                    red in H1. destr_hyps;tauto.
                    (*q is in x0 so p,q is not a valid transition*)
                    admit.
                }
                
                assert(Hpneq2 : p <> n0).
                {   
                    red;intros;symmetry in H9;subst.
                    destruct H2;subst.
                    (*ditto*)
                    admit.
                    red in H1;destr_hyps;tauto.
                }
                eapply graft_height_decreases_strictly with (q:=q) 
                in H5 as Hnew_height;try exact H1;try easy;try solve [
                    destruct H2;subst;tauto
                ].
                
                assert (Hsuf2: is_suffix (cocons (x, l') xs0) (cocons (g, l) xs)) by (eapply suffix_tail;try exact H0 ).
                rename x1 into gs'_p, x0 into ctx'_p.
                destr_hyps.
                rename x0 into gx', x1 into gs'.
                assert(head_grafting_is p gx' gs' (cocons (x, l') xs0)).
                {
                    simpl. tauto.   
                }
                
                eapply IH in H12; try easy.
                assert (Hprojinv: projectionC x p (ltt_recv q lcs)).
                {
                    simpl in H3.
                    eapply typ_after_step_r_redux in H5;try exact H3;destr_hyps;subst;try easy.
                    1-2:red in Hwfgp;
                            rewrite always_P_iff_P_suffix in Hwfgp;
                            specialize (Hwfgp _ H0);simpl in Hwfgp;tauto.
                }
                simpl in H12.
                specialize (H12 _ Hprojinv).
                destruct H12.
                specialize (H13 _ _ eq_refl) as Himp.
                simpl;intros.
                eapply proj_inj in H14;try exact Hprojp;subst;try easy.
                split;intros;try easy.
                inversion H14;subst.
                

                Lemma eventually_suffix2 {A:Type}: forall (P : coseq A -> Prop) xs ys, 
                eventually P ys -> is_suffix ys xs -> eventually P xs.
                Proof.
                    intros * Hev.
                    induction Hev. intros. rewrite eventually_P_iff_P_suffix. exists xs0;easy.

                    intros. eapply IHHev. eapply suffix_tail;try exact H.
                Qed.
                eapply eventually_suffix2;try exact Himp;try easy.
                crush.
                eapply always_suffix;try exact Hfair;try easy.
                
                eapply always_suffix;try exact Hwfgp;try easy.
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
    

  