(* From mathcomp Require Import ssreflect.seq all_ssreflect. *)
From Paco Require Import paco pacotac.
From SST Require Import src.expr src.header src.local CpdtTactics src.lcontext.
From SST Require Import src.global src.projection src.part  src.balanced src.merge src.gttreeh src.wfltt.
From SST Require Import lemma.projection lemma.projection_helper lemma.decidable.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations Setoid.
Require Import Coq.Program.Equality.
Import ListNotations.


Definition issubProj (t:ltt) (g:gtt) (p:part) := 
    exists tg, projectionC g p tg /\ subtypeC t tg.

(*Search subtypeC.*)



Definition assoc (g: tctx) (gt:gtt) := 
    forall p, (isgPartsC p gt -> exists Tp, M.find p g=Some Tp /\  
        issubProj Tp gt p) /\
         (~ isgPartsC p gt -> forall Tpx, M.find p g = Some Tpx -> Tpx=ltt_end).

Lemma subtype_end_inv : forall t, subtypeC t ltt_end -> t=ltt_end.
Proof.
    intros.
    destruct t;try easy;
    pinversion H;apply subtype_monotone.
Qed.



Lemma subtype_send_inv1 : forall q xs T, 
subtypeC (ltt_send q xs) T -> exists ys, T=ltt_send q ys.
Proof.
    intros.
    destruct T eqn:Ht;first (apply subtype_end_inv in H; crush);
    destruct (Nat.eq_dec n q);try (exists l);crush;
    pinversion H;crush;apply subtype_monotone.
Qed. 

Lemma subtype_recv_inv1 : forall q xs T, 
subtypeC (ltt_recv q xs) T -> exists ys, T=ltt_recv q ys.
Proof.
    intros.
    destruct T eqn:Ht;first (apply subtype_end_inv in H; crush);
    destruct (Nat.eq_dec n q);try (exists l);crush;
    pinversion H;crush;apply subtype_monotone.
Qed.

Lemma subtype_send_strong_inv: forall pt xs T, 
subtypeC (ltt_send pt xs) T -> 
exists ys, T=ltt_send pt ys /\
Forall2R
(fun u v : option (sort * ltt) =>
u = None \/
(exists (s s' : sort) (t t' : ltt),
u = Some (s, t) /\
v = Some (s', t') /\ subsort s s' /\ subtypeC t t'))
xs ys.
Proof.
    intros.
    pose proof H as H'.
    apply subtype_send_inv1 in H. destr_hyps. subst.
    apply subtype_send_inv in H'. exists x. easy.
Qed.

Lemma subtype_recv_strong_inv: forall pt xs T, 
subtypeC (ltt_recv pt xs) T -> 
exists ys, T=ltt_recv pt ys /\
Forall2R
(fun u v : option (sort * ltt) =>
u = None \/
(exists (s s' : sort) (t t' : ltt),
u = Some (s, t) /\
v = Some (s', t') /\ subsort s s' /\
subtypeC t' t)) ys xs.
Proof.
    intros.
    pose proof H as H'.
    apply subtype_recv_inv1 in H. destr_hyps. subst.
    apply subtype_recv_inv in H'. exists x. easy.
Qed.
(*Search wfG.*)
Lemma empty_not_wfg : forall p q, ~ wfgC (gtt_send p q []).
Proof.
    unfold not;intros. apply wfgC_triv in H. destr_hyps. inversion H0.
Qed.
Ltac invalid_forall_wfg :=
    try ((match goal with | 
    [H:Forall2 _  (?a::?b) [] |- _] => inversion H 
    | [H:Forall2 _  [] (?a::?b)  |- _] => inversion H 
    | [H:Forall2R _ (?a::?b) [] |- _] => inversion H
    | [H:wfgC (gtt_send _ _ []) |- _] => apply empty_not_wfg in H end);
    contradiction).

Lemma onth_exists {A:Type}: forall n (xs: list (option A)) a p, 
onth n xs = Some a -> ~ p (Some a) -> ~ Forall p xs.
Proof.
    unfold not.
    intros.
    generalize dependent n. 
    generalize dependent xs.
    induction xs;intros;[| inversion H1; subst; specialize (IHxs H5)];
    destruct n; crush.
Qed.

Lemma onth_nil {A:Type}: forall n, onth  n ([]:list (option A))= None.
Proof. intros;destruct n;unfold onth in *;crush. Qed.

Lemma projection_implies_part_send :forall g p q xs, 
projectionC g p (ltt_send q xs) -> isgPartsC p g.
Proof.
    intros. pinversion H;subst;crush. apply proj_mon.
Qed.

Lemma projection_implies_part_recv :forall g p q xs, 
projectionC g p (ltt_recv q xs) -> isgPartsC p g.
Proof.
    intros. pinversion H;subst;crush. apply proj_mon.
Qed.

Section subproj_inversion.
Definition send_cond (xs:list (option (sort*ltt))) (ys:list (option (sort*gtt))) (p:part) := 
    Forall2R (fun x y => x=None 
        \/ (exists s elx s' ely, y=Some (s',ely)/\ x=Some (s,elx) /\ 
        subsort s s' /\
        issubProj elx ely p)) xs ys.

Definition subproj_cont_cond (t:ltt) (ys:list(option(sort*gtt))) (p:part) :=
    Forall (fun y=> (y=None)\/ 
    (exists s' Gy, y=Some (s', Gy) /\issubProj t Gy p)) ys.

Definition recv_cond (xs:list (option (sort*ltt))) (ys:list (option (sort*gtt))) (p:part) := 
    Forall2R (fun y x => y=None 
        \/ (exists s elx s' ely, y=Some (s',ely)/\ x=Some (s,elx) /\ 
        subsort s' s /\
        issubProj elx ely p)) ys xs.


Lemma subproj_helper: forall xs ys gs p,  Forall2R
(fun u v : option (sort * ltt) =>
u = None \/
(exists (s s' : sort) (t t' : ltt),
u = Some (s, t) /\
v = Some (s', t') /\ subsort s s' /\ subtypeC t t'))
xs ys -> Forall2
(fun (u : option (sort * gtt)) (v : option (sort * ltt)) =>
u = None /\ v = None \/
(exists (s : sort) (g : gtt) (t : ltt),
u = Some (s, g) /\
v = Some (s, t) /\ upaco3 projection bot3 g p t))
gs ys -> Forall2R
(fun (x : option (sort * ltt)) (y : option (sort * gtt)) =>
x = None \/
(exists (s : sort) (elx : ltt) (s' : sort) (ely : gtt),
y = Some (s', ely) /\
x = Some (s, elx) /\ subsort s s' /\ issubProj elx ely p)) xs gs.
Proof.
    intros xs.
    induction xs; intros; destruct ys;
    destruct gs;try invalid_forall_wfg;crush. constructor. constructor.
    constructor.
    destruct a;crush. right. inversion H. inversion H0. destruct H4;destruct H10;crush.
    exists x2, x4, x3,x0. unfold issubProj. crush. exists x5. destruct H5;crush.
    inversion H;inversion H0;subst. eapply IHxs with (gs:=gs) (ys:=ys);crush.
Qed.
Lemma subproj_helper2:  forall gs p q xs x0  ys, SList xs -> 
subtypeC (ltt_send q xs) (ltt_send q x0) ->
(isMerge (ltt_send q x0) ys \/ ys= [] )->
Forall2R
(fun u v : option (sort * ltt) =>
u = None \/
(exists (s s' : sort) (t t' : ltt),
u = Some (s, t) /\ v = Some (s', t') /\
subsort s s' /\ subtypeC t t')) xs x0 ->
Forall2
(fun (u : option (sort * gtt)) (v : option ltt) =>
u = None /\ v = None \/
(exists (s : sort) (g : gtt) (t : ltt),
u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g p t)) gs
ys ->
Forall
(fun y : option (sort * gtt) =>
y = None \/
(exists (s' : sort) (Gy : gtt),
y = Some (s', Gy) /\
(exists tg : ltt, projectionC Gy p tg /\ subtypeC (ltt_send q xs) tg)))
gs.
Proof.
    induction gs. crush.
    intros.
    destruct ys. inversion H3.
    constructor. 
    {
        inversion H3;subst.
        destruct a;crush.
        right. exists x,x1. crush.
        exists (ltt_send q x0).
        inversion H4;subst;
        destruct H7;crush. 
    }
    {
        eapply IHgs with (x0:=x0) (ys:=ys);crush.
        inversion H4;crush.
        
        inversion H3;crush.
    }        
Qed.
Lemma subproj_inv_send: forall q xs p G, wfgC G -> 
    SList xs -> issubProj (ltt_send q xs) G p -> 
    (exists ys, G=gtt_send p q ys /\ send_cond xs ys p)
    \/ (exists s t ys, G=gtt_send s t ys /\ p <> s /\ p<> t /\ 
        subproj_cont_cond (ltt_send q xs) ys p ).
Proof.
    intros.
    unfold issubProj in H1.
    destr_hyps.
    pose proof H2 as Hsubpr.
    apply subtype_send_strong_inv in H2.
    destruct H2. destruct H2. subst.
    rename H3 into Hsubtpcond.
    (*ltt_send q x0 is the supertype*)
    pinversion H1; try apply proj_mon; subst.
    {
        
        (*G=gtt_send r q xs0*)
        rename H8 into Hprojcond.
        left. exists xs0. split; try reflexivity. subst.
        unfold send_cond.
        destruct xs; destruct xs0;crush;destruct x0;
        try (match goal with | 
            [H:Forall2 _  (?a::?b) [] |- _] => inversion H 
            | [H:Forall2 _  [] (?a::?b)  |- _] => inversion H 
            | [H:wfgC (gtt_send _ _ []) |- _] => apply empty_not_wfg in H end);
        crush.
        apply subproj_helper with(ys:=o1::x0);crush.
    }
    {
        right. exists p0,q0,xs0. unfold subproj_cont_cond. crush. 
        unfold issubProj.
        destruct ys. inversion H7.
        eapply subproj_helper2 with (x0:=x0) (ys:=o::ys);crush.
    }
Qed.

Lemma subproj_helper_recv: forall xs ys gs p,
Forall2R (fun u v => 
(u = None) \/ (exists s s' t t', u = Some(s,t) /\ 
v = Some (s',t') /\ subsort s s' /\ subtypeC t' t)) ys xs
-> Forall2
(fun (u : option (sort * gtt)) (v : option (sort * ltt)) =>
u = None /\ v = None \/
(exists (s : sort) (g : gtt) (t : ltt),
u = Some (s, g) /\
v = Some (s, t) /\ upaco3 projection bot3 g p t))
gs ys -> Forall2R
(fun  (y : option (sort * gtt)) (x : option (sort * ltt)) =>
y = None \/
(exists (s : sort) (elx : ltt) (s' : sort) (ely : gtt),
y = Some (s', ely) /\
x = Some (s, elx) /\ subsort s' s /\ issubProj elx ely p)) gs xs.
Proof.
    intros xs.
    induction xs; intros; destruct ys;
    destruct gs;try invalid_forall_wfg;crush. constructor. constructor.
    constructor. destruct o0;crush. right. 
    inversion H. inversion H0. destruct H4;destruct H10;crush.
    exists x3,x5,x2,x0. unfold issubProj. crush. exists x4. destruct H5;crush.

    inversion H;inversion H0;subst. eapply IHxs with (gs:=gs)(ys:=ys);crush.
Qed.

Lemma subproj_helper_2_recv:  forall gs p q xs x0  ys, SList xs -> 
subtypeC (ltt_recv q xs) (ltt_recv q x0) ->
(isMerge (ltt_recv q x0) ys \/ ys= [] )->
Forall2R (fun u v => (u = None) \/ 
(exists s s' t t', u = Some(s,t) /\ v = Some (s',t') /\ 
subsort s s' /\ subtypeC t' t)) x0 xs ->
Forall2
(fun (u : option (sort * gtt)) (v : option ltt) =>
u = None /\ v = None \/
(exists (s : sort) (g : gtt) (t : ltt),
u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g p t)) gs
ys ->
Forall
(fun y : option (sort * gtt) =>
y = None \/
(exists (s' : sort) (Gy : gtt),
y = Some (s', Gy) /\
(exists tg : ltt, projectionC Gy p tg /\ subtypeC (ltt_recv q xs) tg)))
gs.
Proof.
    induction gs. crush.
    intros.
    destruct ys. inversion H3.
    constructor. 
    {
        inversion H3;subst.
        destruct a;crush.
        right. exists x,x1. crush.
        exists (ltt_recv q x0).
        inversion H4;subst;
        destruct H7;crush. 
    }
    {
        eapply IHgs with (x0:=x0) (ys:=ys);crush.
        inversion H4;crush.
        
        inversion H3;crush.
    }        
Qed.

Lemma subproj_inv_recv: forall q xs p G, wfgC G -> 
    SList xs -> issubProj (ltt_recv q xs) G p -> 
    (exists ys, G=gtt_send q p ys /\ recv_cond xs ys p)
    \/ (exists s t ys, G=gtt_send s t ys /\ p <> s /\ p<> t /\ 
        subproj_cont_cond (ltt_recv q xs) ys p ).
Proof.
    intros.
    unfold issubProj in H1.
    destr_hyps.
    pose proof H2 as Hsubpr.
    apply subtype_recv_strong_inv in H2.
    destruct H2. destruct H2. subst.
    rename H3 into Hsubtpcond.
    pinversion H1; try apply proj_mon; subst.
    {
        
        (*G=gtt_send r q xs0*)
        rename H8 into Hprojcond.
        left. exists xs0. split; try reflexivity. subst.
        unfold send_cond.
        destruct xs; destruct xs0;crush;destruct x0;
        try (match goal with | 
            [H:Forall2 _  (?a::?b) [] |- _] => inversion H 
            | [H:Forall2 _  [] (?a::?b)  |- _] => inversion H 
            | [H:wfgC (gtt_send _ _ []) |- _] => apply empty_not_wfg in H end);
        crush.
        unfold recv_cond.
        apply subproj_helper_recv with(ys:=o1::x0);crush.
    }
    {
        right. exists p0,q0,xs0. unfold subproj_cont_cond. crush. 
        unfold issubProj.
        destruct ys. inversion H7.
        eapply subproj_helper_2_recv with (x0:=x0) (ys:=o::ys);crush.
    }
Qed.

Lemma subtype_end_inv2: forall t:ltt, subtypeC ltt_end t -> t= ltt_end.
Proof.
    intros. pinversion H;crush. apply sub_mon.
Qed.
(*Search projectionC ltt_end.*)
Lemma subproj_inv_end: forall g p, wfgC g -> 
    issubProj ltt_end g p -> isgPartsC p g -> False.
Proof.
    intros. unfold issubProj in H0. destr_hyps. 
    apply subtype_end_inv2 in H2. subst.
    apply pmergeCR with (G:=g) (r:=p);crush.
Qed. 
End subproj_inversion.
(*Print issubProj.*)

Lemma simul_subproj_helper:  forall p q xp xq x0,
Forall2R
(fun (y : option (sort * gtt)) (x : option (sort * ltt)) =>
y = None \/
(exists (s : sort) (elx : ltt) (s' : sort) (ely : gtt),
y = Some (s', ely) /\ x = Some (s, elx) /\
subsort s' s /\ issubProj elx ely q)) x0 xq ->
Forall2R
(fun (x : option (sort * ltt)) (y : option (sort * gtt)) =>
x = None \/
(exists (s : sort) (elx : ltt) (s' : sort) (ely : gtt),
y = Some (s', ely) /\ x = Some (s, elx) /\
subsort s s' /\ issubProj elx ely p)) xp x0
-> Forall2R
(fun u v : option (sort * ltt) =>
u = None \/
(exists (s : sort) (elx : ltt) (s' : sort) (ely : ltt),
u = Some (s, elx) /\ v = Some (s', ely) /\ subsort s s')) xp xq.
Proof.
    induction xp. constructor. 
    intros. destruct xq;destruct x0;crush. inversion H0. inversion H. inversion H0.   
    constructor.
    {
        destruct a;crush. right. inversion H;inversion H0;crush.
        exists x, x1, x4, x5. crush. 
        inversion H0;subst. destruct H8;crush. eapply sstrans with (s2:=x8);crush.
    }
    {
        eapply IHxp with (x0:=x0);crush. inversion H. crush. inversion H0. crush.
    }
Qed.

Definition typ_p_gtth  (gs:list (option gtt)) (ctx:gtth) p G:=
    typ_gtth gs ctx G /\
    (ishParts p ctx -> False) /\
    Forall
    (fun u : option gtt =>
    u = None \/
    (exists (q : opt_lbl) (lsg : list (option (sort * gtt))),
    u = Some (gtt_send p q lsg) \/
    u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) gs.


Lemma wfg_proof_princip2: forall (Q:gtt->Prop) p,
    (forall ctx gs g, typ_p_gtth gs ctx p g -> Q g) -> 
    (forall g, wfgC g -> isgPartsC p g -> Q g).
Proof.
    intros.
    apply balanced_to_tree with (p:=p) in H0 .
    destr_hyps.
    specialize H with (ctx:=x) (gs:=x0) (g:=g).
    unfold typ_p_gtth in *. all:crush.
Qed.
Lemma typ_gtth_cont1: forall gs p q xs gcs s gc n, 
typ_gtth gs (gtth_send p q gcs) (gtt_send p q xs) ->
    onth n xs=Some (s,gc) -> exists gch, onth n gcs = Some (s,gch) /\
    typ_gtth gs gch gc.
Proof.
    intros.
    inversion H;subst.
    
     eapply Forall2_prop_l with (l:=n) (p:=(s,gc))  in H7;
     try assumption.
     destr_hyps. subst. destruct H2;crush. exists x0. crush. 
Qed.


Lemma typ_gtth_cont2: forall gs p q xs gcs s gch n, 
typ_gtth gs (gtth_send p q gcs) (gtt_send p q xs) ->
    onth n gcs = Some (s,gch) -> exists gc, onth n xs=Some (s,gc)   /\
    typ_gtth gs gch gc.
Proof.
    intros.
    inversion H;subst.
     eapply Forall2_prop_r with (l:=n) (p:=(s,gch))  in H7;
     try assumption.
     destr_hyps. subst. destruct H2;crush. exists x1. crush. 
Qed.
 
Lemma typ_p_gtth_cont2:forall gs p q r xs gcs s gch n, 
typ_p_gtth gs (gtth_send p q gcs) r (gtt_send p q xs) ->
    onth n gcs = Some (s,gch) -> exists gc, onth n xs=Some (s,gc)   /\
    typ_p_gtth gs gch r gc.
Proof.
    intros. inversion H. inversion H1. destr_hyps. subst.
    pose proof H0 as H_gcs_gch.
    eapply typ_gtth_cont2 with (xs:=xs) (gs:=gs) (p:=p) (q:=q) in H0;
    try assumption;subst.
    destr_hyps.
    exists x. crush. unfold typ_p_gtth;crush.
    eapply decidable_helper.ishParts_n with (n:=n) (s0:=s) (g:=gch) in H2;try crush.
    
Qed.

Lemma typ_gtth_inv: forall p q gs gcs g, typ_gtth gs (gtth_send p q gcs) g -> exists xs, g= gtt_send p q xs.
Proof.
    intros.
    inversion H;subst. exists ys. reflexivity.
Qed.
Lemma typ_p_gtth_inv: forall p p' q gs gcs g, typ_p_gtth gs (gtth_send p q gcs)  p' g -> exists xs, g= gtt_send p q xs.
Proof.
    intros. inversion H. apply typ_gtth_inv in H0. easy.
Qed.

Lemma continuation_wfgC : forall p q xs s gc n , wfgC (gtt_send p q xs) -> onth n xs=Some (s,gc) -> wfgC gc.
Proof.
    (*Search wfgC.*)
    intros.
    pose proof H as Hwfg.
    apply wfgC_triv in Hwfg.
    apply wfgC_after_step_all in H;try easy.
    eapply Forall_prop with (l:=n) (p:=(s,gc)) in H;try easy.
    destr_hyps. destruct H;try easy. destr_hyps. inversion H;subst;easy.
Qed.
Lemma same_rec_send_not_wfg: forall p xs, ~ wfgC (gtt_send p p xs).
Proof.
    unfold not. intros. apply wfgC_triv in H. easy.
Qed.

Section Forall2_forall.

Variables (A B: Type).
Variable P : option A -> option B -> Prop. 
Lemma Forall2_forall: 
forall  (xs: list (option A)) (ys: list (option B)), 
Datatypes.length xs =Datatypes.length ys -> (forall k, P (onth k xs) (onth k ys)) -> 
Forall2 P xs ys.
Proof.
    induction xs.
    {
        intros. Search Datatypes.length 0.
        simpl in H.
        apply eq_sym in H.
        rewrite length_zero_iff_nil in H. subst. easy.       
    }
    {

        destruct ys as [| y].
        {
            intros. simpl in H. discriminate H.      
        }
        {
            intros. simpl in H. inversion H. constructor.
            specialize (H0 0). simpl in H0. easy.
            eapply IHxs;try easy.
            intros.
            specialize (H0 (S k)).
            simpl in H0. easy.
        }
    }
Qed.
Lemma Forall2R_Forall : forall  (xs: list (option A)) (ys: list (option B)), 
Datatypes.length xs <= Datatypes.length ys -> (forall k, k < Datatypes.length xs -> P (onth k xs) (onth k ys)) -> 
Forall2R P xs ys.
Proof.
    induction xs.
    intros. constructor.

    intros.
    destruct ys as [ | y].
    {
        simpl in H. inversion H.   
    }
    {
        simpl in H. 
        constructor.
        specialize (H0 0). crush.
        eapply IHxs.
        apply le_S_n;easy.
        intros. specialize (H0 (S k)). simpl in H0.
        apply H0.
        apply le_n_S. easy.
    }
Qed.
End Forall2_forall.

Lemma Forall2R_length {A:Type} {B:Type}: forall (P:A -> B-> Prop) xs ys, Forall2R P xs ys -> Datatypes.length xs <= Datatypes.length ys.
Proof.
    intros;
    induction H;crush.
Qed.

Lemma simul_subproj: forall G p q xp xq, wfgC G -> isgPartsC p G ->
    issubProj (ltt_send q xp) G p ->
    issubProj (ltt_recv p xq) G q ->
    SList xp -> SList xq ->
    Forall2R (fun u v => u=None \/ 
    exists s elx s' ely, u=Some (s,elx) /\ 
    v=Some (s',ely)
    /\ subsort s s' 
    ) xp xq.
Proof.
    intros * Hwfg Hisparts Hsubp Hsubq Hsxp Hsxq. 
    eapply balanced_to_tree in Hisparts as Htyp;try easy.
    destruct  Htyp as [ctx [gs [?Htyp [?Htyp [?Htyp _]]]]].
    generalize dependent G.
    generalize dependent gs.
    generalize dependent ctx.
    induction ctx using gtth_ind_ref.
    {
        intros. inversion Htyp;subst.
        eapply Forall_prop in Htyp1;try exact H1;destruct Htyp1;try easy.
        destr_hyps.
        destruct H;[|destruct H];inversion H;subst;
            eapply subproj_inv_send in Hsubp;eapply subproj_inv_recv in Hsubq;try easy;
            destruct Hsubq;destruct Hsubp;destr_hyps;subst;inversion H0;inversion H2;subst;try tauto;
            unfold recv_cond, send_cond in *;
            eapply simul_subproj_helper;try exact H4;try exact H3.
    }
    {
        intros.
        inversion Htyp;subst.
        assert(exists n ss gg, onth n xs=Some (ss,gg)). 
        {
            eapply  slist_implies_some in H5;destr_hyps.
            destruct x0. exists x, s,g;easy.  
        }
        destr_hyps.
        eapply Forall_prop in H;try exact H0;destruct H;try easy;destr_hyps;subst.
        eapply Forall2_prop_r in H6;try exact H0;destr_hyps.
        destruct H3;try easy. destr_hyps;subst;inversion H3;subst;clear H3.
        eapply H1 with (G:=x7) in Htyp1 as Hiuse;try easy;inversion H;subst.
        assert(Hpp: p0 <> p) by  (red;intros;subst;eapply Htyp0;constructor).
        assert(Hqp: q0 <> p) by  (red;intros;subst;eapply Htyp0;constructor).
        intros;eapply Htyp0;econstructor;try exact H0;try easy.
        eapply continuation_wfgC;try exact Hwfg;try exact H4.
        (*Search isgPartsC onth.*)
        red in Hsubp;destr_hyps;eapply subtype_send_inv1 in H3;destr_hyps;subst.
        pinversion H2;subst;try apply proj_mon.
        exfalso;eapply Htyp0;constructor.
        eapply Forall2_prop_r in H15;try exact H4;destr_hyps.
        destruct H7;try easy;destr_hyps;subst.
        symmetry in H7;inversion H7;subst;clear H7.
        (*Search isMerge onth.*)
        eapply merge_inv_ss in H16;try exact H8;subst.
        destruct H13;try easy. pinversion H3;try apply proj_mon;try easy.
        eapply subproj_inv_send in Hsubp;
        destruct Hsubp;destr_hyps;subst;try easy; inversion H2;subst;
        try solve [exfalso;eapply Htyp0;constructor];
        eapply Forall_prop in H8;try exact H4;destruct H8;
        try easy;destr_hyps;subst;inversion H8;subst;easy.

        
        eapply subproj_inv_recv in Hsubq;
        destruct Hsubq;destr_hyps;subst;try easy; inversion H2;subst;
        try solve [exfalso;eapply Htyp0;constructor];
        eapply Forall_prop in H8;try exact H4;destruct H8;
        try easy;destr_hyps;subst;inversion H8;subst;easy.
        easy.
      }
Qed.
    

Lemma assoc_inv_recv: forall p q xs gamma G,
wfgC G ->
SList xs ->
assoc gamma G ->
M.find p gamma =Some  (ltt_recv q xs)  ->
(exists ys : list (option (sort * gtt)),
G = gtt_send q p ys /\ recv_cond xs ys p) \/
(exists (s t : opt_lbl) (ys : list (option (sort * gtt))),
G = gtt_send s t ys /\
p <> s /\ p <> t /\ subproj_cont_cond (ltt_recv q xs) ys p).
Proof.
    intros.
    unfold assoc in *.
    pose proof H as Hwfg.
    apply decidable_isgPartsC with (pt:= p) in H.
    specialize (H1 p).
    
    destr_hyps.
    destruct H.
    eapply H1 in H.
    destr_hyps.
    rewrite H2 in H. inversion H. subst. apply subproj_inv_recv in H4;crush.

    eapply H3 with (Tpx:= (ltt_recv q xs)) in H;crush.
Qed.


Lemma assoc_inv_send: forall p q xs gamma G,
wfgC G ->
SList xs ->
assoc gamma G ->
M.find p gamma =Some  (ltt_send q xs)  ->
(exists ys : list (option (sort * gtt)), G = gtt_send p q ys /\ send_cond xs ys p) \/
(exists (s t : opt_lbl) (ys : list (option (sort * gtt))),
G = gtt_send s t ys /\ p <> s /\ p <> t /\ subproj_cont_cond (ltt_send q xs) ys p).
Proof.
    intros.
    unfold assoc in *.
    pose proof H as Hwfg.
    apply decidable_isgPartsC with (pt:= p) in H.
    specialize (H1 p).
    
    destr_hyps.
    destruct H.
    eapply H1 in H.
    destr_hyps.
    rewrite H2 in H. inversion H. subst. apply subproj_inv_send in H4;crush.

    eapply H3 with (Tpx:= (ltt_send q xs)) in H;crush.
Qed.

Ltac tac_tctx_wf_to_slist xp Htctx_wf Hfindp q := assert (SList xp) by (red in Htctx_wf;eapply Htctx_wf in Hfindp;
    solve [
        apply wfltt_slist_send with (p:=q);easy
        |
        apply wfltt_slist_recv with (p:=q);easy
    ]
        ).


Lemma assoc_simul_inv: 
    forall gamma g p q xp xq, 
    tctx_wf gamma ->
    wfgC g ->
    assoc gamma g ->
    M.find p gamma = Some (ltt_send q xp) -> 
    M.find q gamma = Some (ltt_recv p xq) ->
    (
        exists xg, g=gtt_send p q xg /\
        send_cond xp xg p  /\
        recv_cond xq xg q
    )
    \/
    (
        exists s t xg, g=gtt_send s t xg /\
        p <> s /\ q <> t /\ 
        Forall (fun u=> u=None \/ exists s g, u=Some (s,g) /\ issubProj (ltt_send q xp) g p
        /\ issubProj (ltt_recv p xq) g q
        ) xg
    )
    .
Proof.
    intros * Htctx_wf Hwfg Hassoc Hfindp Hfindq.
    
    tac_tctx_wf_to_slist xp Htctx_wf Hfindp q.
    tac_tctx_wf_to_slist xq Htctx_wf Hfindq p.
    eapply  assoc_inv_send with (G:=g) in Hfindp;try easy.
    eapply  assoc_inv_recv with (G:=g) in Hfindq; try easy.
    destruct Hfindp;destruct Hfindq;crush.
    {

        left.
        exists x0. crush. 
        (*follows from the assumptions*)    
    }
    {
        right. rename x2 into s, x3 into t, x4 into xg. 
        exists s, t, xg. crush.
        eapply Forall_forall.
        intros.
        destruct x2;crush.
        right.
        destruct p0 as [s0 g].
        exists s0, g.
        (*Check Forall_forall.*)
        (*Search In onth.*)
        apply in_some_implies_onth in H7. destruct H7 as [n].
        split;try easy.   
        unfold subproj_cont_cond in H6, H8.
        inversion H3;subst;clear H3.
        split;
        [eapply Forall_prop with (l:=n) (p:=(s0,g)) in H8 |
        eapply Forall_prop with (l:=n) (p:=(s0,g)) in H6]; crush.
    }
Qed.