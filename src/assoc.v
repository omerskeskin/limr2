(* From mathcomp Require Import ssreflect.seq all_ssreflect. *)
From Paco Require Import paco pacotac.
From SST Require Import src.expr src.header src.local CpdtTactics src.lcontext.
From SST Require Import src.global src.projection src.part  src.balanced src.merge src.gttreeh.
From SST Require Import lemma.projection lemma.projection_helper lemma.decidable.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations Setoid.
Require Import Coq.Program.Equality.
Import ListNotations.


Definition issubProj (t:ltt) (g:gtt) (p:part) := 
    exists tg, projectionC g p tg /\ subtypeC t tg.

Search subtypeC.


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
Print gtth.
(*
Definition option_max x y :=
    match (x,y) with 
        | (None, None) => None
        | (Some a, Some b) => Some (max a b)
        | (Some a, None) => Some a
        | (None, Some b) => Some b
    end. 
Fixpoint extract_hs (hs:list (option (sort * gtth))) := 
    match hs with 
        | [] => []
        | None::ys => None::extract_hs ys
        | Some (s,a)::ys => Some a :: extract_hs ys end.
Fixpoint context_height (h:gtth) :=
    match h with 
        | gtth_hol n => Some 0
        | gtth_send p q hs => seq.foldr option_max None (extract_hs hs)
    end.  *)
(* context_height h x means height of h <= x*)
Inductive context_height: gtth -> nat -> Prop :=
    | height_hole: forall n x, context_height (gtth_hol n) x
    | height_send: forall p q hs x, 
        SList hs -> Forall (fun u=> u=None \/ 
            (exists s h, u=Some (s,h) /\ context_height h x)) hs->
        context_height (gtth_send p q hs) (S x).


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
Search wfG.
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
Search projectionC ltt_end.
Lemma subproj_inv_end: forall g p, wfgC g -> 
    issubProj ltt_end g p -> isgPartsC p g -> False.
Proof.
    intros. unfold issubProj in H0. destr_hyps. 
    apply subtype_end_inv2 in H2. subst.
    apply pmergeCR with (G:=g) (r:=p);crush.
Qed. 
End subproj_inversion.
Print issubProj.

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

(*
Lemma wfg_proof_princip: forall (P:gtth -> list (option gtt) -> Prop) (Q:gtt->Prop), 
(forall ctx gs g, 
    P ctx gs ->
    typ_gtth gs ctx g -> Q g) ->
    (forall p ctx gs, good_grafting ctx gs p  -> P ctx gs) -> forall g p,
    wfgC g -> isgPartsC p g -> Q g.
Proof.
    intros.
    apply balanced_to_tree with (p:=p) in H1;crush.
    assert (good_grafting x x0 p). unfold good_grafting. exists g. crush.
    eapply H0 in H5.
    eapply H  with (g:=g) in H5;crush.
Qed.*)

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

Lemma multigrafting_lemma1: forall p q xp xq G gs s t ghs, wfgC G -> 
SList xp -> SList xq ->
issubProj (ltt_send q xp) G p ->
issubProj (ltt_recv p xq) G q ->
typ_p_gtth gs (gtth_send s t ghs) p G ->
s <> p /\ t <> q.
Proof.
    intros.
    inversion H4.
    destr_hyps.
    assert (Hleft:s <> p).
    {
        
        destruct (Nat.eq_dec s p). subst. exfalso. apply H6.
        constructor. easy.
    }
    split. easy.
    {
        destruct (Nat.eq_dec t q);try easy.
        subst.
        apply subproj_inv_recv in H3;
        apply subproj_inv_send in H2;try easy.
        destruct H2;destruct H3;crush;
        apply typ_p_gtth_inv in H4; destr_hyps; 
        [inversion H2 |
         inversion H4];crush.
    }
Qed.

Lemma continuation_wfgC : forall p q xs s gc n , wfgC (gtt_send p q xs) -> onth n xs=Some (s,gc) -> wfgC gc.
Proof.
    Search wfgC.
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
Lemma lem_6_16_simul_subproj: forall G p, wfgC G -> isgPartsC p G ->
  forall q xp xq,
    wfgC G -> 
    issubProj (ltt_send q xp) G p ->
    issubProj (ltt_recv p xq) G q ->
    SList xp -> SList xq ->
    Forall2R (fun u v => u=None \/ 
    exists s elx s' ely, u=Some (s,elx) /\ 
    v=Some (s',ely)
    /\ subsort s s' 
    ) xp xq.
Proof.
    intros G p Hwfog Hispart.
    eapply wfg_proof_princip2 with (g:=G) (p:=p).
    {
        generalize dependent p.
     induction ctx using gtth_ind_ref.
     {
      clear Hwfog.
      clear Hispart.
      clear G.
      intros.
      inversion H;subst.
      inversion H5;subst.
      destr_hyps.
      eapply Forall_prop with (p:=g) (l:=n) in H7; try assumption.
      
      destruct H7. try easy.
      destruct H7. destruct H7.
      destruct H7; [ | destruct H7]; inversion H7;subst;
      apply subproj_inv_send in H1;apply subproj_inv_recv in H2;
      destruct H1;destruct H2; crush;
      [
      eapply simul_subproj_helper with (p:=p) (q:=q) (x0:=x1) |

      inversion H10;inversion H2;subst;
      apply same_rec_send_not_wfg in H0] ;crush.
     }
     {
      intros.
      assert(exists n ss gg, onth n xs=Some (ss,gg)). 
      {
       inversion H0. inversion H6. apply slist_implies_some in H13. subst.
       destr_hyps.
       destruct x0. exists x,s, g. easy.  
      }
        
      destr_hyps. 
      rename x0 into s, x1 into gch.
      pose proof H0 as Hgraft.
      apply multigrafting_lemma1 with (xp:=xp) (xq:=xq) (q:=q0) in H0;try easy.
      pose proof Hgraft as Hgraft'.
      apply typ_p_gtth_inv in Hgraft. destr_hyps. subst.
      eapply Forall_prop with (l:=x) (p:= (s,gch)) in H;try easy.
      destruct H; try easy.
      destr_hyps. 
      inversion H;subst. rename x1 into s, x2 into gch.
      rename x0 into gcs.
      eapply typ_p_gtth_cont2 with (n:=x) (s:=s) (gch:=gch) in Hgraft';try assumption.
      destruct Hgraft' as [gc']. destr_hyps.
      eapply H7 with (q:=q0) (g:=gc') (gs:=gs);try easy.
      eapply continuation_wfgC with (gc:=gc') (n:=x) (s:=s)  in H1;try easy.
      all:apply subproj_inv_send in H2;apply subproj_inv_recv in H3;try easy;
      destruct H2;destruct H3;crush; unfold issubProj; destr_hyps;
      inversion H11;inversion H13;subst;
      rename H14 into Hsubprojsend, H17 into Hsubprojrecv,x5 into gcs;
      unfold subproj_cont_cond in *.
      1: eapply Forall_prop with (l:=x) (p:=(s,gc')) in Hsubprojsend.
      3: eapply Forall_prop with (l:=x) (p:=(s,gc')) in Hsubprojrecv. 
      all:(crush;try easy).
     }
    }
    all:easy.
Qed.

Check subproj_inv_recv.
Check assoc.
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

Check subproj_inv_send.
(*
Lemma lem_6_18_simul_assoc: forall gamma p q G xp xq, assoc gamma G ->
wfgC G ->
SList xp ->
SList xq ->
M.find p gamma =Some  (ltt_send q xp) ->
M.find q gamma =Some  (ltt_recv p xq) ->
(exists ys, G= gtt_send p q ys /\ 
Forall2R (fun u v => u=None \/ 
    exists s T_p s' gy, u=Some (s,T_p) /\ 
    v=Some (s',gy)
    /\ subsort s s' /\
    issubProj T_p gy p
    ) xp ys /\ 
Forall2R (fun u v => u=None \/ 
    exists s T_q s' gy, u=Some (s,gy) /\ 
    v=Some (s',T_q)
    /\ subsort s' s 
    /\ issubProj T_q gy q
    ) ys xq
) \/ 
(exists (s t : opt_lbl) (ys : list (option (sort * gtt))),
G = gtt_send s t ys /\ p <> s /\ p <> t /\ 
issubProj (ltt_send q xp) G p 
/\ issubProj (ltt_recv p xq) G q).
Proof.
    intros.
    eapply assoc_inv_send with (G:=G) in H3; apply assoc_inv_recv with (G:=G) in H4;crush.
    left.
    unfold send_cond, recv_cond in *.
    admit.
    (*eapply simul_subproj_helper with (x0:=x0) (p:=p) (q:=q); crush.
*)
    right. inversion H5;subst. exists x2, x3, x4. crush.
    rename x2 into s, x3 into t, x4 into ys.
    unfold subproj_cont_cond in *. 
Qed.

*)