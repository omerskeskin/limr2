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
         ~ isgPartsC p gt -> forall Tpx, M.find p g = Some Tpx -> Tpx=ltt_end.

Definition send_cond (xs:list (option (sort*ltt))) (ys:list (option (sort*gtt))) (p:part) := 
    Forall2R (fun x y => x=None 
        \/ (exists s elx s' ely, y=Some (s',ely)/\ x=Some (s,elx) /\ 
        subsort s s' /\
        issubProj elx ely p)) xs ys.
Check send_cond.

Lemma subtype_end_inv : forall t, subtypeC t ltt_end -> t=ltt_end.
Proof.
    intros.
    destruct t;try easy;
    pinversion H;apply subtype_monotone.
Qed.

Definition send_cond2 (t:ltt) (ys:list(option(sort*gtt))) (p:part) :=
    Forall (fun y=> (y=None)\/ 
    (exists s' Gy, y=Some (s', Gy) /\issubProj t Gy p)) ys.

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
        
Section height_induction.
    
End height_induction.

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
    unfold not;intros. unfold wfgC in H. destr_hyps.
    induction x;(try (pinversion H;apply gttT_mon)).
    pinversion H;subst. destruct l.
    inversion H0;subst. inversion H7.
    inversion H4. apply gttT_mon.

Admitted.
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

Lemma projection_implies_part :forall g p q xs, 
projectionC g p (ltt_send q xs) -> isgPartsC p g.
Proof.
    intros. pinversion H;subst;crush. apply proj_mon.
Qed.
Lemma empty_not_wfg_proj: forall p q g, wfgC g -> projectionC g p (ltt_send q []) -> False.
Proof. 
Admitted.
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
Check M.merge.

Lemma subproj_inv_send: forall q xs p G, wfgC G -> 
    SList xs -> issubProj (ltt_send q xs) G p -> 
    (exists ys, G=gtt_send p q ys /\ send_cond xs ys p)
    \/ (exists s t ys, G=gtt_send s t ys /\ p <> s /\ p<> t /\ 
        send_cond2 (ltt_send q xs) ys p ).
Proof.
    intros.
    unfold issubProj in H1.
    destr_hyps.
    
    apply subtype_send_strong_inv in H2.
    destruct H2. destruct H2. subst.
    rename H3 into Hsubtpcond.
    (*ltt_send q x0 is the supertype*)
    Print projection.
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
        eapply subproj_helper with(ys:=o1::x0);crush.
    }
    {

        right. exists p0,q0,xs0. unfold send_cond2. crush. 
        unfold issubProj.
        (*ys: list that merges to ltt_send q x0*)
        inversion H1;subst. crush.
    }
Qed.
