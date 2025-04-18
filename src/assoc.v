(* From mathcomp Require Import ssreflect.seq all_ssreflect. *)
From Paco Require Import paco pacotac.
From SST Require Import src.expr src.header src.local CpdtTactics src.lcontext.
From SST Require Import src.global src.projection src.part src.balanced.
From SST Require Import lemma.projection lemma.projection_helper.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations Setoid.
Require Import Coq.Program.Equality.
Import ListNotations.


Definition issubProj (t:ltt) (g:gtt) (p:part) := exists tg, projectionC g p tg /\ subtypeC t tg.

Search subtypeC.

Definition assoc (g: tctx) (gt:gtt) := 
    forall p, (isgPartsC p gt -> exists Tp, M.find p g=Some Tp /\  
        issubProj Tp gt p) /\
         ~ isgPartsC p gt -> forall Tpx, M.find p g = Some Tpx -> Tpx=ltt_end.

Definition send_cond (xs:list (option (sort*ltt))) (ys:list (option (sort*gtt))) (p:part) := 
    Forall2 (fun x y => x=None 
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

Locate proj_inv_lis.

Lemma subproj_inv_send: forall q xs p G, wfgC G -> issubProj (ltt_send q xs) G p -> 
    (exists ys, G=gtt_send p q ys /\ send_cond xs ys p)
    \/ (exists s t ys, G=gtt_send s t ys /\ p <> s /\ p<> t /\ 
        send_cond2 (ltt_send q xs) ys p ).
