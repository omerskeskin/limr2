(* From mathcomp Require Import ssreflect.seq all_ssreflect. *)
From Paco Require Import paco pacotac.
From SST Require Import src.expr src.header src.local src.lcontext CpdtTactics.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations Setoid.
Require Import Coq.Program.Equality.
Import ListNotations.

Variant wfltt (R: ltt -> Prop) : ltt -> Prop := 
    | wfltt_end : wfltt R ltt_end
    | wfltt_send: forall p xs, SList xs -> Forall 
    (fun u=> u= None \/ exists s g, u= Some (s,g) 
        /\ R g) xs -> wfltt R (ltt_send p xs)
    | wfltt_recv: forall p xs, SList xs -> Forall (fun u=> u= None \/ exists s g, u= Some (s,g) 
        /\ R g) xs -> wfltt R (ltt_recv p xs).

Definition wflttC := paco1 wfltt bot1.
Lemma wfltt_mon : monotone1 wfltt.
Proof.
    red. intros. inversion IN;subst;constructor;
    eapply Forall_impl with (Q:= fun u : option (sort * ltt) =>
u = None \/
(exists (s : sort) (g : ltt), u = Some (s, g) /\ r' g)) in H0;crush;right; exists x,x0;crush.
Qed.
Hint Resolve wfltt_mon:paco.

Lemma wfltt_slist_send : forall p xs, wflttC (ltt_send p xs) -> SList xs.
Proof. intros; pinversion H;easy. Qed.
Lemma wfltt_slist_recv : forall p xs, wflttC (ltt_recv p xs) -> SList xs.
Proof. intros; pinversion H;easy. Qed.

Definition tctx_wf (g:tctx):= forall p l, 
(M.find p g = Some l -> wflttC l).