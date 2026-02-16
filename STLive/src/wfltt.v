(* From mathcomp Require Import ssreflect.seq all_ssreflect. *)
From Paco Require Import paco pacotac.
From live_mpst.STBase Require Import src.expr src.header src.local.
From live_mpst.STLive Require Import src.lcontext.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations Setoid.
From live_mpst.cpdtlib Require Import CpdtTactics.
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

Lemma wfltt_onth_wfltt_send : forall n xs s p t, wflttC (ltt_send p xs) -> 
onth n xs = Some (s,t) ->
wflttC t.
Proof.
    intros.
    pinversion H;subst. eapply Forall_prop with (l:=n) (p:=(s,t)) in H4;try easy.
    destruct H4;try easy. destr_hyps.
    inversion H1;subst.
    destruct H2. red. easy. inversion H2.
Qed.

Lemma wfltt_onth_wfltt_recv : forall n xs s p t, wflttC (ltt_recv p xs) -> 
onth n xs = Some (s,t) ->
wflttC t.
Proof.
    intros.
    pinversion H;subst. eapply Forall_prop with (l:=n) (p:=(s,t)) in H4;try easy.
    destruct H4;try easy. destr_hyps.
    inversion H1;subst.
    destruct H2. red. easy. inversion H2.
Qed.

Definition tctx_wf (g:tctx):= forall p l, 
(M.find p g = Some l -> wflttC l).

Lemma tctx_wf_after_red_send: forall p q ell s gamma gamma', tctx_wf gamma -> 
tctxR gamma (lsend p q (Some s) ell) gamma' -> tctx_wf gamma'.
Proof.
    intros* Hwf Hred.
        eapply tctx_send_invert in Hred as Hrt. destr_hyps.
        red. intros. destruct (Nat.eq_dec p0 p);subst.
        {
         
        rewrite H1 in H2; inversion H2;subst;   
        specialize (Hwf p _ H);
        eapply wfltt_onth_wfltt_send with (p:=q) in H0;try easy.
        }
        {
            eapply red_relevance with (r:= p0) in Hred.
            rewrite H2 in Hred.
            specialize (Hwf p0 _ Hred). easy.
            crush.
        }
Qed.


Lemma tctx_wf_after_red_recv: forall p q ell s gamma gamma', tctx_wf gamma -> 
tctxR gamma (lrecv p q (Some s) ell) gamma' -> tctx_wf gamma'.
Proof.
    intros* Hwf Hred.
        eapply tctx_recv_invert in Hred as Hrt. destr_hyps.
        red. intros. destruct (Nat.eq_dec p0 p);subst.
        {
         
        rewrite H1 in H2; inversion H2;subst;   
        specialize (Hwf p _ H);
        eapply wfltt_onth_wfltt_recv with (p:=q) in H0;try easy.
        }
        {
            eapply red_relevance with (r:= p0) in Hred.
            rewrite H2 in Hred.
            specialize (Hwf p0 _ Hred). easy.
            crush.
        }
Qed.

Lemma tctx_wf_after_red_comm: forall p q ell gamma gamma', tctx_wf gamma -> 
tctxR gamma (lcomm p q ell) gamma' -> tctx_wf gamma'.
Proof.
    intros* Hwf Hred.
    eapply tctx_comm_invert in Hred as Hrt. destr_hyps.
    red. intros. destruct (Nat.eq_dec p0 p);destruct (Nat.eq_dec p0 q);crush.
    {
        rewrite H6 in H5; inversion H5;subst.
        specialize (Hwf p _ H). eapply wfltt_onth_wfltt_send with (p:=q) in H4;try easy.
    }
    {
     rewrite H6 in H3; inversion H3;subst.
        specialize (Hwf q _ H0). eapply wfltt_onth_wfltt_recv with (p:=p) in H2;try easy.
       
    }
    {
        eapply red_relevance with (r:=p0) in Hred.
        rewrite H6 in Hred. specialize (Hwf p0 _ Hred). easy. crush.
    }
Qed.
