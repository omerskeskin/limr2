(* From mathcomp Require Import ssreflect.seq all_ssreflect. *)
From Paco Require Import paco pacotac.
From SST Require Import src.expr src.header src.local CpdtTactics src.lcontext.
From SST Require Import src.global src.projection src.part  src.balanced src.path_props src.merge src.gttreeh.
From SST Require Import lemma.projection lemma.projection_helper lemma.decidable.
From SST Require Import src.step lemma.step src.assoc lemma.correspond.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Init.Logic.

Theorem assoc_implies_weak_safety: forall gamma G, tctx_wf gamma -> wfgC G ->
assoc gamma G -> weak_safety gamma.
Proof.
    unfold weak_safety.
    intros.
    unfold tctxRE in *. destr_hyps.
    eapply lem_6_11a_tctx_send_invert in H2.
    eapply lem_6_11b_tctx_recv_invert in H3.
    destr_hyps.
    rename x3 into xp, x1 into xq.
    assert (Hsubp: issubProj (ltt_send q xp) G p) by (apply assoc_inv_find with (gamma:=gamma);crush). 
    assert (Hsubq: issubProj (ltt_recv p xq) G q) by (apply assoc_inv_find with (gamma:=gamma);crush).
    Check lem_6_16_simul_subproj.

    eapply lem_6_16_simul_subproj with (xq:=xq) in Hsubp;try easy.
    eapply Forall2R_prop with (l:=k) (p:=(s,x4)) in Hsubp;try easy. destr_hyps.
    destruct H9;try easy. destr_hyps;crush.
    rename x5 into Tp, x7 into Tq, x3 into s1, x6 into s2.
    eapply simple_red_comm with (k:=k) (sq:=s2) (sp:=s1) (Tp:=Tp) (Tq:=Tq) (xq:=xq) in H2;try easy.
    set (gamma':= M.add p Tp (M.add q Tq (M.remove p (M.remove q gamma)))).
    exists gamma'.
    unfold gamma'. easy.
    crush.
    unfold issubProj in Hsubp. destr_hyps. Search "subtype_send_inv". 
    apply subtype_send_inv1 in H9. destr_hyps. subst.   Search projectionC isgPartsC.
    eapply projection_implies_part_send  in H8;easy.
    1-2: unfold tctx_wf in H;specialize (H p q xp) as Hawf1;
    specialize (H q p xq) as Hawf2;crush.
Qed.
Search sig.
Theorem assoc_implies_safety: forall gamma G, tctx_wf gamma -> wfgC G -> 
assoc gamma G -> 
    safeC gamma.
Proof.
    pcofix CIH.
    intros.
    pose proof H1 as Hassoc.
    eapply assoc_implies_weak_safety in H1;try easy.
    pcofix CIH.
    pfold.
    Check safety_red.
    eapply safety_red;try easy.
    intros.
    assert (exists G', tctx_wf c' /\ wfgC G' /\ assoc c' G'). admit.
    destruct H3 as [G' Hassoc2].
    split. apply assoc_implies_weak_safety with (G:=G');try easy.
    right. eapply CIH with (G:=G');try easy.
Admitted.