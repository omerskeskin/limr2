From mathcomp Require Import ssreflect.seq all_ssreflect.
From Paco Require Import paco pacotac.
From SST Require Import src.expr src.header src.local src.lcontext src.path_props CpdtTactics.
Require Import List String Coq.Arith.PeanoNat Setoid Morphisms Relations.
Import ListNotations. 

Open Scope string_scope.
Definition prt_p:=0.
Definition prt_q:=1.
Definition prt_r:=2.
(*adopt the convention that all opts have the same length*)
CoFixpoint T_p := ltt_send prt_q [Some (sint,T_p); Some (sint,ltt_end); None].
CoFixpoint T_q := ltt_recv prt_p [Some (sint,T_q); Some (sint, ltt_send prt_r [None;None;Some (sint,ltt_end)]); None].
Definition T_r := ltt_recv prt_q [None;None; Some (sint,ltt_end)].

Definition gamma := M.add prt_p T_p (M.add prt_q T_q (M.add prt_r T_r M.empty)).
Print Instances Proper.

#[global] Instance RWMTCTXR: Proper ((@M.Equal ltt) ==> (eq) ==> (@M.Equal ltt) ==> (iff)) tctxR.
Proof. unfold "==>". constructor; intros; subst. 
apply Rstruct with (g1:=y) (g2:=y1) (g1':=x) (g2':=x1);crush. 
apply Rstruct with (g1:=x) (g2:=x1) (g1':=y) (g2':=y1);crush.
Qed.

Lemma red_1 : tctxR gamma (lsend prt_p prt_q (Some sint) 0) gamma.
Proof.
    Search m_update.
    assert(M.Equal (m_update prt_p T_p gamma) gamma).
    {
        apply map_perm_invariance;crush.
    }
    rewrite (ltt_eq T_p) in H;simpl in H.
    setoid_rewrite <- H at 2.
    apply simple_red_send with (xs:=[Some (sint, T_p); Some (sint, ltt_end); None]);
    [unfold prt_p in *;unfold prt_q in *;crush| unfold gamma;try rewrite M.add_spec1 | ];
    unfold T_p at 2;
    rewrite (ltt_eq T_p);
    simpl; fold T_p; easy.
Qed.
Lemma red_2 : tctxR gamma  (lrecv prt_q prt_p (Some sint) 0) (gamma).
Proof.
    set (gmp:=(M.add prt_p T_p (M.add prt_r T_r (M.add prt_q T_q M.empty)))).
    assert (H_perm:M.Equal gamma gmp). easy.
    apply Rstruct with (g1':=gmp) (g2':=gmp); try assumption.
    apply RvarI.
    {
        apply RvarI; try (unfold M.mem;reflexivity).
        rewrite (ltt_eq T_q).
        apply Rrecv with (n:=0). easy. fold T_p. rewrite <- (ltt_eq T_q). reflexivity. 
    }
    {
        unfold M.mem.
        reflexivity.
    }
Qed.

Lemma red_3 : tctxR gamma  (lcomm prt_p prt_q 0) gamma.
Proof.
    set (gmp:=(M.add prt_r T_r (M.add prt_p T_p (M.add prt_q T_q M.empty)))).
    assert (H_perm:M.Equal gamma gmp). easy.
    apply Rstruct with (g1':=gmp) (g2':=gmp); try assumption.
    set (p_only:=(M.add prt_p T_p M.empty)).
    set (q_only:=(M.add prt_q T_q M.empty)).
    assert(H_disj:MF.Disjoint p_only q_only).
    {
        unfold MF.Disjoint. unfold not.
        intros.
        destruct H.
        apply MF.add_in_iff in H.
        destruct H.
        {
            subst. apply MF.in_find in H0.
            unfold M.find in H0. simpl in H0. easy.
        }
        {
            apply MF.not_in_empty in H. assumption.
        }
    }
    assert(p_trans:tctxR p_only (lsend prt_p prt_q (Some sint) 0) p_only).
    {
        unfold p_only.
        rewrite (ltt_eq T_p).
        apply Rsend with (n:=0). easy. fold T_p.
        rewrite <- (ltt_eq T_p). reflexivity.
    }
    
    assert(q_trans:tctxR q_only (lrecv prt_q prt_p (Some sint) 0) q_only).
    {
        unfold q_only.
        rewrite (ltt_eq T_q).
        apply Rrecv with (n:=0). easy. fold T_p.
        rewrite <- (ltt_eq T_q). reflexivity.
    }
    assert(H_eqn: M.Equal (disj_merge p_only q_only H_disj) (M.add prt_p T_p (M.add prt_q T_q M.empty))).
    {
        unfold M.Equal.
        intros.
        unfold disj_merge.
        rewrite MF.merge_spec1mn; try easy.
        unfold p_only. unfold q_only.
        do 4 rewrite MF.add_o.
        Search M.find M.empty.
        rewrite M.empty_spec.
        destruct (Nat.eq_dec prt_p y); destruct (Nat.eq_dec prt_q y); try (simpl; easy).
        subst. discriminate.
    }
    apply RvarI; try (unfold M.mem; reflexivity).
    Search MF.Disjoint.
    apply Rstruct with (g1':=disj_merge p_only q_only H_disj) (g2':=disj_merge p_only q_only H_disj).
    apply Rcomm with (g1:=p_only) (g1':=p_only) (g2:=q_only) (g2':=q_only) (H1:= H_disj) (H2:=H_disj) (s:=sint) (s':=sint); try easy.
    apply srefl.
    apply MF.Equal_equiv. assumption.
    apply MF.Equal_equiv. assumption.
Qed.

Lemma red_4 : tctxR gamma (lrecv prt_r prt_q (Some sint) 2) (M.add prt_p  T_p (M.add prt_q T_q (M.add prt_r ltt_end M.empty))).
Proof.
    apply RvarI.
    apply RvarI.
    rewrite (ltt_eq T_r). simpl.
    apply Rrecv with (n:=2). easy. simpl. reflexivity. 1-2:unfold M.mem. 1-2:reflexivity.
Qed.

CoFixpoint inf_pq_path := cocons (gamma,(lcomm prt_p prt_q) 0) inf_pq_path.

Theorem inf_pq_path_fair : fairness inf_pq_path.
Proof.
    red.
    pcofix CIH.
    rewrite (coseq_eq inf_pq_path). simpl.
    pfold.
    constructor.
    unfold fairPath.
    intros.
    assert(H_p:p=prt_p).
    {   
        destruct (Nat.eq_dec p prt_p). assumption.
        simpl in H.
        inversion H. subst. 
        apply lem_6_11c_tctx_comm_invert in H0.
        destr_hyps.
        destruct (Nat.eq_dec p prt_q);
        destruct (Nat.eq_dec p prt_r); crush. 
        unfold prt_r,prt_p,prt_q in *;crush.

        intros.
        unfold gamma in H0.
        rewrite M.add_spec2 in H0.
        rewrite M.add_spec1 in H0. rewrite (ltt_eq T_q) in H0. simpl in H0.
        discriminate H0. crush.
        
        unfold gamma in H0.
        rewrite M.add_spec2 in H0.
        rewrite M.add_spec2 in H0.
        rewrite M.add_spec1 in H0. rewrite (ltt_eq T_r) in H0. simpl in H0. discriminate. crush.
        crush.
        rewrite M.add_spec2 in H0; try rewrite M.add_spec2 in H0; try rewrite M.add_spec2 in H0;
        try rewrite M.empty_spec in H0;crush.
    }
    assert(H_q:q=prt_q).
    {
        destruct (Nat.eq_dec q prt_q). assumption.
        simpl in H.
        inversion H. subst. 
        apply lem_6_11c_tctx_comm_invert in H0.
        destr_hyps.
        destruct (Nat.eq_dec q prt_p);
        destruct (Nat.eq_dec q prt_r); crush.

        unfold gamma in H0;
        first rewrite M.add_spec2 in H0;
        first rewrite M.add_spec2 in H0;
        first rewrite M.add_spec2 in H0;
        first rewrite M.empty_spec in H0;
        first discriminate H0; crush.
        
        discriminate H0.
        
        unfold gamma in H1.
        rewrite M.add_spec2 in H1.
        rewrite M.add_spec2 in H1.
        rewrite M.add_spec1 in H1. rewrite (ltt_eq T_r) in H1. simpl in H1. discriminate. crush.
        crush.
        rewrite M.add_spec2 in H1; try rewrite M.add_spec2 in H1; try rewrite M.add_spec2 in H1;
        try rewrite M.empty_spec in H1;crush.
    }
    apply evh. subst. simpl. easy.
    right. assumption.
Qed.

Lemma red_5: tctxR gamma (lsend prt_p prt_q (Some sint) 1) (M.add prt_p ltt_end (M.add prt_q T_q (M.add prt_r T_r M.empty))).
Proof.
    set (gmp:=(M.add prt_q T_q (M.add prt_r T_r (M.add prt_p T_p M.empty)))).
    assert (H_perm:M.Equal gamma gmp). easy.
    apply Rstruct with (g1':=gmp) (g2' := (M.add prt_q T_q (M.add prt_r T_r (M.add prt_p ltt_end M.empty)))); try easy.
    unfold gmp.
    apply RvarI; try (unfold M.mem; reflexivity).
    + apply RvarI; try (unfold M.mem; reflexivity).
        - rewrite (ltt_eq T_p). apply Rsend with (n:=1); try easy.
Qed.

Lemma red_6: tctxR gamma (lrecv prt_q prt_p (Some sint) 1) (M.add prt_p T_p (M.add prt_q (ltt_send prt_r [None;None;Some (sint,ltt_end)]) (M.add prt_r T_r M.empty))).
Proof.
    set (gmp:=(M.add prt_p T_p (M.add prt_r T_r (M.add prt_q T_q M.empty)))).
    assert (H_perm:M.Equal gamma gmp). easy.
    apply Rstruct with (g1':=gmp) (g2' := (M.add prt_p T_p (M.add prt_r T_r (M.add prt_q (ltt_send prt_r [None;None;Some (sint,ltt_end)]) M.empty)))); try easy.
    unfold gmp.
    apply RvarI; try (unfold M.mem; reflexivity).
    + apply RvarI; try (unfold M.mem; reflexivity).
        - rewrite (ltt_eq T_q). apply Rrecv with (n:=1); try easy.
Qed.

Definition gamma' := M.add prt_p ltt_end (M.add prt_q (ltt_send prt_r [None;None;Some (sint,ltt_end)]) (M.add prt_r T_r M.empty)).

Lemma red_7 : tctxR gamma (lcomm prt_p prt_q 1) gamma'.
Proof.
    set (p_only := M.add prt_p T_p M.empty).
    set (q_only := M.add prt_q T_q M.empty).
    
    set (p_only' := M.add prt_p ltt_end M.empty).
    set (q_only' := M.add prt_q (ltt_send prt_r [None;None;Some (sint,ltt_end)]) M.empty).
    assert(Hp1: tctxR p_only (lsend prt_p prt_q (Some sint) 1) p_only').
    {
        unfold p_only.
        unfold p_only'.
        rewrite (ltt_eq T_p).
        apply Rsend with (n:=1); try easy.   
    }
    assert(Hq1: tctxR q_only (lrecv prt_q prt_p (Some sint) 1) q_only').
    {
        unfold q_only.
        unfold q_only'.
        rewrite (ltt_eq T_q).
        apply Rrecv with (n:=1); try easy.   
    }
    assert(H_disj:MF.Disjoint p_only q_only).
    {
        unfold MF.Disjoint. unfold not.
        intros.
        destruct H.
        apply MF.add_in_iff in H.
        destruct H.
        {
            subst. apply MF.in_find in H0.
            unfold M.find in H0. simpl in H0. easy.
        }
        {
            apply MF.not_in_empty in H. assumption.
        }
    }

    set (pq := M.add prt_p T_p (M.add prt_q T_q M.empty)).
    set (pq' := M.add prt_p ltt_end (M.add prt_q (ltt_send prt_r [None;None;Some (sint, ltt_end)]) M.empty)).
    
    assert(H_eqn: M.Equal (disj_merge p_only q_only H_disj) (M.add prt_p T_p (M.add prt_q T_q M.empty))).
    {
        unfold M.Equal.
        intros.
        unfold disj_merge.
        rewrite MF.merge_spec1mn; try easy.
        unfold p_only. unfold q_only.
        do 4 rewrite MF.add_o.
        Search M.find M.empty.
        rewrite M.empty_spec.
        destruct (Nat.eq_dec prt_p y); destruct (Nat.eq_dec prt_q y); try (simpl; easy).
        subst. discriminate.
    }
    assert (Hpq : tctxR pq (lcomm prt_p prt_q 1) pq').
    {
     unfold pq. unfold pq'. admit.
    }
Abort.