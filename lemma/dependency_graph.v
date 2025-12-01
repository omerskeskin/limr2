Require dpdgraph.dpdgraph.
From SST Require multigrafting liveness liveness_helpers fairness_feasible.

Print FileDependGraph lemma.path_assoc  lemma.completeness 
 lemma.subj_red_prog_fid lemma.projection lemma.subj_red_helpers 
 lemma.soundness lemma.fairness_feasible
lemma.liveness_helpers lemma.liveness lemma.live_proc lemma.multigrafting
src.path_props src.lcontext.

Set DependGraph File "graph_redux.dpd".

Print FileDependGraph lemma.path_assoc  
 lemma.subj_red_prog_fid 
 lemma.fairness_feasible
lemma.liveness_helpers lemma.multigrafting lemma.liveness lemma.live_proc.
