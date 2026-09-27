module

import AutoIp._part_2_reg._ch_19_general_source_conditions._cor_holder_in_log.Spec -- shake: keep

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.exists_sourceSet_subset_sourceSetIndex_logIndex` can hold together. -/
theorem AutoIp.exists_sourceSet_subset_sourceSetIndex_logIndex_satisfiable : ∃ (ν : ℝ), ∃ (p : ℝ), ∃ (κ : ℝ), ((0 : ℝ) < ν) ∧ ((0 : ℝ) < p) :=
  ⟨1, 1, 0, by norm_num, by norm_num⟩

/-- The hypotheses of `AutoIp.exists_sourceSet_subset_sourceSetIndex_logIndex` can fail. -/
theorem AutoIp.exists_sourceSet_subset_sourceSetIndex_logIndex_nontrivial : ∃ (ν : ℝ), ∃ (p : ℝ), ∃ (κ : ℝ), ¬ (((0 : ℝ) < ν) ∧ ((0 : ℝ) < p)) :=
  ⟨0, 1, 0, fun h => lt_irrefl _ h.1⟩
