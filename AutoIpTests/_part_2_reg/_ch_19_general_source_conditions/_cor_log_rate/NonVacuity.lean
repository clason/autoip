module

import AutoIp._part_2_reg._ch_19_general_source_conditions._cor_log_rate.Spec -- shake: keep

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.exists_norm_spectralReg_sub_moorePenrose_le_logIndex` can hold together. -/
theorem AutoIp.exists_norm_spectralReg_sub_moorePenrose_le_logIndex_satisfiable : ∃ (p : ℝ), ∃ (κ : ℝ), (0 : ℝ) < p :=
  ⟨1, 0, by norm_num⟩

/-- The hypotheses of `AutoIp.exists_norm_spectralReg_sub_moorePenrose_le_logIndex` can fail. -/
theorem AutoIp.exists_norm_spectralReg_sub_moorePenrose_le_logIndex_nontrivial : ∃ (p : ℝ), ∃ (κ : ℝ), ¬ ((0 : ℝ) < p) :=
  ⟨0, 0, lt_irrefl _⟩
