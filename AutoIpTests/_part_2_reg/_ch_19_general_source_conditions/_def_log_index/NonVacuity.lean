module

import AutoIp._part_2_reg._ch_19_general_source_conditions._def_log_index.Spec -- shake: keep

/-- The hypotheses of `AutoIp.logIndex` can hold together. -/
theorem AutoIp.logIndex_satisfiable : ∃ (κ : ℝ), ∃ (p : ℝ), ∃ (lam : ℝ), (0 : ℝ) < p :=
  by
  exact ⟨0, 1, 0, one_pos⟩

/-- The hypotheses of `AutoIp.logIndex` can fail. -/
theorem AutoIp.logIndex_nontrivial : ∃ (κ : ℝ), ∃ (p : ℝ), ∃ (lam : ℝ), ¬ ((0 : ℝ) < p) :=
  by
  exact ⟨0, 0, 0, lt_irrefl 0⟩
