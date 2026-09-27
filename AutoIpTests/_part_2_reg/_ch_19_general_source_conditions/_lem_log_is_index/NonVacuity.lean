module

import AutoIp._part_2_reg._ch_19_general_source_conditions._lem_log_is_index.Spec -- shake: keep
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter Topology

/-- The hypotheses of `AutoIp.isIndexFunction_logIndex` can hold together. -/
theorem AutoIp.isIndexFunction_logIndex_satisfiable : ∃ (κ : ℝ), ∃ (p : ℝ), (0 : ℝ) < p :=
  by
  refine ⟨0, 1, ?_⟩
  exact by norm_num

/-- The hypotheses of `AutoIp.isIndexFunction_logIndex` can fail. -/
theorem AutoIp.isIndexFunction_logIndex_nontrivial : ∃ (κ : ℝ), ∃ (p : ℝ), ¬ ((0 : ℝ) < p) :=
  by
  refine ⟨0, 0, ?_⟩
  intro H
  exact absurd H (lt_irrefl 0)
