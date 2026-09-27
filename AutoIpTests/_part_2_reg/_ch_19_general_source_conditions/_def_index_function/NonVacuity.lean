module

import AutoIp._part_2_reg._ch_19_general_source_conditions._def_index_function.Spec -- shake: keep

open Filter Topology

/-- The hypotheses of `AutoIp.IsIndexFunction.nonneg` can hold together. -/
theorem AutoIp.IsIndexFunction.nonneg_satisfiable : ∃ (κ : ℝ), ∃ (φ : ℝ → ℝ), ∃ (t : ℝ), (AutoIp.IsIndexFunction κ φ) ∧ (t ∈ Set.Icc (0 : ℝ) κ) :=
  by
  refine ⟨1, fun t => t, 0, ?_⟩
  exact ⟨⟨rfl, continuousOn_id, fun _ _ _ _ h => h⟩, by simp⟩

/-- The hypotheses of `AutoIp.IsIndexFunction.nonneg` can fail. -/
theorem AutoIp.IsIndexFunction.nonneg_nontrivial : ∃ (κ : ℝ), ∃ (φ : ℝ → ℝ), ∃ (t : ℝ), ¬ ((AutoIp.IsIndexFunction κ φ) ∧ (t ∈ Set.Icc (0 : ℝ) κ)) :=
  by
  refine ⟨1, fun _ => 1, 0, ?_⟩
  rintro ⟨H, _⟩
  exact one_ne_zero H.map_zero
