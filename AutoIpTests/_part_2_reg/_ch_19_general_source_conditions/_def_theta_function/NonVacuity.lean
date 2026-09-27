module

import AutoIp._part_2_reg._ch_19_general_source_conditions._def_theta_function.Spec -- shake: keep

open Filter Topology

/-- The hypotheses of `AutoIp.isIndexFunction_thetaIndex` can hold together. -/
theorem AutoIp.isIndexFunction_thetaIndex_satisfiable : ∃ (κ : ℝ), ∃ (φ : ℝ → ℝ), AutoIp.IsIndexFunction κ φ :=
  by
  refine ⟨1, fun t => t, ?_⟩
  exact ⟨rfl, continuousOn_id, fun _ _ _ _ h => h⟩

/-- The hypotheses of `AutoIp.isIndexFunction_thetaIndex` can fail. -/
theorem AutoIp.isIndexFunction_thetaIndex_nontrivial : ∃ (κ : ℝ), ∃ (φ : ℝ → ℝ), ¬ (AutoIp.IsIndexFunction κ φ) :=
  by
  refine ⟨1, fun _ => 1, ?_⟩
  intro H
  exact one_ne_zero H.map_zero

/-- The hypotheses of `AutoIp.existsUnique_thetaIndex_eq` can hold together. -/
theorem AutoIp.existsUnique_thetaIndex_eq_satisfiable : ∃ (κ : ℝ), ∃ (φ : ℝ → ℝ), ∃ (t : ℝ), (AutoIp.IsIndexFunction κ φ) ∧ (t ∈ Set.Ioc (0 : ℝ) (AutoIp.thetaIndex φ κ)) :=
  by
  refine ⟨1, fun t => t, 1, ⟨rfl, continuousOn_id, fun _ _ _ _ h => h⟩, ?_⟩
  rw [AutoIp.thetaIndex_apply]
  simp

/-- The hypotheses of `AutoIp.existsUnique_thetaIndex_eq` can fail. -/
theorem AutoIp.existsUnique_thetaIndex_eq_nontrivial : ∃ (κ : ℝ), ∃ (φ : ℝ → ℝ), ∃ (t : ℝ), ¬ ((AutoIp.IsIndexFunction κ φ) ∧ (t ∈ Set.Ioc (0 : ℝ) (AutoIp.thetaIndex φ κ))) :=
  by
  refine ⟨1, fun t => t, 0, ?_⟩
  rintro ⟨H, _⟩
  exact absurd H (by simp_all)

/-- The hypotheses of `AutoIp.exists_orderIso_thetaIndex` can hold together. -/
theorem AutoIp.exists_orderIso_thetaIndex_satisfiable : ∃ (κ : ℝ), ∃ (φ : ℝ → ℝ), ((0 : ℝ) ≤ κ) ∧ (AutoIp.IsIndexFunction κ φ) :=
  ⟨1, fun t => t, zero_le_one, ⟨rfl, continuousOn_id, fun _ _ _ _ h => h⟩⟩

/-- The hypotheses of `AutoIp.exists_orderIso_thetaIndex` can fail. -/
theorem AutoIp.exists_orderIso_thetaIndex_nontrivial : ∃ (κ : ℝ), ∃ (φ : ℝ → ℝ), ¬ (((0 : ℝ) ≤ κ) ∧ (AutoIp.IsIndexFunction κ φ)) :=
  ⟨-1, fun t => t, fun h => absurd h.1 (by norm_num)⟩
