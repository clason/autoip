module

import AutoIp._part_2_reg._ch_13_regularization._thm_bakushinskii.Spec -- shake: keep

open Filter Topology

/-- The hypotheses of `AutoIp.exists_norm_moorePenrose_le_of_heuristic` can hold together. -/
theorem AutoIp.exists_norm_moorePenrose_le_of_heuristic_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F → E), ∃ (a : AutoIp.ParameterChoice F), (AutoIp.ParameterChoice.IsHeuristic a) ∧ (AutoIp.IsRegularizationMethod T R a) :=
  by
  let a : AutoIp.ParameterChoice ℝ := ⟨fun _ _ => 1, fun _ _ => one_pos⟩
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, 1, fun _ z => z, a, ?_, ?_⟩
  · intro δ ε y
    rfl
  · intro y hy ε hε
    have hmp : AutoIp.moorePenrose (1 : ℝ →L[ℝ] ℝ) ⟨y, hy⟩ = y := by
      have heq := (AutoIp.moorePenrose_isMinimumNorm ⟨y, hy⟩).isLeastSquares y
      simp only [one_apply_eq_self, sub_self, norm_zero] at heq
      exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm heq (norm_nonneg _)))
    refine ⟨ε, hε, fun δ hδ z hz => ?_⟩
    rw [hmp, norm_sub_rev]
    exact lt_of_le_of_lt hz hδ.2

/-- The hypotheses of `AutoIp.exists_norm_moorePenrose_le_of_heuristic` can fail. -/
theorem AutoIp.exists_norm_moorePenrose_le_of_heuristic_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F → E), ∃ (a : AutoIp.ParameterChoice F), ¬ ((AutoIp.ParameterChoice.IsHeuristic a) ∧ (AutoIp.IsRegularizationMethod T R a)) :=
  by
  let a : AutoIp.ParameterChoice ℝ := ⟨fun δ _ => (δ : ℝ), fun δ _ => δ.2⟩
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 0, fun _ _ => 0, a, ?_⟩
  rintro ⟨H, -⟩
  have h := H ⟨1, Set.mem_Ioi.2 one_pos⟩ ⟨2, Set.mem_Ioi.2 two_pos⟩ 0
  change (1 : ℝ) = 2 at h
  norm_num at h
