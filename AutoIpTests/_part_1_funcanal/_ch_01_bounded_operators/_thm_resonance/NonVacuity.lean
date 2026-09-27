module

import AutoIp._part_1_funcanal._ch_01_bounded_operators._thm_resonance.Spec -- shake: keep

/-- The hypotheses of `banach_steinhaus_exists_unbounded` can hold together. -/
theorem banach_steinhaus_exists_unbounded_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (ι : Type), ∃ (E : Type), ∃ (F : Type), ∃ (x5 : NormedAddCommGroup E), ∃ (x6 : NormedSpace 𝕜 E), ∃ (x7 : CompleteSpace E), ∃ (x8 : NormedAddCommGroup F), ∃ (x9 : NormedSpace 𝕜 F), ∃ (T : ι → E →L[𝕜] F), ∀ (C : ℝ), ∃ (i : ι), C < ‖T i‖ :=
  by
  refine ⟨ℝ, inferInstance, ℕ, ℝ, ℝ, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, fun n => (n : ℝ) • ContinuousLinearMap.id ℝ ℝ, ?_⟩
  intro C
  obtain ⟨n, hn⟩ := exists_nat_gt C
  refine ⟨n, ?_⟩
  rw [norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_natCast]
  exact hn

/-- The hypotheses of `banach_steinhaus_exists_unbounded` can fail. -/
theorem banach_steinhaus_exists_unbounded_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (ι : Type), ∃ (E : Type), ∃ (F : Type), ∃ (x5 : NormedAddCommGroup E), ∃ (x6 : NormedSpace 𝕜 E), ∃ (x7 : CompleteSpace E), ∃ (x8 : NormedAddCommGroup F), ∃ (x9 : NormedSpace 𝕜 F), ∃ (T : ι → E →L[𝕜] F), ¬ (∀ (C : ℝ), ∃ (i : ι), C < ‖T i‖) :=
  by
  refine ⟨ℝ, inferInstance, Empty, ℝ, ℝ, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, ?_⟩
  intro H
  exact absurd H (by simp)
