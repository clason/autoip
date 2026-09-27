module

import AutoIp._part_2_reg._ch_14_order_optimality._def_worst_case_error.Spec -- shake: keep

open scoped ENNReal

/-- The hypotheses of `AutoIp.worstCaseError` can hold together. -/
theorem AutoIp.worstCaseError_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (x8 : CompleteSpace E), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F → E), ∃ (a : AutoIp.ParameterChoice F), ∃ (y : F), ∃ (δ : ℝ), (y ∈ AutoIp.mpDomain T) ∧ ((0 : ℝ) < δ) :=
  ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 1, fun α z => (1 + (α : ℝ))⁻¹ * z, ⟨fun δ _ => (δ : ℝ), fun δ _ => δ.2⟩,
    1, 1, Submodule.mem_sup_left ⟨1, rfl⟩, one_pos⟩

/-- The hypotheses of `AutoIp.worstCaseError` can fail. -/
theorem AutoIp.worstCaseError_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (x8 : CompleteSpace E), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F → E), ∃ (a : AutoIp.ParameterChoice F), ∃ (y : F), ∃ (δ : ℝ), ¬ ((y ∈ AutoIp.mpDomain T) ∧ ((0 : ℝ) < δ)) :=
  ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 0, 0, ⟨fun _ _ => 1, fun _ _ => one_pos⟩, 0, 0, by
      rintro ⟨-, h⟩
      exact absurd h (lt_irrefl 0)⟩

/-- The hypotheses of `AutoIp.modulusOfContinuity` can hold together. -/
theorem AutoIp.modulusOfContinuity_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (M : Set E), ∃ (δ : ℝ), (0 : ℝ) < δ :=
  ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    1, Metric.closedBall 0 1, 1, one_pos⟩

/-- The hypotheses of `AutoIp.modulusOfContinuity` can fail. -/
theorem AutoIp.modulusOfContinuity_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (M : Set E), ∃ (δ : ℝ), ¬ ((0 : ℝ) < δ) :=
  ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    0, ∅, 0, lt_irrefl 0⟩
