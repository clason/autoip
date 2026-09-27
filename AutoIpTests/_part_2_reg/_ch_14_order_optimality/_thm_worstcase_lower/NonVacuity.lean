module

import AutoIp._part_2_reg._ch_14_order_optimality._thm_worstcase_lower.Spec -- shake: keep

open Filter Topology
open scoped ENNReal

/-- The hypotheses of `AutoIp.modulusOfContinuity_le_iSup_worstCaseError` can hold together. -/
theorem AutoIp.modulusOfContinuity_le_iSup_worstCaseError_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →ₗ[𝕜] E), ∃ (a : AutoIp.ParameterChoice F), ∃ (M : Set E), ∃ (δ : ℝ), (M ⊆ (↑(LinearMap.ker (↑T : E →ₗ[𝕜] F))ᗮ : Set E)) ∧ ((0 : ℝ) < δ) :=
  by
  have hk : LinearMap.ker ((1 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) = ⊥ := LinearMap.ker_id
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 1, fun α => (1 + (α : ℝ))⁻¹ • LinearMap.id,
    ⟨fun δ _ => (δ : ℝ), fun δ _ => δ.2⟩, Metric.closedBall 0 1, 1, ?_, one_pos⟩
  intro x _
  rw [SetLike.mem_coe, hk, Submodule.bot_orthogonal_eq_top]
  exact Submodule.mem_top

/-- The hypotheses of `AutoIp.modulusOfContinuity_le_iSup_worstCaseError` can fail. -/
theorem AutoIp.modulusOfContinuity_le_iSup_worstCaseError_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →ₗ[𝕜] E), ∃ (a : AutoIp.ParameterChoice F), ∃ (M : Set E), ∃ (δ : ℝ), ¬ ((M ⊆ (↑(LinearMap.ker (↑T : E →ₗ[𝕜] F))ᗮ : Set E)) ∧ ((0 : ℝ) < δ)) :=
  ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 0, 0, ⟨fun _ _ => 1, fun _ _ => one_pos⟩, ∅, 0, by
      rintro ⟨-, h⟩
      exact absurd h (lt_irrefl 0)⟩
