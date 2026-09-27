module

import AutoIp._part_2_reg._ch_11_moore_penrose._thm_mp_inverse.Spec -- shake: keep

open scoped InnerProductSpace
open scoped InnerProductSpace

/-- The hypotheses of `AutoIp.moorePenrose_apply_apply_of_mem_orthogonal` can hold together. -/
theorem AutoIp.moorePenrose_apply_apply_of_mem_orthogonal_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (x : E), x ∈ (LinearMap.ker (↑T : E →ₗ[𝕜] F))ᗮ :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 0, 0, ?_⟩
  exact by simp

/-- The hypotheses of `AutoIp.moorePenrose_apply_apply_of_mem_orthogonal` can fail. -/
theorem AutoIp.moorePenrose_apply_apply_of_mem_orthogonal_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (x : E), ¬ (x ∈ (LinearMap.ker (↑T : E →ₗ[𝕜] F))ᗮ) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 0, 1, ?_⟩
  simp

/-- The hypotheses of `AutoIp.eq_moorePenrose_of_apply_eq_of_eq_zero` can hold together. -/
theorem AutoIp.eq_moorePenrose_of_apply_eq_of_eq_zero_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (S : F → E), ∃ (y : F), (∀ y ∈ AutoIp.mpDomain T, ∀ z ∈ AutoIp.mpDomain T, S (y + z) = S y + S z) ∧ (∀ x ∈ (LinearMap.ker (↑T : E →ₗ[𝕜] F))ᗮ, S ((T : E → F) x) = x) ∧ (∀ y ∈ (LinearMap.range (↑T : E →ₗ[𝕜] F))ᗮ, S y = (0 : E)) ∧ (y ∈ AutoIp.mpDomain T) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 0, fun _ => 0, 0, ?_⟩
  exact ⟨by simp, by simp, by simp, by simp⟩

/-- The hypotheses of `AutoIp.eq_moorePenrose_of_apply_eq_of_eq_zero` can fail. -/
theorem AutoIp.eq_moorePenrose_of_apply_eq_of_eq_zero_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (S : F → E), ∃ (y : F), ¬ ((∀ y ∈ AutoIp.mpDomain T, ∀ z ∈ AutoIp.mpDomain T, S (y + z) = S y + S z) ∧ (∀ x ∈ (LinearMap.ker (↑T : E →ₗ[𝕜] F))ᗮ, S ((T : E → F) x) = x) ∧ (∀ y ∈ (LinearMap.range (↑T : E →ₗ[𝕜] F))ᗮ, S y = (0 : E)) ∧ (y ∈ AutoIp.mpDomain T)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 0, fun _ => 1, 0, ?_⟩
  rintro ⟨-, h, -⟩
  have := h 0 (Submodule.zero_mem _)
  simp at this
