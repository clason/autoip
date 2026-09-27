module

import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_domain_dense.Spec -- shake: keep

open scoped InnerProductSpace

/-- The hypotheses of `AutoIp.moorePenrose_eq_zero_of_mem_orthogonal_range` can hold together. -/
theorem AutoIp.moorePenrose_eq_zero_of_mem_orthogonal_range_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (x8 : CompleteSpace E), ∃ (T : E →L[𝕜] F), ∃ (y : F), y ∈ (LinearMap.range (↑T : E →ₗ[𝕜] F))ᗮ :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 0, 0, ?_⟩
  exact by simp

/-- The hypotheses of `AutoIp.moorePenrose_eq_zero_of_mem_orthogonal_range` can fail. -/
theorem AutoIp.moorePenrose_eq_zero_of_mem_orthogonal_range_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (x8 : CompleteSpace E), ∃ (T : E →L[𝕜] F), ∃ (y : F), ¬ (y ∈ (LinearMap.range (↑T : E →ₗ[𝕜] F))ᗮ) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ContinuousLinearMap.id ℝ ℝ, 1, ?_⟩
  simp
