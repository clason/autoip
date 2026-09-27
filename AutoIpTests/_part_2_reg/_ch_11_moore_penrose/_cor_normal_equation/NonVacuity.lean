module

import AutoIp._part_2_reg._ch_11_moore_penrose._cor_normal_equation.Spec -- shake: keep

open scoped InnerProductSpace

/-- The hypotheses of `AutoIp.eq_moorePenrose_of_isLeastSquares` can hold together. -/
theorem AutoIp.eq_moorePenrose_of_isLeastSquares_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (y : F), ∃ (x : E), (AutoIp.IsLeastSquares T y x) ∧ (x ∈ (LinearMap.ker (↑T : E →ₗ[𝕜] F))ᗮ) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 0, 0, 0, ?_⟩
  exact ⟨fun _ => le_rfl, by simp⟩

/-- The hypotheses of `AutoIp.eq_moorePenrose_of_isLeastSquares` can fail. -/
theorem AutoIp.eq_moorePenrose_of_isLeastSquares_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (y : F), ∃ (x : E), ¬ ((AutoIp.IsLeastSquares T y x) ∧ (x ∈ (LinearMap.ker (↑T : E →ₗ[𝕜] F))ᗮ)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 0, 0, 1, ?_⟩
  rintro ⟨-, h⟩
  simp at h
