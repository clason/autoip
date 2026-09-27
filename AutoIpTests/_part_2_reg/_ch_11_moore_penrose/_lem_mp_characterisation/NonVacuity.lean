module

import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_characterisation.Spec -- shake: keep

open scoped InnerProductSpace

/-- The hypotheses of `AutoIp.eq_moorePenrose_of_comp_eq_of_isSelfAdjoint` can hold together. -/
theorem AutoIp.eq_moorePenrose_of_comp_eq_of_isSelfAdjoint_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (S : F →L[𝕜] E), ∃ (y : F), (IsClosed (↑(LinearMap.range (↑T : E →ₗ[𝕜] F)) : Set F)) ∧ (T ∘SL S ∘SL T = T) ∧ (S ∘SL T ∘SL S = S) ∧ (IsSelfAdjoint (S ∘SL T)) ∧ (IsSelfAdjoint (T ∘SL S)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, 0, 0, ?_⟩
  exact ⟨by simp, by simp, by simp, by simp⟩

/-- The hypotheses of `AutoIp.eq_moorePenrose_of_comp_eq_of_isSelfAdjoint` can fail. -/
theorem AutoIp.eq_moorePenrose_of_comp_eq_of_isSelfAdjoint_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (S : F →L[𝕜] E), ∃ (y : F), ¬ ((IsClosed (↑(LinearMap.range (↑T : E →ₗ[𝕜] F)) : Set F)) ∧ (T ∘SL S ∘SL T = T) ∧ (S ∘SL T ∘SL S = S) ∧ (IsSelfAdjoint (S ∘SL T)) ∧ (IsSelfAdjoint (T ∘SL S))) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ContinuousLinearMap.id ℝ ℝ, 0, 0, ?_⟩
  rintro ⟨-, h, -⟩
  have := congrArg (fun T : ℝ →L[ℝ] ℝ => T 1) h
  simp at this
