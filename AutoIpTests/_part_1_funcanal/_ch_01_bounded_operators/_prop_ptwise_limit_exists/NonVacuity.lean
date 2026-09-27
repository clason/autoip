module

import AutoIp._part_1_funcanal._ch_01_bounded_operators._prop_ptwise_limit_exists.Spec -- shake: keep

/-- The hypotheses of `ContinuousLinearMap.exists_tendsto_of_dense_span` can hold together. -/
theorem ContinuousLinearMap.exists_tendsto_of_dense_span_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : NormedSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : NormedSpace 𝕜 F), ∃ (x8 : CompleteSpace F), ∃ (T : ℕ → E →L[𝕜] F), ∃ (C : ℝ), ∃ (M : Set E), (∀ (n : ℕ), ‖T n‖ ≤ C) ∧ (Dense (↑(Submodule.span 𝕜 M) : Set E)) ∧ (∀ x ∈ M, ∃ (y : F), Filter.Tendsto (fun (n : ℕ) => (T n : E → F) x) Filter.atTop (nhds y)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 0, 0, Set.univ, ?_⟩
  exact ⟨by simp, by simp, by simp⟩

/-- The hypotheses of `ContinuousLinearMap.exists_tendsto_of_dense_span` can fail. -/
theorem ContinuousLinearMap.exists_tendsto_of_dense_span_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : NormedSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : NormedSpace 𝕜 F), ∃ (x8 : CompleteSpace F), ∃ (T : ℕ → E →L[𝕜] F), ∃ (C : ℝ), ∃ (M : Set E), ¬ ((∀ (n : ℕ), ‖T n‖ ≤ C) ∧ (Dense (↑(Submodule.span 𝕜 M) : Set E)) ∧ (∀ x ∈ M, ∃ (y : F), Filter.Tendsto (fun (n : ℕ) => (T n : E → F) x) Filter.atTop (nhds y))) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 0, -1, Set.univ, ?_⟩
  rintro ⟨h, -, -⟩
  have := h 0
  simp at this
  linarith
