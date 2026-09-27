module

import AutoIp._part_1_funcanal._ch_01_bounded_operators._prop_dense_ptwise_filter.Spec -- shake: keep

/-- The hypotheses of `ContinuousLinearMap.tendsto_of_dense_span_filter` can hold together. -/
theorem ContinuousLinearMap.tendsto_of_dense_span_filter_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : NormedSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : NormedSpace 𝕜 F), ∃ (ι : Type), ∃ (ℱ : Filter ι), ∃ (T : ι → E →L[𝕜] F), ∃ (S : E →L[𝕜] F), ∃ (C : ℝ), ∃ (M : Set E), ∃ (x : E), (∀ (i : ι), ‖T i‖ ≤ C) ∧ (Dense (↑(Submodule.span 𝕜 M) : Set E)) ∧ (∀ x ∈ M, Filter.Tendsto (fun (i : ι) => (T i : E → F) x) ℱ (nhds ((S : E → F) x))) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    Empty, ⊥, 0, 0, 0, Set.univ, 0, ?_⟩
  exact ⟨fun i => i.elim, by simp, by simp⟩

/-- The hypotheses of `ContinuousLinearMap.tendsto_of_dense_span_filter` can fail. -/
theorem ContinuousLinearMap.tendsto_of_dense_span_filter_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : NormedSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : NormedSpace 𝕜 F), ∃ (ι : Type), ∃ (ℱ : Filter ι), ∃ (T : ι → E →L[𝕜] F), ∃ (S : E →L[𝕜] F), ∃ (C : ℝ), ∃ (M : Set E), ∃ (x : E), ¬ ((∀ (i : ι), ‖T i‖ ≤ C) ∧ (Dense (↑(Submodule.span 𝕜 M) : Set E)) ∧ (∀ x ∈ M, Filter.Tendsto (fun (i : ι) => (T i : E → F) x) ℱ (nhds ((S : E → F) x)))) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    Unit, ⊥, 0, 0, -1, Set.univ, 0, ?_⟩
  rintro ⟨h, -, -⟩
  have := h ()
  simp at this
  linarith
