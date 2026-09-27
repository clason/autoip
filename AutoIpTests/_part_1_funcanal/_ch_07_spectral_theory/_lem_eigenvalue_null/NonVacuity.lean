module

import AutoIp._part_1_funcanal._ch_07_spectral_theory._lem_eigenvalue_null.Spec -- shake: keep
import AutoIpTests.Witnesses.Diagonal

open scoped InnerProductSpace

/-- The hypotheses of `IsCompactOperator.finite_spectrum_norm_ge` can hold together. -/
theorem IsCompactOperator.finite_spectrum_norm_ge_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (H : Type), ∃ (x3 : NormedAddCommGroup H), ∃ (x4 : InnerProductSpace 𝕜 H), ∃ (x5 : CompleteSpace H), ∃ (K : H →L[𝕜] H), ∃ (ε : ℝ), (IsCompactOperator (⇑K : H → H)) ∧ ((0 : ℝ) < ε) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, inferInstance, 0, 1, ?_⟩
  exact ⟨isCompactOperator_zero, by norm_num⟩

/-- The hypotheses of `IsCompactOperator.finite_spectrum_norm_ge` can fail. -/
theorem IsCompactOperator.finite_spectrum_norm_ge_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (H : Type), ∃ (x3 : NormedAddCommGroup H), ∃ (x4 : InnerProductSpace 𝕜 H), ∃ (x5 : CompleteSpace H), ∃ (K : H →L[𝕜] H), ∃ (ε : ℝ), ¬ ((IsCompactOperator (⇑K : H → H)) ∧ ((0 : ℝ) < ε)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, inferInstance, 0, 0, ?_⟩
  rintro ⟨_, H⟩
  exact absurd H (lt_irrefl 0)

/-- The hypotheses of `IsCompactOperator.countable_spectrum` can hold together. -/
theorem IsCompactOperator.countable_spectrum_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (H : Type), ∃ (x3 : NormedAddCommGroup H), ∃ (x4 : InnerProductSpace 𝕜 H), ∃ (x5 : CompleteSpace H), ∃ (K : H →L[𝕜] H), IsCompactOperator (⇑K : H → H) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, inferInstance, 0, ?_⟩
  exact isCompactOperator_zero

/-- The hypotheses of `IsCompactOperator.countable_spectrum` can fail. -/
theorem IsCompactOperator.countable_spectrum_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (H : Type), ∃ (x3 : NormedAddCommGroup H), ∃ (x4 : InnerProductSpace 𝕜 H), ∃ (x5 : CompleteSpace H), ∃ (K : H →L[𝕜] H), ¬ (IsCompactOperator (⇑K : H → H)) :=
  ⟨ℝ, inferInstance, Witnesses.Diagonal.H, inferInstance, inferInstance, inferInstance, 1,
    Witnesses.Diagonal.not_isCompactOperator_one⟩

/-- The hypotheses of `IsCompactOperator.eq_zero_of_accPt_spectrum` can hold together. -/
theorem IsCompactOperator.eq_zero_of_accPt_spectrum_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (H : Type), ∃ (x3 : NormedAddCommGroup H), ∃ (x4 : InnerProductSpace 𝕜 H), ∃ (x5 : CompleteSpace H), ∃ (K : H →L[𝕜] H), ∃ (μ : 𝕜), (IsCompactOperator (⇑K : H → H)) ∧ (AccPt μ (Filter.principal (spectrum 𝕜 K))) :=
  by
  refine ⟨ℝ, inferInstance, Witnesses.Diagonal.H, inferInstance, inferInstance, inferInstance,
    Witnesses.Diagonal.T, 0, Witnesses.Diagonal.isCompactOperator_T, ?_⟩
  rw [accPt_iff_nhds]
  intro U hU
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (Witnesses.Diagonal.tendsto_w hU)
  exact ⟨Witnesses.Diagonal.w N, ⟨hN N le_rfl, Witnesses.Diagonal.mem_spectrum_T N⟩,
    (Witnesses.Diagonal.w_pos N).ne'⟩

/-- The hypotheses of `IsCompactOperator.eq_zero_of_accPt_spectrum` can fail. -/
theorem IsCompactOperator.eq_zero_of_accPt_spectrum_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (H : Type), ∃ (x3 : NormedAddCommGroup H), ∃ (x4 : InnerProductSpace 𝕜 H), ∃ (x5 : CompleteSpace H), ∃ (K : H →L[𝕜] H), ∃ (μ : 𝕜), ¬ ((IsCompactOperator (⇑K : H → H)) ∧ (AccPt μ (Filter.principal (spectrum 𝕜 K)))) :=
  by
  refine ⟨ℝ, inferInstance, Witnesses.Diagonal.H, inferInstance, inferInstance, inferInstance, 1,
    0, ?_⟩
  rintro ⟨h, -⟩
  exact Witnesses.Diagonal.not_isCompactOperator_one h
