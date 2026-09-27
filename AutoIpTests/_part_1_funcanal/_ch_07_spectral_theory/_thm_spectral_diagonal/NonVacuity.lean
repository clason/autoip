module

import AutoIp._part_1_funcanal._ch_07_spectral_theory._thm_spectral_diagonal.Spec -- shake: keep
import AutoIpTests.Witnesses.Diagonal

open scoped InnerProductSpace

/-- The hypotheses of `IsSelfAdjoint.exists_ordered_hasSum_smul_inner` can hold together. -/
theorem IsSelfAdjoint.exists_ordered_hasSum_smul_inner_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (H : Type), ∃ (x3 : NormedAddCommGroup H), ∃ (x4 : InnerProductSpace 𝕜 H), ∃ (x5 : CompleteSpace H), ∃ (K : H →L[𝕜] H), (IsSelfAdjoint K) ∧ (IsCompactOperator (⇑K : H → H)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, inferInstance, 0, ?_⟩
  exact ⟨by simp, isCompactOperator_zero⟩

/-- The hypotheses of `IsSelfAdjoint.exists_ordered_hasSum_smul_inner` can fail. -/
theorem IsSelfAdjoint.exists_ordered_hasSum_smul_inner_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (H : Type), ∃ (x3 : NormedAddCommGroup H), ∃ (x4 : InnerProductSpace 𝕜 H), ∃ (x5 : CompleteSpace H), ∃ (K : H →L[𝕜] H), ¬ ((IsSelfAdjoint K) ∧ (IsCompactOperator (⇑K : H → H))) :=
  by
  refine ⟨ℝ, inferInstance, Witnesses.Diagonal.H, inferInstance, inferInstance, inferInstance, 1,
    ?_⟩
  rintro ⟨-, h⟩
  exact Witnesses.Diagonal.not_isCompactOperator_one h
