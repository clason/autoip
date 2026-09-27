module

import AutoIp._part_1_funcanal._ch_08_svd._thm_svd.Spec -- shake: keep
import AutoIpTests.Witnesses.Diagonal

open scoped InnerProductSpace

/-- The hypotheses of `IsCompactOperator.exists_isOrderedSingularSystem` can hold together. -/
theorem IsCompactOperator.exists_isOrderedSingularSystem_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), IsCompactOperator (⇑K : E → F) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, ?_⟩
  exact isCompactOperator_zero

/-- The hypotheses of `IsCompactOperator.exists_isOrderedSingularSystem` can fail. -/
theorem IsCompactOperator.exists_isOrderedSingularSystem_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ¬ (IsCompactOperator (⇑K : E → F)) :=
  ⟨ℝ, inferInstance, Witnesses.Diagonal.H, Witnesses.Diagonal.H, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, 1, Witnesses.Diagonal.not_isCompactOperator_one⟩
