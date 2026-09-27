module

import AutoIp._part_1_funcanal._ch_06_compact_operators._thm_compact_range_not_closed.Spec -- shake: keep
import AutoIpTests.Witnesses.Diagonal

open scoped Topology

/-- The hypotheses of `IsCompactOperator.not_isClosed_range_of_not_finiteDimensional` can hold together. -/
theorem IsCompactOperator.not_isClosed_range_of_not_finiteDimensional_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : NormedSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : NormedSpace 𝕜 F), ∃ (x8 : CompleteSpace E), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), (IsCompactOperator (⇑K : E → F)) ∧ (¬FiniteDimensional 𝕜 ↥(LinearMap.range (↑K : E →ₗ[𝕜] F))) :=
  by
  refine ⟨ℝ, inferInstance, Witnesses.Diagonal.H, Witnesses.Diagonal.H, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Witnesses.Diagonal.T, ?_⟩
  exact ⟨Witnesses.Diagonal.isCompactOperator_T,
    Witnesses.Diagonal.not_finiteDimensional_range⟩

/-- The hypotheses of `IsCompactOperator.not_isClosed_range_of_not_finiteDimensional` can fail. -/
theorem IsCompactOperator.not_isClosed_range_of_not_finiteDimensional_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : NormedSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : NormedSpace 𝕜 F), ∃ (x8 : CompleteSpace E), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ¬ ((IsCompactOperator (⇑K : E → F)) ∧ (¬FiniteDimensional 𝕜 ↥(LinearMap.range (↑K : E →ₗ[𝕜] F)))) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, ?_⟩
  rintro ⟨_, H⟩
  exact H (by rw [ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero]; infer_instance)
