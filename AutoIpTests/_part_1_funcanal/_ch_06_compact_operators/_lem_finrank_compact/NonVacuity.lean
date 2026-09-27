module

import AutoIp._part_1_funcanal._ch_06_compact_operators._lem_finrank_compact.Spec -- shake: keep
import AutoIpTests.Witnesses.Diagonal

open scoped Topology

/-- The hypotheses of `IsCompactOperator.of_finiteDimensional_range` can hold together. -/
theorem IsCompactOperator.of_finiteDimensional_range_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : NormedSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : NormedSpace 𝕜 F), ∃ (T : E →L[𝕜] F), FiniteDimensional 𝕜 ↥(LinearMap.range (↑T : E →ₗ[𝕜] F)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 0
    , ?_⟩
  exact by rw [ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero]; infer_instance

/-- The hypotheses of `IsCompactOperator.of_finiteDimensional_range` can fail. -/
theorem IsCompactOperator.of_finiteDimensional_range_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : NormedSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : NormedSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ¬ (FiniteDimensional 𝕜 ↥(LinearMap.range (↑T : E →ₗ[𝕜] F))) :=
  ⟨ℝ, inferInstance, Witnesses.Diagonal.H, Witnesses.Diagonal.H, inferInstance, inferInstance,
    inferInstance, inferInstance, Witnesses.Diagonal.T,
    Witnesses.Diagonal.not_finiteDimensional_range⟩
