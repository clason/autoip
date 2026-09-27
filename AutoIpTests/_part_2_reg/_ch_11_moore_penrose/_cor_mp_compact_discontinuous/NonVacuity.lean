module

import AutoIp._part_2_reg._ch_11_moore_penrose._cor_mp_compact_discontinuous.Spec -- shake: keep
import AutoIpTests.Witnesses.Diagonal

open scoped Topology
open scoped InnerProductSpace

/-- The hypotheses of `IsCompactOperator.isClosed_range_iff_finiteDimensional` can hold together. -/
theorem IsCompactOperator.isClosed_range_iff_finiteDimensional_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : NormedSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : NormedSpace 𝕜 F), ∃ (x8 : CompleteSpace E), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), IsCompactOperator (⇑K : E → F) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, ?_⟩
  exact isCompactOperator_zero

/-- The hypotheses of `IsCompactOperator.isClosed_range_iff_finiteDimensional` can fail. -/
theorem IsCompactOperator.isClosed_range_iff_finiteDimensional_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : NormedSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : NormedSpace 𝕜 F), ∃ (x8 : CompleteSpace E), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ¬ (IsCompactOperator (⇑K : E → F)) :=
  ⟨ℝ, inferInstance, Witnesses.Diagonal.H, Witnesses.Diagonal.H, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, 1, Witnesses.Diagonal.not_isCompactOperator_one⟩

/-- The hypotheses of `AutoIp.not_exists_norm_moorePenrose_le_of_isCompactOperator` can hold together. -/
theorem AutoIp.not_exists_norm_moorePenrose_le_of_isCompactOperator_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), (IsCompactOperator (⇑K : E → F)) ∧ (¬FiniteDimensional 𝕜 ↥(LinearMap.range (↑K : E →ₗ[𝕜] F))) :=
  ⟨ℝ, inferInstance, Witnesses.Diagonal.H, Witnesses.Diagonal.H, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, Witnesses.Diagonal.T,
    Witnesses.Diagonal.isCompactOperator_T, Witnesses.Diagonal.not_finiteDimensional_range⟩

/-- The hypotheses of `AutoIp.not_exists_norm_moorePenrose_le_of_isCompactOperator` can fail. -/
theorem AutoIp.not_exists_norm_moorePenrose_le_of_isCompactOperator_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ¬ ((IsCompactOperator (⇑K : E → F)) ∧ (¬FiniteDimensional 𝕜 ↥(LinearMap.range (↑K : E →ₗ[𝕜] F)))) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, ?_⟩
  rintro ⟨_, H⟩
  exact H (by rw [ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero]; infer_instance)
