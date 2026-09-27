module

import AutoIp._part_1_funcanal._ch_03_hilbert_spaces._lem_closed_range_adjoint.Spec -- shake: keep
import AutoIpTests.Witnesses.Diagonal

/-- The hypotheses of `ContinuousLinearMap.isClosed_range_adjoint_of_isClosed_range` can hold together. -/
theorem ContinuousLinearMap.isClosed_range_adjoint_of_isClosed_range_satisfiable : ∃ (𝕜 : Type), ∃ (E : Type), ∃ (F : Type), ∃ (x3 : RCLike 𝕜), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), IsClosed (↑(LinearMap.range (↑T : E →ₗ[𝕜] F)) : Set F) :=
  by
  refine ⟨ℝ, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, ?_⟩
  exact by simp

/-- The hypotheses of `ContinuousLinearMap.isClosed_range_adjoint_of_isClosed_range` can fail. -/
theorem ContinuousLinearMap.isClosed_range_adjoint_of_isClosed_range_nontrivial : ∃ (𝕜 : Type), ∃ (E : Type), ∃ (F : Type), ∃ (x3 : RCLike 𝕜), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ¬ (IsClosed (↑(LinearMap.range (↑T : E →ₗ[𝕜] F)) : Set F)) :=
  ⟨ℝ, Witnesses.Diagonal.H, Witnesses.Diagonal.H, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, Witnesses.Diagonal.T, Witnesses.Diagonal.not_isClosed_range⟩

/-- The hypotheses of `ContinuousLinearMap.range_adjoint_eq_orthogonal_ker_of_isClosed_range` can hold together. -/
theorem ContinuousLinearMap.range_adjoint_eq_orthogonal_ker_of_isClosed_range_satisfiable : ∃ (𝕜 : Type), ∃ (E : Type), ∃ (F : Type), ∃ (x3 : RCLike 𝕜), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), IsClosed (↑(LinearMap.range (↑T : E →ₗ[𝕜] F)) : Set F) :=
  by
  refine ⟨ℝ, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, ?_⟩
  exact by simp

/-- The hypotheses of `ContinuousLinearMap.range_adjoint_eq_orthogonal_ker_of_isClosed_range` can fail. -/
theorem ContinuousLinearMap.range_adjoint_eq_orthogonal_ker_of_isClosed_range_nontrivial : ∃ (𝕜 : Type), ∃ (E : Type), ∃ (F : Type), ∃ (x3 : RCLike 𝕜), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ¬ (IsClosed (↑(LinearMap.range (↑T : E →ₗ[𝕜] F)) : Set F)) :=
  ⟨ℝ, Witnesses.Diagonal.H, Witnesses.Diagonal.H, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, Witnesses.Diagonal.T, Witnesses.Diagonal.not_isClosed_range⟩
