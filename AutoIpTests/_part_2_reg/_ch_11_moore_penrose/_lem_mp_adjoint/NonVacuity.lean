module

import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_adjoint.Spec -- shake: keep
import AutoIpTests.Witnesses.Diagonal

open scoped InnerProductSpace

/-- The hypotheses of `AutoIp.adjoint_moorePenroseL_apply` can hold together. -/
theorem AutoIp.adjoint_moorePenroseL_apply_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (x : E), IsClosed (↑(LinearMap.range (↑T : E →ₗ[𝕜] F)) : Set F) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, 0, ?_⟩
  exact by simp

/-- The hypotheses of `AutoIp.adjoint_moorePenroseL_apply` can fail. -/
theorem AutoIp.adjoint_moorePenroseL_apply_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (x : E), ¬ (IsClosed (↑(LinearMap.range (↑T : E →ₗ[𝕜] F)) : Set F)) :=
  ⟨ℝ, inferInstance, Witnesses.Diagonal.H, Witnesses.Diagonal.H, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, Witnesses.Diagonal.T,
    Witnesses.Diagonal.y, Witnesses.Diagonal.not_isClosed_range⟩

/-- The hypotheses of `AutoIp.adjoint_moorePenrose` can hold together. -/
theorem AutoIp.adjoint_moorePenrose_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), IsClosed (↑(LinearMap.range (↑T : E →ₗ[𝕜] F)) : Set F) :=
  ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, by simp⟩

/-- The hypotheses of `AutoIp.adjoint_moorePenrose` can fail. -/
theorem AutoIp.adjoint_moorePenrose_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ¬ (IsClosed (↑(LinearMap.range (↑T : E →ₗ[𝕜] F)) : Set F)) :=
  ⟨ℝ, inferInstance, Witnesses.Diagonal.H, Witnesses.Diagonal.H, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, Witnesses.Diagonal.T,
    Witnesses.Diagonal.not_isClosed_range⟩
