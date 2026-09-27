module

import AutoIp._part_2_reg._ch_17_landweber._thm_landweber_residual_monotone.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity
import AutoIpTests.Witnesses.Zero

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.landweber_adjoint_residual_ne_zero_iff` can hold together. -/
theorem AutoIp.landweber_adjoint_residual_ne_zero_iff_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ω : ℝ), ∃ (z : F), ∃ (m : ℕ), (0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) < (1 : ℝ) :=
  by
  have hω : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) * ‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ) < 1 := by
    rw [Witnesses.Identity.norm_one']; norm_num
  exact ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, 1 / 2, 0, 0, hω⟩

/-- The hypotheses of `AutoIp.landweber_adjoint_residual_ne_zero_iff` can fail. -/
theorem AutoIp.landweber_adjoint_residual_ne_zero_iff_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ω : ℝ), ∃ (z : F), ∃ (m : ℕ), ¬ ((0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) < (1 : ℝ)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, 0, 0, 0, ?_⟩
  intro H
  exact absurd H (by simp)

/-- The hypotheses of `AutoIp.landweber_residual_lt` can hold together. -/
theorem AutoIp.landweber_residual_lt_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ω : ℝ), ∃ (z : F), ∃ (m : ℕ), ((0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) < (1 : ℝ)) ∧ (((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K : F → E) ((K : E → F) (AutoIp.landweber K ω z m) - z) ≠
  (0 : E)) :=
  by
  have hω : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) * ‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ) < 1 := by
    rw [Witnesses.Identity.norm_one']; norm_num
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, 1 / 2, 1, 0, hω, ?_⟩
  rw [AutoIp.landweber_zero, map_zero, zero_sub, map_neg, Witnesses.Identity.adjoint_one_apply]
  norm_num

/-- The hypotheses of `AutoIp.landweber_residual_lt` can fail. -/
theorem AutoIp.landweber_residual_lt_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ω : ℝ), ∃ (z : F), ∃ (m : ℕ), ¬ (((0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) < (1 : ℝ)) ∧ (((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K : F → E) ((K : E → F) (AutoIp.landweber K ω z m) - z) ≠
  (0 : E))) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, 0, 0, 0, ?_⟩
  rintro ⟨H, _⟩
  exact absurd H (by simp)

/-- The hypotheses of `AutoIp.landweber_adjoint_residual_ne_zero_iff_of_dense` can hold together. -/
theorem AutoIp.landweber_adjoint_residual_ne_zero_iff_of_dense_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ω : ℝ), ∃ (z : F), ∃ (m : ℕ), ((0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) < (1 : ℝ)) ∧ (Submodule.topologicalClosure (LinearMap.range (↑K : E →ₗ[𝕜] F)) = ⊤) :=
  by
  have hω : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) * ‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ) < 1 := by
    rw [Witnesses.Identity.norm_one']; norm_num
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, 1 / 2, 0, 0, hω, ?_⟩
  have hr : LinearMap.range ((1 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) = ⊤ := LinearMap.range_id
  rw [hr]
  exact le_antisymm le_top (Submodule.le_topologicalClosure _)

/-- The hypotheses of `AutoIp.landweber_adjoint_residual_ne_zero_iff_of_dense` can fail. -/
theorem AutoIp.landweber_adjoint_residual_ne_zero_iff_of_dense_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ω : ℝ), ∃ (z : F), ∃ (m : ℕ), ¬ (((0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) < (1 : ℝ)) ∧ (Submodule.topologicalClosure (LinearMap.range (↑K : E →ₗ[𝕜] F)) = ⊤)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, 1, 0, 0, ?_⟩
  rintro ⟨_, H⟩
  rw [ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero,
    Witnesses.Zero.topologicalClosure_bot] at H
  exact bot_ne_top H
