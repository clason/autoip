module

import AutoIp._part_2_reg._ch_18_discretization._thm_dual_lsq_convergence.Spec -- shake: keep
import AutoIpTests.Witnesses.Filtration

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.dualLsq_tendsto` can hold together. -/
theorem AutoIp.dualLsq_tendsto_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (Y : ℕ → Submodule 𝕜 F), ∃ (x12 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (Y n)), ∃ (y : F), (Monotone Y) ∧ (∀ (n : ℕ), Module.finrank 𝕜 ↥(Y n) = n) ∧ (Submodule.topologicalClosure (⨆ (n : ℕ), Y n) =
  (LinearMap.ker (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) T) : F →ₗ[𝕜] E))ᗮ) ∧ (y ∈ AutoIp.mpDomain T) :=
  by
  refine ⟨ℝ, inferInstance, Witnesses.Filtration.H, Witnesses.Filtration.H, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ContinuousLinearMap.id ℝ _, Witnesses.Filtration.X, fun _ => inferInstance, 0,
    Witnesses.Filtration.mono, Witnesses.Filtration.finrank_X, ?_, Submodule.zero_mem _⟩
  rw [ContinuousLinearMap.adjoint_id, ContinuousLinearMap.coe_id, LinearMap.ker_id,
    Submodule.bot_orthogonal_eq_top]
  exact Witnesses.Filtration.dense

/-- The hypotheses of `AutoIp.dualLsq_tendsto` can fail. -/
theorem AutoIp.dualLsq_tendsto_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (Y : ℕ → Submodule 𝕜 F), ∃ (x12 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (Y n)), ∃ (y : F), ¬ ((Monotone Y) ∧ (∀ (n : ℕ), Module.finrank 𝕜 ↥(Y n) = n) ∧ (Submodule.topologicalClosure (⨆ (n : ℕ), Y n) =
  (LinearMap.ker (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) T) : F →ₗ[𝕜] E))ᗮ) ∧ (y ∈ AutoIp.mpDomain T)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, fun _ => ⊥, fun _ => inferInstance, 0, ?_⟩
  rintro ⟨_, h, _⟩
  have h1 := h 1
  rw [finrank_bot] at h1
  exact absurd h1 (by norm_num)
