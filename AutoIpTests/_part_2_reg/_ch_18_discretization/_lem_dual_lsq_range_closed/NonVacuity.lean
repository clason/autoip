module

import AutoIp._part_2_reg._ch_18_discretization._lem_dual_lsq_range_closed.Spec -- shake: keep
import AutoIpTests.Witnesses.Filtration

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.isClosed_range_dualLsq` can hold together. -/
theorem AutoIp.isClosed_range_dualLsq_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (Y : ℕ → Submodule 𝕜 F), ∃ (x10 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (Y n)), ∃ (n : ℕ), (Monotone Y) ∧ (∀ (n : ℕ), Module.finrank 𝕜 ↥(Y n) = n) :=
  by
  exact ⟨ℝ, inferInstance, ℝ, Witnesses.Filtration.H, inferInstance, inferInstance,
    inferInstance, inferInstance, Witnesses.Filtration.K, Witnesses.Filtration.X,
    fun _ => inferInstance, 0, Witnesses.Filtration.mono, Witnesses.Filtration.finrank_X⟩

/-- The hypotheses of `AutoIp.isClosed_range_dualLsq` can fail. -/
theorem AutoIp.isClosed_range_dualLsq_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (Y : ℕ → Submodule 𝕜 F), ∃ (x10 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (Y n)), ∃ (n : ℕ), ¬ ((Monotone Y) ∧ (∀ (n : ℕ), Module.finrank 𝕜 ↥(Y n) = n)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    0, fun _ => ⊥, fun _ => inferInstance, 0, ?_⟩
  rintro ⟨_, h⟩
  have h1 := h 1
  rw [finrank_bot] at h1
  exact absurd h1 (by norm_num)
