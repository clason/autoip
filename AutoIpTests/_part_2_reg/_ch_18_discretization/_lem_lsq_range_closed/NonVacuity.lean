module

import AutoIp._part_2_reg._ch_18_discretization._lem_lsq_range_closed.Spec -- shake: keep
import AutoIpTests.Witnesses.Filtration

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.isClosed_range_lsq` can hold together. -/
theorem AutoIp.isClosed_range_lsq_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (X : ℕ → Submodule 𝕜 E), ∃ (x10 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (X n)), ∃ (n : ℕ), (Monotone X) ∧ (∀ (n : ℕ), Module.finrank 𝕜 ↥(X n) = n) :=
  by
  exact ⟨ℝ, inferInstance, Witnesses.Filtration.H, ℝ, inferInstance, inferInstance,
    inferInstance, inferInstance, ContinuousLinearMap.adjoint Witnesses.Filtration.K,
    Witnesses.Filtration.X, fun _ => inferInstance, 0, Witnesses.Filtration.mono,
    Witnesses.Filtration.finrank_X⟩

/-- The hypotheses of `AutoIp.isClosed_range_lsq` can fail. -/
theorem AutoIp.isClosed_range_lsq_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (X : ℕ → Submodule 𝕜 E), ∃ (x10 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (X n)), ∃ (n : ℕ), ¬ ((Monotone X) ∧ (∀ (n : ℕ), Module.finrank 𝕜 ↥(X n) = n)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    0, fun _ => ⊥, fun _ => inferInstance, 0, ?_⟩
  rintro ⟨_, h⟩
  have h1 := h 1
  rw [finrank_bot] at h1
  exact absurd h1 (by norm_num)
