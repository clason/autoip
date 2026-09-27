module

import AutoIp._part_2_reg._ch_18_discretization._lem_lsq_convergence_criterion.Spec -- shake: keep
import AutoIpTests.Witnesses.Filtration

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.lsq_tendsto_iff` can hold together. -/
theorem AutoIp.lsq_tendsto_iff_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (X : ℕ → Submodule 𝕜 E), ∃ (x12 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (X n)), ∃ (y : F), (Monotone X) ∧ (∀ (n : ℕ), Module.finrank 𝕜 ↥(X n) = n) ∧ (Submodule.topologicalClosure (⨆ (n : ℕ), X n) = ⊤) ∧ (y ∈ AutoIp.mpDomain T) :=
  by
  exact ⟨ℝ, inferInstance, Witnesses.Filtration.H, ℝ, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    ContinuousLinearMap.adjoint Witnesses.Filtration.K, Witnesses.Filtration.X,
    fun _ => inferInstance, 1, Witnesses.Filtration.mono, Witnesses.Filtration.finrank_X,
    Witnesses.Filtration.dense, Submodule.mem_sup_left ⟨Witnesses.Filtration.b 0, by
      rw [ContinuousLinearMap.coe_coe, Witnesses.Filtration.adjoint_K_apply,
        Witnesses.Filtration.inner_b_zero_self]⟩⟩

/-- The hypotheses of `AutoIp.lsq_tendsto_iff` can fail. -/
theorem AutoIp.lsq_tendsto_iff_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (X : ℕ → Submodule 𝕜 E), ∃ (x12 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (X n)), ∃ (y : F), ¬ ((Monotone X) ∧ (∀ (n : ℕ), Module.finrank 𝕜 ↥(X n) = n) ∧ (Submodule.topologicalClosure (⨆ (n : ℕ), X n) = ⊤) ∧ (y ∈ AutoIp.mpDomain T)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, fun _ => ⊥, fun _ => inferInstance, 0, ?_⟩
  rintro ⟨_, h, _⟩
  have h1 := h 1
  rw [finrank_bot] at h1
  exact absurd h1 (by norm_num)
