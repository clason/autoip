module

import AutoIp._part_1_funcanal._ch_05_weak_convergence._lem_weak_limit_unique.Spec -- shake: keep

open scoped Topology

/-- The hypotheses of `TendstoWeakly.unique` can hold together. -/
theorem TendstoWeakly.unique_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (x3 : NormedAddCommGroup E), ∃ (x4 : NormedSpace 𝕜 E), ∃ (x : ℕ → E), ∃ (a : E), ∃ (b : E), (TendstoWeakly 𝕜 x a) ∧ (TendstoWeakly 𝕜 x b) :=
  ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, fun _ => 0, 0, 0,
    ⟨fun f => tendsto_const_nhds, fun f => tendsto_const_nhds⟩⟩

/-- The hypotheses of `TendstoWeakly.unique` can fail. -/
theorem TendstoWeakly.unique_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (x3 : NormedAddCommGroup E), ∃ (x4 : NormedSpace 𝕜 E), ∃ (x : ℕ → E), ∃ (a : E), ∃ (b : E), ¬ ((TendstoWeakly 𝕜 x a) ∧ (TendstoWeakly 𝕜 x b)) :=
  ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, fun _ => 1, 0, 0, by
      rintro ⟨h, -⟩
      have h1 := h (1 : ℝ →L[ℝ] ℝ)
      simp only [ContinuousLinearMap.one_apply] at h1
      exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h1)⟩
