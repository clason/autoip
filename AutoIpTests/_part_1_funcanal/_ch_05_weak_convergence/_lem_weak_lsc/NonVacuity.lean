module

import AutoIp._part_1_funcanal._ch_05_weak_convergence._lem_weak_lsc.Spec -- shake: keep

open scoped Topology

/-- The hypotheses of `TendstoWeakly.norm_le_liminf_norm` can hold together. -/
theorem TendstoWeakly.norm_le_liminf_norm_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (x3 : NormedAddCommGroup E), ∃ (x4 : NormedSpace 𝕜 E), ∃ (x : ℕ → E), ∃ (a : E), TendstoWeakly 𝕜 x a :=
  ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, fun _ => 0, 0,
    fun f => tendsto_const_nhds⟩

/-- The hypotheses of `TendstoWeakly.norm_le_liminf_norm` can fail. -/
theorem TendstoWeakly.norm_le_liminf_norm_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (x3 : NormedAddCommGroup E), ∃ (x4 : NormedSpace 𝕜 E), ∃ (x : ℕ → E), ∃ (a : E), ¬ (TendstoWeakly 𝕜 x a) :=
  ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, fun _ => 1, 0, by
      intro h
      have h1 := h (1 : ℝ →L[ℝ] ℝ)
      simp only [ContinuousLinearMap.one_apply] at h1
      have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds h1
      exact one_ne_zero this⟩
