module

import AutoIp._part_1_funcanal._ch_05_weak_convergence._lem_weak_seq_cont.Spec -- shake: keep

open scoped Topology

/-- The hypotheses of `TendstoWeakly.map` can hold together. -/
theorem TendstoWeakly.map_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : NormedSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : NormedSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (x : ℕ → E), ∃ (a : E), TendstoWeakly 𝕜 x a :=
  ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    0, fun _ => 0, 0, fun f => tendsto_const_nhds⟩

/-- The hypotheses of `TendstoWeakly.map` can fail. -/
theorem TendstoWeakly.map_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : NormedSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : NormedSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (x : ℕ → E), ∃ (a : E), ¬ (TendstoWeakly 𝕜 x a) :=
  ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    0, fun _ => 1, 0, by
      intro h
      have h1 := h (1 : ℝ →L[ℝ] ℝ)
      simp only [ContinuousLinearMap.one_apply] at h1
      exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h1)⟩
