module

import AutoIp._part_1_funcanal._ch_05_weak_convergence._lem_strong_to_weak.Spec -- shake: keep

open scoped Topology

/-- The hypotheses of `TendstoWeakly.of_tendsto` can hold together. -/
theorem TendstoWeakly.of_tendsto_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (x3 : NormedAddCommGroup E), ∃ (x4 : NormedSpace 𝕜 E), ∃ (x : ℕ → E), ∃ (a : E), Filter.Tendsto x Filter.atTop (nhds a) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, fun _ => 0, 0, ?_⟩
  exact by simp

/-- The hypotheses of `TendstoWeakly.of_tendsto` can fail. -/
theorem TendstoWeakly.of_tendsto_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (x3 : NormedAddCommGroup E), ∃ (x4 : NormedSpace 𝕜 E), ∃ (x : ℕ → E), ∃ (a : E), ¬ (Filter.Tendsto x Filter.atTop (nhds a)) :=
  ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, fun _ => 1, 0, by
      intro h
      exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)⟩
