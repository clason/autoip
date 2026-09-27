module

import AutoIp._part_1_funcanal._ch_05_weak_convergence._thm_radon_riesz.Spec -- shake: keep
import AutoIpTests.Witnesses.Diagonal

open scoped InnerProductSpace Topology

/-- The hypotheses of `TendstoWeakly.tendsto_of_tendsto_norm` can hold together. -/
theorem TendstoWeakly.tendsto_of_tendsto_norm_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (H : Type), ∃ (x3 : NormedAddCommGroup H), ∃ (x4 : InnerProductSpace 𝕜 H), ∃ (x : ℕ → H), ∃ (a : H), (TendstoWeakly 𝕜 x a) ∧ (Filter.Tendsto (fun (n : ℕ) => ‖x n‖) Filter.atTop (nhds ‖a‖)) :=
  ⟨ℝ, inferInstance, Witnesses.Diagonal.H, inferInstance, inferInstance, fun _ => 0, 0,
    ⟨fun f => by simpa using tendsto_const_nhds, by simpa using tendsto_const_nhds⟩⟩

/-- The hypotheses of `TendstoWeakly.tendsto_of_tendsto_norm` can fail. -/
theorem TendstoWeakly.tendsto_of_tendsto_norm_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (H : Type), ∃ (x3 : NormedAddCommGroup H), ∃ (x4 : InnerProductSpace 𝕜 H), ∃ (x : ℕ → H), ∃ (a : H), ¬ ((TendstoWeakly 𝕜 x a) ∧ (Filter.Tendsto (fun (n : ℕ) => ‖x n‖) Filter.atTop (nhds ‖a‖))) :=
  ⟨ℝ, inferInstance, Witnesses.Diagonal.H, inferInstance, inferInstance, fun _ => 0, Witnesses.Diagonal.y, by
      rintro ⟨-, h⟩
      simp only [norm_zero] at h
      exact Witnesses.Diagonal.norm_y_ne_zero (tendsto_nhds_unique tendsto_const_nhds h).symm⟩
