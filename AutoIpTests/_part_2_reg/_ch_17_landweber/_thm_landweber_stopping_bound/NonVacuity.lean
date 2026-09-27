module

import AutoIp._part_2_reg._ch_17_landweber._thm_landweber_stopping_bound.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.landweber_stopping_le` can hold together. -/
theorem AutoIp.landweber_stopping_le_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ω : ℝ), ∃ (x : E), ∃ (τ : ℝ), ∃ (δ : ℝ), ∃ (z : F), ((0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) < (1 : ℝ)) ∧ ((1 : ℝ) < τ) ∧ ((0 : ℝ) < δ) ∧ (‖z - (K : E → F) x‖ ≤ δ) :=
  by
  have hω : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) * ‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ) < 1 := by
    rw [Witnesses.Identity.norm_one']; norm_num
  exact ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, 1 / 2, 0, 2, 1, 0, hω, by norm_num, one_pos, by simp⟩

/-- The hypotheses of `AutoIp.landweber_stopping_le` can fail. -/
theorem AutoIp.landweber_stopping_le_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ω : ℝ), ∃ (x : E), ∃ (τ : ℝ), ∃ (δ : ℝ), ∃ (z : F), ¬ (((0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) < (1 : ℝ)) ∧ ((1 : ℝ) < τ) ∧ ((0 : ℝ) < δ) ∧ (‖z - (K : E → F) x‖ ≤ δ)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, 0, 0, 0, 1, 0, ?_⟩
  rintro ⟨_, H, _, _⟩
  exact absurd H (by norm_num)
