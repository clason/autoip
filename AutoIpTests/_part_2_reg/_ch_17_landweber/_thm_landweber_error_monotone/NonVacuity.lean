module

import AutoIp._part_2_reg._ch_17_landweber._thm_landweber_error_monotone.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.landweber_error_lt` can hold together. -/
theorem AutoIp.landweber_error_lt_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ω : ℝ), ∃ (x : E), ∃ (z : F), ∃ (δ : ℝ), ∃ (m : ℕ), ((0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) < (1 : ℝ)) ∧ (‖z - (K : E → F) x‖ ≤ δ) ∧ ((2 : ℝ) * δ < ‖(K : E → F) (AutoIp.landweber K ω z m) - z‖) :=
  by
  have hω : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) * ‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ) < 1 := by
    rw [Witnesses.Identity.norm_one']; norm_num
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, 1 / 2, 1, 1, 0, 0, hω, by simp, ?_⟩
  rw [AutoIp.landweber_zero, map_zero, zero_sub, norm_neg]
  norm_num

/-- The hypotheses of `AutoIp.landweber_error_lt` can fail. -/
theorem AutoIp.landweber_error_lt_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ω : ℝ), ∃ (x : E), ∃ (z : F), ∃ (δ : ℝ), ∃ (m : ℕ), ¬ (((0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) < (1 : ℝ)) ∧ (‖z - (K : E → F) x‖ ≤ δ) ∧ ((2 : ℝ) * δ < ‖(K : E → F) (AutoIp.landweber K ω z m) - z‖)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, 0, 0, 0, 0, 0, ?_⟩
  rintro ⟨H, _, _⟩
  exact absurd H (by simp)
