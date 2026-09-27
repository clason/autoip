/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_filter.Spec

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable {K : E →L[𝕜] F}

/-- For a regularizing filter, `|1 - λ φ_α(λ)| ≤ 1 + C_φ` for all `α > 0` and all
`λ ∈ [0, κ]`, `λ = 0` included. -/
public theorem abs_one_sub_mul_le_one_add {φ : Set.Ioi (0 : ℝ) → ℝ → ℝ} {Cφ : ℝ}
    (hφ : IsRegularizingFilter K φ Cφ) {b : Set.Ioi (0 : ℝ)}
    {s : ℝ} (hsm : s ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2)) : |1 - s * φ b s| ≤ 1 + Cφ := by
  rcases hsm.1.lt_or_eq with h0 | h0
  · have h := hφ.mul_abs_le b s ⟨h0, hsm.2⟩
    have habs : |s * φ b s| ≤ Cφ := by rw [abs_mul, abs_of_pos h0]; exact h
    rw [abs_le] at habs ⊢
    constructor <;> linarith [habs.1, habs.2]
  · rw [← h0]
    simp only [zero_mul, sub_zero, abs_one]
    linarith [hφ.const_pos]

end AutoIp
