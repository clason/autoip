/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace AutoIp

/-- `δ (δ/ρ)^{-1/(ν+1)} = δ^{ν/(ν+1)} ρ^{1/(ν+1)}` for `δ, ρ > 0` and `ν > -1`. -/
public theorem mul_rpow_neg_rate {δ ρ ν : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hν1 : 0 < ν + 1) :
    δ * (δ / ρ) ^ (-(1 : ℝ) / (ν + 1)) = δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1)) := by
  have hν1' : (ν : ℝ) + 1 ≠ 0 := hν1.ne'
  have h1 : (δ / ρ) ^ (-(1 : ℝ) / (ν + 1))
      = δ ^ (-(1 : ℝ) / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1)) := by
    rw [Real.div_rpow hδ.le hρ.le, div_eq_mul_inv]
    congr 1
    rw [show (-(1 : ℝ) / (ν + 1)) = -((1 : ℝ) / (ν + 1)) by ring, Real.rpow_neg hρ.le,
      inv_inv]
  rw [h1, ← mul_assoc]
  congr 1
  nth_rewrite 1 [← Real.rpow_one δ]
  rw [← Real.rpow_add hδ]
  congr 1
  field_simp
  ring

end AutoIp
