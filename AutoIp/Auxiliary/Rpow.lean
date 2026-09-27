/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Rpow

Identities for real powers.
-/

namespace AutoIp

/-- Halving the exponent undoes squaring: `(x ^ 2) ^ (ν / 2) = x ^ ν`. -/
public theorem rpow_sq_div_two {x : ℝ} (hx : 0 ≤ x) (ν : ℝ) : (x ^ 2) ^ (ν / 2) = x ^ ν := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx]
  congr 1
  push_cast
  ring

/-- `a (a²)^{ν/2} = (a²)^{(ν+1)/2}` for `a > 0`, because `a = (a²)^{1/2}`. -/
public theorem mul_rpow_sq_div_two {a : ℝ} (ha : 0 < a) {ν : ℝ} :
    a * (a ^ 2) ^ (ν / 2) = (a ^ 2) ^ ((ν + 1) / 2) := by
  have ha0 : (0 : ℝ) < a ^ 2 := pow_pos ha 2
  have hhalf : ((a ^ 2) : ℝ) ^ ((1 : ℝ) / 2) = a := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq ha.le]
  calc a * (a ^ 2) ^ (ν / 2)
      = (a ^ 2) ^ ((1 : ℝ) / 2) * (a ^ 2) ^ (ν / 2) := by rw [hhalf]
    _ = (a ^ 2) ^ ((1 : ℝ) / 2 + ν / 2) := (Real.rpow_add ha0 _ _).symm
    _ = (a ^ 2) ^ ((ν + 1) / 2) := by congr 1; ring

/-- `ρ^{ν/(ν+1)} ρ^{1/(ν+1)} = ρ` for `ρ > 0`. -/
public theorem rpow_split_rate {ρ ν : ℝ} (hρ : 0 < ρ) (hν1 : 0 < ν + 1) :
    ρ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1)) = ρ := by
  rw [← Real.rpow_add hρ, show ν / (ν + 1) + (1 : ℝ) / (ν + 1) = 1 by field_simp,
    Real.rpow_one]

/-- `(δ/ρ)^{ν/(ν+1)} ρ = δ^{ν/(ν+1)} ρ^{1/(ν+1)}` for `δ, ρ > 0`. -/
public theorem rpow_div_mul_rate {δ ρ ν : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hν1 : 0 < ν + 1) :
    (δ / ρ) ^ (ν / (ν + 1)) * ρ = δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1)) := by
  have hpa : (0 : ℝ) < ρ ^ (ν / (ν + 1)) := Real.rpow_pos_of_pos hρ _
  rw [Real.div_rpow hδ.le hρ.le, div_mul_eq_mul_div, div_eq_iff hpa.ne', mul_assoc,
    mul_comm (ρ ^ ((1 : ℝ) / (ν + 1))), rpow_split_rate hρ hν1]

/-- `α^{3/2} = α √α` for `α > 0`. -/
public theorem rpow_three_halves {α : ℝ} (hα : 0 < α) : α ^ ((3 : ℝ) / 2) = α * Real.sqrt α := by
  rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hα,
    Real.rpow_one]

end AutoIp
