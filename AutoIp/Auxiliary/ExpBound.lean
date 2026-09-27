/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# ExpBound

Bounds of a power by an exponential via the maximum of `s ↦ s ^ b e ^ (-a s)`, in a sharp
form and a crude form.
-/

namespace AutoIp

/-- The maximum of `s ↦ s ^ b e ^ (-a s)` on `(0, ∞)`, attained at `s = b / a`:
`s ^ b e ^ (-a s) ≤ (b / a) ^ b e ^ (-b)`. -/
public theorem rpow_mul_exp_neg_le (a b s : ℝ) (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) :
    s ^ b * Real.exp (-(a * s)) ≤ (b / a) ^ b * Real.exp (-b) := by
  set q : ℝ := a * s / b with hq
  have hq0 : 0 < q := by positivity
  have h1 : q ≤ Real.exp (q - 1) := by
    have := Real.add_one_le_exp (q - 1); linarith
  have h2 : q ^ b ≤ (Real.exp (q - 1)) ^ b := Real.rpow_le_rpow hq0.le h1 hb.le
  rw [← Real.exp_mul] at h2
  have h3 : q ^ b = (a / b) ^ b * s ^ b := by
    rw [hq, show a * s / b = (a / b) * s by ring, Real.mul_rpow (by positivity) hs.le]
  rw [h3] at h2
  have h4 : (q - 1) * b = a * s - b := by rw [hq]; field_simp
  rw [h4] at h2
  have hab : (b / a) ^ b * (a / b) ^ b = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity),
      show b / a * (a / b) = 1 by field_simp, Real.one_rpow]
  have hmul := mul_le_mul_of_nonneg_left h2
    (show (0:ℝ) ≤ (b / a) ^ b * Real.exp (-(a * s)) by positivity)
  calc s ^ b * Real.exp (-(a * s))
      = (b / a) ^ b * Real.exp (-(a * s)) * ((a / b) ^ b * s ^ b) := by
        rw [show (b / a) ^ b * Real.exp (-(a * s)) * ((a / b) ^ b * s ^ b)
          = ((b / a) ^ b * (a / b) ^ b) * (s ^ b * Real.exp (-(a * s))) by ring,
          hab, one_mul]
    _ ≤ (b / a) ^ b * Real.exp (-(a * s)) * Real.exp (a * s - b) := hmul
    _ = (b / a) ^ b * Real.exp (-b) := by rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- `w ^ m ≤ (m / a) ^ m e ^ (a w)` for a natural exponent `m > 0`, `a > 0` and `w ≥ 0`. -/
public theorem pow_le_pow_div_mul_exp {a : ℝ} (ha : 0 < a) {mm : ℕ} (hm : 0 < mm)
    {w : ℝ} (hw : 0 ≤ w) : w ^ mm ≤ ((mm : ℝ) / a) ^ mm * Real.exp (a * w) := by
  have hm0 : (0:ℝ) < (mm : ℝ) := by exact_mod_cast hm
  rcases hw.lt_or_eq with hw0 | hw0
  · have h := rpow_mul_exp_neg_le a (mm : ℝ) w ha hm0 hw0
    rw [Real.rpow_natCast w mm, Real.rpow_natCast _ mm] at h
    have hexp : Real.exp (-(mm : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hpos : (0:ℝ) < Real.exp (a * w) := Real.exp_pos _
    have := mul_le_mul_of_nonneg_right h hpos.le
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at this
    refine this.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (by nlinarith [Real.exp_pos (a * w)]) (by positivity)
  · subst hw0
    rw [zero_pow hm.ne']
    positivity

end AutoIp
