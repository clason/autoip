/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_standard_filters

section _def_iterated_tikhonov

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The iterated Tikhonov filter `φ^(m)_α(λ) = λ⁻¹ (1 - (α/(α+λ))^m)` for `λ ≠ 0`, and
`φ^(m)_α(0) = m/α`, for `α > 0`. The index `m` may be `0`, where the prose has `m ≥ 1`, and the
formula is used for every `λ ≠ 0`, not only `λ > 0`. -/
public noncomputable def iteratedTikhonovFilter (m : ℕ) (α : Set.Ioi (0 : ℝ)) (lam : ℝ) : ℝ :=
  if lam = 0 then (m : ℝ) / (α : ℝ)
  else lam⁻¹ * (1 - ((α : ℝ) / ((α : ℝ) + lam)) ^ m)

/-- The clause `φ^(m)_α(0) = m/α`. -/
public theorem iteratedTikhonovFilter_zero (m : ℕ) (α : Set.Ioi (0 : ℝ)) :
    iteratedTikhonovFilter m α 0 = (m : ℝ) / (α : ℝ) := by
  simp [iteratedTikhonovFilter]

/-- The clause `φ^(m)_α(λ) = λ⁻¹ (1 - (α/(α+λ))^m)`, here for every `λ ≠ 0`. -/
public theorem iteratedTikhonovFilter_of_ne_zero {lam : ℝ} (h : lam ≠ 0) (m : ℕ)
    (α : Set.Ioi (0 : ℝ)) :
    iteratedTikhonovFilter m α lam = lam⁻¹ * (1 - ((α : ℝ) / ((α : ℝ) + lam)) ^ m) := by
  simp [iteratedTikhonovFilter, h]

/-- For `m = 1` the filter is the Tikhonov filter, on `λ ≥ 0`. -/
public theorem iteratedTikhonovFilter_one {α : Set.Ioi (0 : ℝ)} {lam : ℝ} (hlam : 0 ≤ lam) :
    iteratedTikhonovFilter 1 α lam = tikhonovFilter α lam := by
  have hα : (0 : ℝ) < (α : ℝ) := α.2
  have hsum : (0 : ℝ) < (α : ℝ) + lam := by linarith
  rcases eq_or_ne lam 0 with rfl | h
  · rw [iteratedTikhonovFilter_zero, tikhonovFilter_apply, zero_add, Nat.cast_one, one_div]
  · rw [iteratedTikhonovFilter_of_ne_zero h, tikhonovFilter_apply, pow_one]
    field_simp
    ring

/-- The residual function `r^(m)_α(λ) = 1 - λ φ^(m)_α(λ) = (α/(α+λ))^m`, for `λ > 0`. -/
public theorem one_sub_mul_iteratedTikhonovFilter {m : ℕ} {α : Set.Ioi (0 : ℝ)} {lam : ℝ}
    (hlam : 0 < lam) :
    1 - lam * iteratedTikhonovFilter m α lam = ((α : ℝ) / ((α : ℝ) + lam)) ^ m := by
  rw [iteratedTikhonovFilter_of_ne_zero hlam.ne', ← mul_assoc, mul_inv_cancel₀ hlam.ne',
    one_mul]
  ring

end AutoIp

end _def_iterated_tikhonov
