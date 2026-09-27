/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_frac_power
import AutoIp.Auxiliary.Rpow
import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init

open scoped InnerProductSpace
variable {ι : Type*}

/-- Interpolation of a weighted `ℓ¹` sum: for `0 < s < r` and `θ = s / r`,
`∑ᵢ wᵢ ^ s dᵢ ≤ (∑ᵢ wᵢ ^ r dᵢ) ^ θ * (∑ᵢ dᵢ) ^ (1 - θ)`. Summability of the left-hand family is
not assumed: without it the sum is `0` and the bound is trivial. -/
public theorem tsum_rpow_mul_le_rpow_mul_rpow {w d : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hd : ∀ i, 0 ≤ d i) (hdsum : Summable d) {r s : ℝ} (hs0 : 0 < s) (hsr : s < r)
    (hsum : Summable fun i => w i ^ r * d i) :
    ∑' i, w i ^ s * d i
      ≤ (∑' i, w i ^ r * d i) ^ (s / r) * (∑' i, d i) ^ (1 - s / r) := by
  have hr0 : (0 : ℝ) < r := hs0.trans hsr
  set θ := s / r with hθdef
  have hθ0 : 0 < θ := div_pos hs0 hr0
  have hθ1 : θ < 1 := (div_lt_one hr0).mpr hsr
  have hθ1' : (0 : ℝ) < 1 - θ := sub_pos.mpr hθ1
  have hrs : r * θ = s := by rw [hθdef]; field_simp
  have hwd : ∀ i, (0 : ℝ) ≤ w i ^ r * d i :=
    fun i => mul_nonneg (Real.rpow_nonneg (hw i) r) (hd i)
  have hpq : (θ⁻¹).HolderConjugate ((1 - θ)⁻¹) :=
    ⟨by rw [inv_inv, inv_inv, inv_one]; ring, inv_pos.mpr hθ0, inv_pos.mpr hθ1'⟩
  -- the three pointwise identities that turn Hölder's shape into this one
  have hterm : ∀ i, (w i ^ r * d i) ^ θ * d i ^ (1 - θ) = w i ^ s * d i := by
    intro i
    rcases eq_or_lt_of_le (hd i) with hdi | hdi
    · rw [← hdi, mul_zero, Real.zero_rpow hθ0.ne', Real.zero_rpow hθ1'.ne', mul_zero, mul_zero]
    · rw [Real.mul_rpow (Real.rpow_nonneg (hw i) r) (hd i), ← Real.rpow_mul (hw i), hrs,
        mul_assoc, ← Real.rpow_add hdi, show θ + (1 - θ) = 1 by ring, Real.rpow_one]
  have hfeq : ∀ i, ((w i ^ r * d i) ^ θ) ^ θ⁻¹ = w i ^ r * d i := fun i => by
    rw [← Real.rpow_mul (hwd i), mul_inv_cancel₀ hθ0.ne', Real.rpow_one]
  have hgeq : ∀ i, (d i ^ (1 - θ)) ^ (1 - θ)⁻¹ = d i := fun i => by
    rw [← Real.rpow_mul (hd i), mul_inv_cancel₀ hθ1'.ne', Real.rpow_one]
  calc ∑' i, w i ^ s * d i
      = ∑' i, (w i ^ r * d i) ^ θ * d i ^ (1 - θ) := tsum_congr fun i => (hterm i).symm
    _ ≤ (∑' i, ((w i ^ r * d i) ^ θ) ^ θ⁻¹) ^ (1 / θ⁻¹)
          * (∑' i, (d i ^ (1 - θ)) ^ (1 - θ)⁻¹) ^ (1 / (1 - θ)⁻¹) :=
        Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hpq
          (fun i => Real.rpow_nonneg (hwd i) θ) (fun i => Real.rpow_nonneg (hd i) _)
          (hsum.congr fun i => (hfeq i).symm) (hdsum.congr fun i => (hgeq i).symm)
    _ = (∑' i, w i ^ r * d i) ^ θ * (∑' i, d i) ^ (1 - θ) := by
        rw [tsum_congr hfeq, tsum_congr hgeq, one_div, inv_inv, one_div, inv_inv]
