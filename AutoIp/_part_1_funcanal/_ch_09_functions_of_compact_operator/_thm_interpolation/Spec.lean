/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_frac_power
import AutoIp.Auxiliary.Rpow
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._thm_interpolation.Helpers

section _thm_interpolation

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- The interpolation inequality `‖|K|^s x‖ ≤ ‖|K|^r x‖^{s/r} ‖x‖^{1-s/r}` for `r > s ≥ 0`.
At `s = 0`, `|K|^0` is the identity: the fractional power is defined for `ν ≥ 0`, where the
blueprint defines it for `ν > 0`. -/
public theorem IsSingularSystem.norm_absRpow_le_rpow_mul_rpow (hs : IsSingularSystem K σ v u)
    {r s : ℝ} (hs0 : 0 ≤ s) (hsr : s < r) (x : E) :
    ‖hs.absRpow s hs0 x‖
      ≤ ‖hs.absRpow r (hs0.trans hsr.le) x‖ ^ (s / r) * ‖x‖ ^ (1 - s / r) := by
  rcases eq_or_lt_of_le hs0 with rfl | hspos
  · -- `s = 0`: both sides are `‖x‖`.
    simp [hs.absRpow_zero]
  have hr0 : (0 : ℝ) < r := hspos.trans hsr
  set θ := s / r with hθdef
  have hθ0 : 0 < θ := div_pos hspos hr0
  have hθ1 : θ < 1 := (div_lt_one hr0).mpr hsr
  have hτ : ∀ i, (0 : ℝ) < σ i ^ 2 := fun i => pow_pos (hs.pos i) 2
  set d : ι → ℝ := fun i => ‖(inner 𝕜 (v i) x : 𝕜)‖ ^ 2 with hddef
  have hd0 : ∀ i, 0 ≤ d i := fun i => by rw [hddef]; positivity
  -- the expansion of `|K| ^ t`, with coefficients written as powers of `σ i ^ 2`
  have habs : ∀ (t : ℝ) (ht : 0 < t), HasSum
      (fun i => ((RCLike.ofReal ((σ i ^ 2) ^ (t / 2)) : 𝕜) * inner 𝕜 (v i) x) • v i)
      (hs.absRpow t ht.le x) := by
    intro t ht
    refine (hs.hasSum_absRpow ht x).congr_fun fun i => ?_
    rw [AutoIp.rpow_sq_div_two (hs.pos i).le t]
  have hterm : ∀ (t : ℝ) (i : ι),
      ‖(RCLike.ofReal ((σ i ^ 2) ^ (t / 2)) : 𝕜) * inner 𝕜 (v i) x‖ ^ 2
        = (σ i ^ 2) ^ t * d i := by
    intro t i
    rw [norm_mul, RCLike.norm_ofReal, mul_pow,
      abs_of_nonneg (Real.rpow_nonneg (hτ i).le _), hddef]
    congr 1
    rw [← Real.rpow_natCast ((σ i ^ 2) ^ (t / 2)) 2, ← Real.rpow_mul (hτ i).le]
    norm_num
  have hsumm : ∀ t : ℝ, 0 < t → Summable (fun i => (σ i ^ 2) ^ t * d i) := by
    intro t ht
    exact ((hs.orthonormal_left.summable_iff_norm_sq_summable _).mp (habs t ht).summable).congr
      (hterm t)
  have hnorm : ∀ (t : ℝ) (ht : 0 < t),
      ‖hs.absRpow t ht.le x‖ ^ 2 = ∑' i, (σ i ^ 2) ^ t * d i := by
    intro t ht
    rw [hs.orthonormal_left.norm_sq_eq_tsum_norm_sq (habs t ht)]
    exact tsum_congr (hterm t)
  have hdsumm : Summable d := hs.orthonormal_left.inner_products_summable (x := x)
  have hdle : ∑' i, d i ≤ ‖x‖ ^ 2 := hs.orthonormal_left.tsum_inner_products_le x
  set A := ∑' i, (σ i ^ 2) ^ r * d i with hAdef
  set B := ∑' i, d i with hBdef
  have hA0 : 0 ≤ A := tsum_nonneg fun i => by positivity
  have hB0 : 0 ≤ B := tsum_nonneg hd0
  -- Hölder, with the conjugate pair `r / s`, `r / (r - s)`
  have hmain : ∑' i, (σ i ^ 2) ^ s * d i ≤ A ^ θ * B ^ (1 - θ) := by
    rw [hAdef, hBdef, hθdef]
    exact tsum_rpow_mul_le_rpow_mul_rpow (fun i => (hτ i).le) hd0 hdsumm hspos hsr
      (hsumm r hr0)
  -- unwind the squares
  have hpow : ∀ a b : ℝ, 0 ≤ a → (a ^ b) ^ (2 : ℕ) = (a ^ (2 : ℕ)) ^ b := by
    intro a b ha
    rw [← Real.rpow_natCast (a ^ b) 2, ← Real.rpow_natCast a 2, ← Real.rpow_mul ha,
      ← Real.rpow_mul ha, mul_comm]
  have hstep : A ^ θ * B ^ (1 - θ) ≤ A ^ θ * (‖x‖ ^ 2) ^ (1 - θ) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hB0 hdle (by linarith))
      (Real.rpow_nonneg hA0 θ)
  have hfin : ‖hs.absRpow s hs0 x‖ ^ 2
      ≤ (‖hs.absRpow r (hs0.trans hsr.le) x‖ ^ θ * ‖x‖ ^ (1 - θ)) ^ 2 := by
    have hAeq : A = ‖hs.absRpow r (hs0.trans hsr.le) x‖ ^ 2 := (hnorm r hr0).symm
    have e1 : (‖hs.absRpow r (hs0.trans hsr.le) x‖ ^ θ * ‖x‖ ^ (1 - θ)) ^ 2
        = A ^ θ * (‖x‖ ^ 2) ^ (1 - θ) := by
      rw [mul_pow, hpow _ _ (norm_nonneg _), hpow _ _ (norm_nonneg _), ← hAeq]
    rw [e1, hnorm s hspos]
    linarith [hmain, hstep]
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hfin

end _thm_interpolation
