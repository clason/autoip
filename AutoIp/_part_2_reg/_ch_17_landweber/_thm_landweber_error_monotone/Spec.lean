/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_17_landweber._def_landweber
public import Mathlib.Analysis.Normed.Operator.Basic

section _thm_landweber_error_monotone

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F}

/-- The error decreases while the residual exceeds twice the noise: for bounded `K`,
`x† = x` with `K x† = y`, `‖y - y^δ‖ ≤ δ` and `m ∈ ℕ`, if `‖K x^δ_m - y^δ‖ > 2δ`, then
`‖x^δ_{m+1} - x†‖ < ‖x^δ_m - x†‖`, for the datum `y^δ = z`.

`y` does not appear: the noise bound is stated as `‖y^δ - K x†‖ ≤ δ`.

The step size `ω ∈ (0, κ⁻¹)` is stated as `0 < ω` and `ωκ < 1`, which is the same for `K ≠ 0` and,
unlike the interval, makes no use of `0⁻¹`. It holds for every `K`, `K = 0` included. -/
public theorem landweber_error_lt (K : E →L[𝕜] F) {ω : ℝ}
    (hω : 0 < ω ∧ ω * ‖K‖ ^ 2 < 1) {x : E} {z : F} {δ : ℝ}
    (hz : ‖z - K x‖ ≤ δ) (m : ℕ) (hres : 2 * δ < ‖K (landweber K ω z m) - z‖) :
    ‖landweber K ω z (m + 1) - x‖ < ‖landweber K ω z m - x‖ := by
  obtain ⟨hω0, hωK⟩ := hω
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hz
  have hrec := landweber_succ K ω z m
  set xm := landweber K ω z m with hxmdef
  set ρ : F := z - K xm with hρdef
  have hρnorm : ‖ρ‖ = ‖K xm - z‖ := by rw [hρdef, norm_sub_rev]
  have hρpos : 2 * δ < ‖ρ‖ := by rw [hρnorm]; exact hres
  have hρ0 : 0 < ‖ρ‖ := lt_of_le_of_lt (by linarith) hρpos
  have hKe : K (xm - x) = -ρ + (z - K x) := by
    rw [map_sub, hρdef]; abel
  have hcross : RCLike.re (inner 𝕜 (xm - x) (ContinuousLinearMap.adjoint K ρ)) ≤
      -‖ρ‖ ^ 2 + δ * ‖ρ‖ := by
    rw [ContinuousLinearMap.adjoint_inner_right, hKe, inner_add_left, inner_neg_left,
      map_add, map_neg, inner_self_eq_norm_sq]
    have h1 := re_inner_le_norm (𝕜 := 𝕜) (z - K x) ρ
    have h2 : ‖z - K x‖ ≤ δ := hz
    nlinarith [norm_nonneg ρ]
  have hadj : ‖ContinuousLinearMap.adjoint K ρ‖ ≤ ‖K‖ * ‖ρ‖ := by
    calc ‖ContinuousLinearMap.adjoint K ρ‖ ≤ ‖ContinuousLinearMap.adjoint K‖ * ‖ρ‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖K‖ * ‖ρ‖ := by
          rw [LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint K]
  have hq0 : ‖ContinuousLinearMap.adjoint K ρ‖ ^ 2 ≤ ‖K‖ ^ 2 * ‖ρ‖ ^ 2 := by
    nlinarith [norm_nonneg (ContinuousLinearMap.adjoint K ρ), norm_nonneg ρ, norm_nonneg K]
  have key : ‖landweber K ω z (m + 1) - x‖ ^ 2 < ‖xm - x‖ ^ 2 := by
    have hEq : landweber K ω z (m + 1) - x =
        (xm - x) + (RCLike.ofReal ω : 𝕜) • ContinuousLinearMap.adjoint K ρ := by
      rw [hrec]; abel
    rw [hEq, norm_add_sq (𝕜 := 𝕜), inner_smul_right, RCLike.re_ofReal_mul, norm_smul,
      RCLike.norm_ofReal, abs_of_pos hω0, mul_pow]
    have h1 : 2 * (ω * RCLike.re (inner 𝕜 (xm - x) (ContinuousLinearMap.adjoint K ρ))) ≤
        2 * (ω * (-‖ρ‖ ^ 2 + δ * ‖ρ‖)) := by
      have := mul_le_mul_of_nonneg_left hcross hω0.le
      linarith
    have h2 : ω ^ 2 * ‖ContinuousLinearMap.adjoint K ρ‖ ^ 2 ≤ ω * ‖ρ‖ ^ 2 := by
      have ha := mul_le_mul_of_nonneg_left hq0 (sq_nonneg ω)
      have hb : 0 ≤ (1 - ω * ‖K‖ ^ 2) * (ω * ‖ρ‖ ^ 2) :=
        mul_nonneg (by linarith) (mul_nonneg hω0.le (sq_nonneg ‖ρ‖))
      nlinarith
    have h3 : 0 < ω * ‖ρ‖ * (‖ρ‖ - 2 * δ) :=
      mul_pos (mul_pos hω0 hρ0) (by linarith)
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) key

end AutoIp

end _thm_landweber_error_monotone
