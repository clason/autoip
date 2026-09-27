/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_17_landweber._def_landweber
import AutoIp.Auxiliary.StepSize
import AutoIp._part_2_reg._ch_17_landweber._thm_landweber_residual_monotone
public import Mathlib.Analysis.Normed.Operator.Basic

section _thm_landweber_stopping_bound

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F}

/-- The discrepancy principle stops in `O(δ⁻²)` steps: for `x† = x ∈ X`, `τ > 1`, `δ > 0`
and `y^δ = z ∈ B_δ(K x†)`, the first index `m` with `‖K x^δ_m - y^δ‖ ≤ τ δ` exists and
satisfies `m ≤ ⌈ω⁻¹ (τ-1)⁻² ‖x†‖² δ⁻²⌉`.

The step size `ω ∈ (0, κ⁻¹)` is stated as `0 < ω` and `ωκ < 1`, which is the same for `K ≠ 0` and,
unlike the interval, makes no use of `0⁻¹`. It holds for every `K`, `K = 0` included. -/
public theorem landweber_stopping_le (K : E →L[𝕜] F) {ω : ℝ}
    (hω : 0 < ω ∧ ω * ‖K‖ ^ 2 < 1) {x : E} {τ δ : ℝ} (hτ : 1 < τ) (hδ : 0 < δ)
    {z : F} (hz : ‖z - K x‖ ≤ δ) :
    ∃ m : ℕ, ‖K (landweber K ω z m) - z‖ ≤ τ * δ ∧
      (∀ k < m, τ * δ < ‖K (landweber K ω z k) - z‖) ∧
      m ≤ ⌈ω⁻¹ * ((τ - 1) ^ 2)⁻¹ * ‖x‖ ^ 2 * (δ ^ 2)⁻¹⌉₊ := by
  classical
  obtain ⟨hω0, hωKlt⟩ := hω
  have hωK : ω * ‖K‖ ^ 2 ≤ 1 := hωKlt.le
  have hτ1 : 0 < τ - 1 := by linarith
  set y : F := K x with hydef
  set G : F →L[𝕜] F := ContinuousLinearMap.id 𝕜 F -
      (RCLike.ofReal ω : 𝕜) • (K ∘L ContinuousLinearMap.adjoint K) with hGdef
  have hGapp : ∀ w : F,
      G w = w - (RCLike.ofReal ω : 𝕜) • K (ContinuousLinearMap.adjoint K w) := by
    intro w; simp [hGdef]
  have hres : ∀ (w : F) (n : ℕ), w - K (landweber K ω w n) = (G ^ n) w := by
    intro w n
    induction n with
    | zero => simp [landweber_zero]
    | succ n ih =>
      have hsucc : (G ^ (n + 1)) w = G ((G ^ n) w) := by
        rw [pow_succ', mul_apply_eq_comp]
      have hrec := landweber_succ K ω w n
      rw [hsucc, ← ih, hGapp, hrec, map_add, map_smul]
      abel
  have hcontr : ∀ w : F, ‖G w‖ ≤ ‖w‖ := by
    intro w
    have h := sq_norm_sub_smul_apply_adjoint_le K hω0 hωK w
    have h2 : ‖G w‖ ^ 2 ≤ ‖w‖ ^ 2 := by
      rw [hGapp]
      nlinarith [mul_nonneg hω0.le (sq_nonneg ‖ContinuousLinearMap.adjoint K w‖)]
    exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg w) h2
  have hpow : ∀ (n : ℕ) (w : F), ‖(G ^ n) w‖ ≤ ‖w‖ := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      have hsucc : (G ^ (n + 1)) w = (G ^ n) (G w) := by
        rw [pow_succ, mul_apply_eq_comp]
      rw [hsucc]
      exact le_trans (ih (G w)) (hcontr w)
  -- one step of the error recursion for the *exact* datum `y`
  have hstep : ∀ n : ℕ, ‖landweber K ω y (n + 1) - x‖ ^ 2 +
      ω * ‖y - K (landweber K ω y n)‖ ^ 2 ≤ ‖landweber K ω y n - x‖ ^ 2 := by
    intro n
    have hrec := landweber_succ K ω y n
    have hEq : landweber K ω y (n + 1) - x = (landweber K ω y n - x) +
        (RCLike.ofReal ω : 𝕜) •
          ContinuousLinearMap.adjoint K (y - K (landweber K ω y n)) := by
      rw [hrec]; abel
    have hKe : K (landweber K ω y n - x) = -(y - K (landweber K ω y n)) := by
      rw [map_sub, ← hydef]; abel
    have hcross : RCLike.re (inner 𝕜 (landweber K ω y n - x)
        (ContinuousLinearMap.adjoint K (y - K (landweber K ω y n)))) =
        -‖y - K (landweber K ω y n)‖ ^ 2 := by
      rw [ContinuousLinearMap.adjoint_inner_right, hKe, inner_neg_left, map_neg,
        inner_self_eq_norm_sq]
    have hadj : ‖ContinuousLinearMap.adjoint K (y - K (landweber K ω y n))‖ ≤
        ‖K‖ * ‖y - K (landweber K ω y n)‖ := by
      calc ‖ContinuousLinearMap.adjoint K (y - K (landweber K ω y n))‖
          ≤ ‖ContinuousLinearMap.adjoint K‖ * ‖y - K (landweber K ω y n)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖K‖ * ‖y - K (landweber K ω y n)‖ := by
            rw [LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint K]
    have hq0 : ‖ContinuousLinearMap.adjoint K (y - K (landweber K ω y n))‖ ^ 2 ≤
        ‖K‖ ^ 2 * ‖y - K (landweber K ω y n)‖ ^ 2 := by
      nlinarith [norm_nonneg (ContinuousLinearMap.adjoint K (y - K (landweber K ω y n))),
        norm_nonneg (y - K (landweber K ω y n)), norm_nonneg K]
    rw [hEq, norm_add_sq (𝕜 := 𝕜), inner_smul_right, RCLike.re_ofReal_mul, hcross,
      norm_smul, RCLike.norm_ofReal, abs_of_pos hω0, mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left hq0 (sq_nonneg ω),
      mul_nonneg hω0.le (sq_nonneg ‖y - K (landweber K ω y n)‖)]
  have hkey : ∀ m : ℕ, ‖landweber K ω y m - x‖ ^ 2 + ω * m * ‖(G ^ m) y‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    intro m
    induction m with
    | zero => simp [landweber_zero]
    | succ m ih =>
      have h1 := hstep m
      rw [hres y m] at h1
      have hmono : ‖(G ^ (m + 1)) y‖ ≤ ‖(G ^ m) y‖ := by
        have hsucc : (G ^ (m + 1)) y = G ((G ^ m) y) := by
          rw [pow_succ', mul_apply_eq_comp]
        rw [hsucc]; exact hcontr _
      have h3 : ‖(G ^ (m + 1)) y‖ ^ 2 ≤ ‖(G ^ m) y‖ ^ 2 := by
        nlinarith [norm_nonneg ((G ^ (m + 1)) y), norm_nonneg ((G ^ m) y)]
      have hp1 : 0 ≤ ω * (m : ℝ) * (‖(G ^ m) y‖ ^ 2 - ‖(G ^ (m + 1)) y‖ ^ 2) :=
        mul_nonneg (mul_nonneg hω0.le (Nat.cast_nonneg m)) (by linarith)
      have hp2 : 0 ≤ ω * (‖(G ^ m) y‖ ^ 2 - ‖(G ^ (m + 1)) y‖ ^ 2) :=
        mul_nonneg hω0.le (by linarith)
      rw [show ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 by push_cast; ring]
      nlinarith [hp1, hp2, h1, ih]
  have hsplit : ∀ n : ℕ, ‖(G ^ n) z‖ ≤ ‖(G ^ n) y‖ + δ := by
    intro n
    have hdec : (G ^ n) z = (G ^ n) y + (G ^ n) (z - y) := by
      rw [← map_add]; congr 1; abel
    rw [hdec]
    exact le_trans (norm_add_le _ _) (by linarith [hpow n (z - y), hz])
  have hgoal : ∀ n : ℕ, ‖K (landweber K ω z n) - z‖ = ‖(G ^ n) z‖ := by
    intro n
    rw [← hres z n, norm_sub_rev]
  set M : ℕ := ⌈ω⁻¹ * ((τ - 1) ^ 2)⁻¹ * ‖x‖ ^ 2 * (δ ^ 2)⁻¹⌉₊ with hMdef
  have hMres : ‖(G ^ M) z‖ ≤ τ * δ := by
    rcases eq_or_lt_of_le (norm_nonneg x) with hx | hx
    · have hM0 : M = 0 := by
        rw [hMdef, show ω⁻¹ * ((τ - 1) ^ 2)⁻¹ * ‖x‖ ^ 2 * (δ ^ 2)⁻¹ = 0 by rw [← hx]; ring]
        simp
      have hy0 : y = 0 := by rw [hydef, show x = 0 from norm_eq_zero.mp hx.symm, map_zero]
      rw [hy0, sub_zero] at hz
      rw [hM0, show (G ^ 0) z = z by simp]
      nlinarith [hδ.le]
    · have hωne : ω ≠ 0 := hω0.ne'
      have hτne : τ - 1 ≠ 0 := hτ1.ne'
      have hδne : δ ≠ 0 := hδ.ne'
      have hMc : ω⁻¹ * ((τ - 1) ^ 2)⁻¹ * ‖x‖ ^ 2 * (δ ^ 2)⁻¹ ≤ (M : ℝ) := by
        rw [hMdef]; exact Nat.le_ceil _
      have hcpos : 0 < ω⁻¹ * ((τ - 1) ^ 2)⁻¹ * ‖x‖ ^ 2 * (δ ^ 2)⁻¹ :=
        mul_pos (mul_pos (mul_pos (inv_pos.mpr hω0) (inv_pos.mpr (pow_pos hτ1 2)))
          (pow_pos hx 2)) (inv_pos.mpr (pow_pos hδ 2))
      have hMpos : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le hcpos hMc
      have hmulpos : 0 < ω * ((τ - 1) ^ 2 * δ ^ 2) :=
        mul_pos hω0 (mul_pos (pow_pos hτ1 2) (pow_pos hδ 2))
      have hclear := mul_le_mul_of_nonneg_left hMc hmulpos.le
      rw [show ω * ((τ - 1) ^ 2 * δ ^ 2) *
          (ω⁻¹ * ((τ - 1) ^ 2)⁻¹ * ‖x‖ ^ 2 * (δ ^ 2)⁻¹) = ‖x‖ ^ 2 by field_simp] at hclear
      have hB2 : ω * (M : ℝ) * ‖(G ^ M) y‖ ^ 2 ≤ ‖x‖ ^ 2 := by
        nlinarith [hkey M, sq_nonneg ‖landweber K ω y M - x‖]
      have hωM0 : 0 < ω * (M : ℝ) := mul_pos hω0 hMpos
      have hBle : ‖(G ^ M) y‖ ^ 2 ≤ ((τ - 1) * δ) ^ 2 := by
        nlinarith [hB2, hclear, hωM0]
      have hyle : ‖(G ^ M) y‖ ≤ (τ - 1) * δ :=
        le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hτ1.le hδ.le) hBle
      have := hsplit M
      linarith
  have hex : ∃ n : ℕ, ‖K (landweber K ω z n) - z‖ ≤ τ * δ := ⟨M, by rw [hgoal]; exact hMres⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_, Nat.find_le (by rw [hgoal]; exact hMres)⟩
  intro k hk
  exact not_le.mp (Nat.find_min hex hk)

end AutoIp

end _thm_landweber_stopping_bound
