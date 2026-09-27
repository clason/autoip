/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_standard_filters
public import AutoIp._part_2_reg._ch_20_iterated_tikhonov._def_landweber_residual_poly
public import AutoIp._part_2_reg._ch_20_iterated_tikhonov._def_residual_polynomial
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.ComputeDegree
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init

section _lem_landweber_residual_polynomial

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- `{q_k}` with `q_k(λ) = (1 - ωλ)^k` is a residual family, and for `k ≥ 1` its semi-iterative
filter is the Landweber filter at `α = 1/k`. It holds for every real `ω`, where the prose fixes
`ω ∈ (0, κ⁻¹]`. -/
public theorem landweber_isResidualPolynomialFamily {ω : ℝ} :
    IsResidualPolynomialFamily (landweberResidualPoly ω) ∧
      ∀ (k : ℕ) (hk : 0 < k), ∀ lam : ℝ,
        semiIterativeFilter (landweberResidualPoly ω) k lam =
          landweberFilter ω ⟨1 / (k : ℝ), Set.mem_Ioi.2 (by positivity)⟩ lam := by
  have hd : Polynomial.derivative ((1 : Polynomial ℝ) - Polynomial.C ω * Polynomial.X)
      = -Polynomial.C ω := by
    simp
  refine ⟨⟨fun k => by simp [landweberResidualPoly_apply], fun k => ?_⟩, ?_⟩
  · have h1 : ((1 : Polynomial ℝ) - Polynomial.C ω * Polynomial.X).degree ≤ 1 := by
      compute_degree
    simpa [landweberResidualPoly_apply] using Polynomial.degree_pow_le_of_le k h1
  · intro k hk lam
    have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    rcases eq_or_ne lam 0 with rfl | h
    · rw [semiIterativeFilter_zero, landweberFilter_zero, landweberResidualPoly_apply]
      have hev : (Polynomial.derivative
          (((1 : Polynomial ℝ) - Polynomial.C ω * Polynomial.X) ^ k)).eval 0
          = -((k : ℝ) * ω) := by
        rw [Polynomial.derivative_pow, hd]
        simp
      rw [hev, neg_neg, div_div_eq_mul_div, div_one]
      ring
    · rw [semiIterativeFilter_of_ne_zero h, landweberFilter_of_ne_zero h,
        one_div_one_div, Real.rpow_natCast, div_eq_inv_mul, landweberResidualPoly_apply]
      simp

/-- `{q_k}` with `q_k(λ) = (1 - ωλ)^k` is a residual family. It holds for every real `ω`, where
the prose fixes `ω ∈ (0, κ⁻¹]`. -/
public theorem landweberResidualPoly_isResidualPolynomialFamily (ω : ℝ) :
    IsResidualPolynomialFamily (landweberResidualPoly ω) :=
  (landweber_isResidualPolynomialFamily (ω := ω)).1

/-- For `k ≥ 1` the semi-iterative filter of `q_k(λ) = (1 - ωλ)^k` is the Landweber filter at
`α = 1/k`. It holds for every real `ω`, where the prose fixes `ω ∈ (0, κ⁻¹]`. -/
public theorem semiIterativeFilter_landweberResidualPoly {ω : ℝ} {k : ℕ} (hk : 0 < k)
    (lam : ℝ) :
    semiIterativeFilter (landweberResidualPoly ω) k lam =
      landweberFilter ω ⟨1 / (k : ℝ), Set.mem_Ioi.2 (by positivity)⟩ lam :=
  (landweber_isResidualPolynomialFamily (ω := ω)).2 k hk lam

end AutoIp

end _lem_landweber_residual_polynomial
