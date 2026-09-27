/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.Polynomial.Basic
import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Algebra.Order.Algebra

section _def_residual_polynomial

namespace AutoIp

/-- `{q_k}_{k ≥ 0}` is a residual family of real polynomials. -/
public structure IsResidualPolynomialFamily (q : ℕ → Polynomial ℝ) : Prop where
  /-- `q_k(0) = 1` for every `k`. -/
  eval_zero_eq_one : ∀ k : ℕ, (q k).eval 0 = 1
  /-- `deg q_k ≤ k` for every `k`. -/
  degree_le : ∀ k : ℕ, (q k).degree ≤ (k : ℕ)

/-- The semi-iterative filter `φ_k(λ) = (1 - q_k(λ))/λ` for `λ ≠ 0`, and `φ_k(0) = -q_k'(0)`.
It is defined for any family `q`, residual or not, and the formula is used for every `λ ≠ 0`,
not only `λ > 0`. -/
public noncomputable def semiIterativeFilter (q : ℕ → Polynomial ℝ) (k : ℕ) (lam : ℝ) : ℝ :=
  if lam = 0 then -(Polynomial.derivative (q k)).eval 0 else (1 - (q k).eval lam) / lam

/-- The clause `φ_k(0) = -q_k'(0)`. -/
public theorem semiIterativeFilter_zero (q : ℕ → Polynomial ℝ) (k : ℕ) :
    semiIterativeFilter q k 0 = -(q k).derivative.eval 0 := by
  simp [semiIterativeFilter]

/-- The clause `φ_k(λ) = (1 - q_k(λ))/λ`, here for every `λ ≠ 0`. -/
public theorem semiIterativeFilter_of_ne_zero {lam : ℝ} (h : lam ≠ 0) (q : ℕ → Polynomial ℝ)
    (k : ℕ) : semiIterativeFilter q k lam = (1 - (q k).eval lam) / lam := by
  simp [semiIterativeFilter, h]

/-- For a residual family, `φ_k` is a polynomial of degree at most `k - 1`. The degree bound is
written `< k`, which at `k = 0` makes `φ₀` the zero polynomial. -/
public theorem exists_eq_eval_of_isResidualPolynomialFamily {q : ℕ → Polynomial ℝ}
    (hq : IsResidualPolynomialFamily q) (k : ℕ) :
    ∃ r : Polynomial ℝ, (∀ t : ℝ, semiIterativeFilter q k t = r.eval t) ∧
      r.degree < (k : ℕ) := by
  classical
  have hdvd : ∃ r : Polynomial ℝ, 1 - q k = Polynomial.X * r := by
    have h : (Polynomial.X : Polynomial ℝ) ∣ (1 - q k) := by
      simp [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero, hq.eval_zero_eq_one k]
    exact h
  obtain ⟨r, hr⟩ := hdvd
  refine ⟨r, fun t => ?_, ?_⟩
  · rcases eq_or_ne t 0 with rfl | h
    · rw [semiIterativeFilter_zero]
      have hderiv := congrArg Polynomial.derivative hr
      rw [Polynomial.derivative_sub, Polynomial.derivative_one, Polynomial.derivative_mul,
        Polynomial.derivative_X] at hderiv
      have h2 := congrArg (fun p : Polynomial ℝ => p.eval 0) hderiv
      simpa using h2
    · rw [semiIterativeFilter_of_ne_zero h]
      have h1 : (1 : ℝ) - (q k).eval t = t * r.eval t := by
        have := congrArg (fun p : Polynomial ℝ => p.eval t) hr
        simpa using this
      rw [h1, mul_comm, mul_div_assoc, div_self h, mul_one]
  have hdq : (1 - q k).degree ≤ (k : ℕ) := by
    refine le_trans (Polynomial.degree_sub_le _ _) (max_le ?_ (hq.degree_le k))
    exact le_trans Polynomial.degree_one_le (by exact_mod_cast Nat.zero_le k)
  rcases eq_or_ne r 0 with rfl | hr0
  · simp
  · rw [hr, Polynomial.degree_mul, Polynomial.degree_X,
      Polynomial.degree_eq_natDegree hr0] at hdq
    rw [Polynomial.degree_eq_natDegree hr0]
    have hsucc : ((r.natDegree + 1 : ℕ) : WithBot ℕ) ≤ (k : ℕ) := by
      rw [Nat.cast_add, Nat.cast_one, add_comm]
      exact hdq
    exact_mod_cast Nat.lt_of_succ_le (by exact_mod_cast hsucc)

end AutoIp

end _def_residual_polynomial

/- The residual function of the semi-iterative method is `r_k = q_k`:
`1 - λ φ_k(λ) = q_k(λ)`. -/
example {q : ℕ → Polynomial ℝ} (hq : AutoIp.IsResidualPolynomialFamily q) (k : ℕ) (lam : ℝ) :
    1 - lam * AutoIp.semiIterativeFilter q k lam = (q k).eval lam := by
  rcases eq_or_ne lam 0 with rfl | h
  · simp [hq.eval_zero_eq_one k]
  · rw [AutoIp.semiIterativeFilter_of_ne_zero h, mul_div_cancel₀ _ h]
    ring

/- The method is `x_k := φ_k(K*K) K* y`: spectral regularization with the semi-iterative
filter `φ_k`. -/
example {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}
    (hs : IsSingularSystem K σ v u) (q : ℕ → Polynomial ℝ) (k : ℕ)
    (hb : ∃ C, ∀ i, |AutoIp.semiIterativeFilter q k (σ i ^ 2)| ≤ C) (α : Set.Ioi (0 : ℝ))
    (y : F) :
    AutoIp.spectralReg hs (fun _ => AutoIp.semiIterativeFilter q k) (fun _ => hb) α y
      = hs.funCalc (AutoIp.semiIterativeFilter q k) hb (K.adjoint y) := by
  rw [AutoIp.spectralReg_eq, ContinuousLinearMap.comp_apply]
