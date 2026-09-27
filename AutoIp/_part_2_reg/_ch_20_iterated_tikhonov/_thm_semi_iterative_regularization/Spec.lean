/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_13_regularization._def_regularization
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_filter
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
public import AutoIp._part_2_reg._ch_20_iterated_tikhonov._def_residual_polynomial
import AutoIp._part_2_reg._ch_15_spectral_regularization._thm_spectral_is_regularization
import Mathlib.Topology.Algebra.Polynomial
import AutoIp.Auxiliary.BoundedOnIcc

import Mathlib.Topology.Order.AtTopBotIxx
section _thm_semi_iterative_regularization

namespace AutoIp

open Filter Topology
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- For a residual family `{q_k}` with (1) `|q_k(λ)| ≤ C_q` on `[0, κ]` for all `k` and (2)
`q_k(λ) → 0` for every `λ ∈ (0, κ]`, the semi-iterative filter reindexed by `α` is a
regularizing filter with `C_φ = 1 + C_q`. The reindexing is by any map `κ : ℝ → ℕ` with
`κ(α) → ∞` as `α → 0⁺`, in place of `α = 1/k`; this `κ` is not the prose's `κ = ‖K‖²`.

It holds for every `K`, `K = 0` included. -/
public theorem semiIterativeFilter_isRegularizingFilter [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] {K : E →L[𝕜] F} {q : ℕ → Polynomial ℝ}
    (hq : IsResidualPolynomialFamily q) {Cq : ℝ}
    (hbdd : ∀ k : ℕ, ∀ lam ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |(q k).eval lam| ≤ Cq)
    (hconv : ∀ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
      Tendsto (fun k : ℕ => (q k).eval lam) atTop (𝓝 0))
    {κ : ℝ → ℕ} (hκ : Tendsto κ (𝓝[>] (0 : ℝ)) atTop) :
    IsRegularizingFilter K (fun α lam => semiIterativeFilter q (κ (α : ℝ)) lam) (1 + Cq) := by
  have hκ0 : (0 : ℝ) ≤ ‖K‖ ^ 2 := by positivity
  have hCq : (1 : ℝ) ≤ Cq := by
    have h := hbdd 0 0 ⟨le_rfl, hκ0⟩
    rw [hq.eval_zero_eq_one 0] at h
    simpa using h
  obtain ⟨r, hval⟩ : ∃ r : ℕ → Polynomial ℝ, ∀ (k : ℕ) (t : ℝ),
      semiIterativeFilter q k t = (r k).eval t := by
    choose r hr using fun k => exists_eq_eval_of_isResidualPolynomialFamily hq k
    exact ⟨r, fun k => (hr k).1⟩
  refine ⟨by linarith, ?_, ?_, ?_⟩
  · -- each `φ_k` is a polynomial, hence bounded on `[0, ‖K‖²]`
    intro α
    obtain ⟨B, hB⟩ := exists_bound_on_Icc_of_continuous (‖K‖ ^ 2)
      (φ := fun t : ℝ => (r (κ (α : ℝ))).eval t) (Polynomial.continuous _)
    refine ⟨B, fun t ht => ?_⟩
    rw [hval]
    exact hB t ht
  · -- (1) `φ_{κ α}(λ) → λ⁻¹`, since `κ α → ∞` and `q_k(λ) → 0`
    intro lam hlam
    have hl : lam ≠ 0 := hlam.1.ne'
    have h1 : Tendsto (fun α : ℝ => (q (κ α)).eval lam) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      (hconv lam hlam).comp hκ
    have h2 : Tendsto (fun α : ℝ => (1 - (q (κ α)).eval lam) / lam)
        (𝓝[>] (0 : ℝ)) (𝓝 lam⁻¹) := by
      have h := (h1.const_sub 1).div_const lam
      simpa using h
    exact (h2.comp (map_coe_Ioi_atBot (0 : ℝ)).le).congr fun α =>
      (semiIterativeFilter_of_ne_zero hl q (κ (α : ℝ))).symm
  · -- (2) `λ |φ_k(λ)| = |1 - q_k(λ)| ≤ 1 + C_q`
    intro α lam hlam
    have hl : lam ≠ 0 := hlam.1.ne'
    rw [semiIterativeFilter_of_ne_zero hl, abs_div, abs_of_pos hlam.1,
      show lam * (|1 - (q (κ (α : ℝ))).eval lam| / lam) = |1 - (q (κ (α : ℝ))).eval lam| by
        field_simp]
    have hb := hbdd (κ (α : ℝ)) lam ⟨hlam.1.le, hlam.2⟩
    rw [abs_le] at hb ⊢
    exact ⟨by linarith [hb.2], by linarith [hb.1]⟩

/-- Under (1) and (2), the family `{R_α}` of the semi-iterative filter reindexed by `α` is a
regularization. The reindexing is `k = ⌊α⁻¹⌋`, in place of `α = 1/k`, so that the family is
defined for every `α > 0`.

It holds for every `K`, `K = 0` included. -/
public theorem isRegularization_semiIterativeFilter [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [CompleteSpace F] {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ}
    {v : ι → E} {u : ι → F} (hs : IsSingularSystem K σ v u)
    {q : ℕ → Polynomial ℝ} (hq : IsResidualPolynomialFamily q) {Cq : ℝ}
    (hbdd : ∀ k : ℕ, ∀ lam ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |(q k).eval lam| ≤ Cq)
    (hconv : ∀ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
      Tendsto (fun k : ℕ => (q k).eval lam) atTop (𝓝 0)) :
    IsRegularization K
      (spectralReg hs (fun α lam => semiIterativeFilter q ⌊(α : ℝ)⁻¹⌋₊ lam)
        ((semiIterativeFilter_isRegularizingFilter hq hbdd hconv
          (tendsto_nat_floor_atTop.comp tendsto_inv_nhdsGT_zero)).exists_bound_on_spectrum hs)) :=
  isRegularization_spectralReg hs
    (semiIterativeFilter_isRegularizingFilter hq hbdd hconv
      (tendsto_nat_floor_atTop.comp tendsto_inv_nhdsGT_zero))

end AutoIp

end _thm_semi_iterative_regularization
