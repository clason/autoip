/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_filter
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_spectral_residual_form

section _lem_filter_norm_bound

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Operator norm bound: for a regularizing filter and all `α > 0`,
`‖R_α‖ ≤ √C_φ (sup_{λ ∈ (0,κ]} |φ_α(λ)|)^{1/2}`.

It holds for every `K`, `K = 0` included. -/
public theorem opNorm_spectralReg_le (hs : IsSingularSystem K σ v u) {φ : Set.Ioi (0 : ℝ) → ℝ →
    ℝ} {C : ℝ}
    (hφ : IsRegularizingFilter K φ C) {α : Set.Ioi (0 : ℝ)} :
    ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α‖ ≤
      Real.sqrt C * Real.sqrt (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |φ α lam|) := by
  obtain ⟨B, hB⟩ := hφ.bddOn α
  set Φ := ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |φ α lam| with hΦdef
  have hΦ0 : 0 ≤ Φ :=
    Real.iSup_nonneg fun lam => Real.iSup_nonneg fun _ => abs_nonneg _
  have hbdd : BddAbove (Set.range (fun lam : ℝ =>
      ⨆ _ : lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |φ α lam|)) := by
    refine ⟨max B 0, ?_⟩
    rintro _ ⟨lam, rfl⟩
    exact Real.iSup_le (fun h => le_trans (hB lam ⟨h.1.le, h.2⟩) (le_max_left _ _))
      (le_max_right _ _)
  have hΦle : ∀ i, |φ α (σ i ^ 2)| ≤ Φ := by
    intro i
    have h1 := le_ciSup hbdd (σ i ^ 2)
    rwa [ciSup_pos (show σ i ^ 2 ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2) from
      ⟨pow_pos (hs.pos i) 2, (hs.sq_mem_Icc i).2⟩)] at h1
  have hCle : ∀ i, σ i ^ 2 * |φ α (σ i ^ 2)| ≤ C := fun i =>
    hφ.mul_abs_le α (σ i ^ 2) ⟨pow_pos (hs.pos i) 2, (hs.sq_mem_Icc i).2⟩
  have hC0 : (0 : ℝ) ≤ C := hφ.const_pos.le
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  obtain ⟨-, hRn⟩ := hasSum_spectralReg_and_norm_sq (α := α) hs (hφ.exists_bound_on_spectrum
      hs) y
  set c : ι → 𝕜 := fun i => (inner 𝕜 (u i) y : 𝕜) with hcdef
  have hsum1 : Summable (fun i => ‖c i‖ ^ 2) :=
    hs.orthonormal_right.inner_products_summable (x := y)
  have hterm : ∀ i, |φ α (σ i ^ 2)| ^ 2 * σ i ^ 2 * ‖c i‖ ^ 2 ≤ Φ * C * ‖c i‖ ^ 2 := by
    intro i
    have h1 : |φ α (σ i ^ 2)| ^ 2 * σ i ^ 2 ≤ Φ * C := by
      have e : |φ α (σ i ^ 2)| ^ 2 * σ i ^ 2
          = |φ α (σ i ^ 2)| * (σ i ^ 2 * |φ α (σ i ^ 2)|) := by ring
      rw [e]
      exact mul_le_mul (hΦle i) (hCle i)
        (mul_nonneg (sq_nonneg _) (abs_nonneg _)) hΦ0
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  have hsum2 : Summable (fun i => |φ α (σ i ^ 2)| ^ 2 * σ i ^ 2 * ‖c i‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun i => by positivity) hterm (hsum1.mul_left (Φ * C))
  have hle : ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y‖ ^ 2 ≤ Φ * C * ‖y‖ ^ 2 := by
    rw [← hRn.tsum_eq]
    calc ∑' i, |φ α (σ i ^ 2)| ^ 2 * σ i ^ 2 * ‖c i‖ ^ 2
        ≤ ∑' i, Φ * C * ‖c i‖ ^ 2 :=
          Summable.tsum_le_tsum hterm hsum2 (hsum1.mul_left (Φ * C))
      _ = Φ * C * ∑' i, ‖c i‖ ^ 2 := hsum1.tsum_mul_left _
      _ ≤ Φ * C * ‖y‖ ^ 2 := by
          exact mul_le_mul_of_nonneg_left
            (hs.orthonormal_right.tsum_inner_products_le y) (by positivity)
  have hrhs : (Real.sqrt C * Real.sqrt Φ * ‖y‖) ^ 2 = Φ * C * ‖y‖ ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hC0, Real.sq_sqrt hΦ0]
    ring
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) (hle.trans_eq hrhs.symm)

end AutoIp

end _lem_filter_norm_bound
