/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_13_regularization._def_regularization
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_filter
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound
import AutoIp._part_2_reg._ch_13_regularization._thm_reg_diverges_outside_domain
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_approx_error_spectral
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_filter_residual_bound
import Mathlib.Analysis.Normed.Group.Tannery

section _thm_spectral_is_regularization

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Spectral regularizations are regularizations: for a regularizing filter, `R_α y → K†y`
for every `y ∈ Dom(K†)`, i.e. `{R_α}_{α>0}` is a regularization of `K†`.

It holds for every `K`, `K = 0` included. -/
public theorem isRegularization_spectralReg (hs : IsSingularSystem K σ v u) {φ : Set.Ioi (0 : ℝ)
    → ℝ → ℝ}
    {C : ℝ} (hφ : IsRegularizingFilter K φ C) :
    IsRegularization K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs)) := by
  have hreg : IsRegularization K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs)) := by
    intro y hy
    set x := moorePenrose K ⟨y, hy⟩ with hxdef
    set c : ι → 𝕜 := fun i => (inner 𝕜 (v i) x : 𝕜) with hcdef
    have hsummable : Summable (fun i => ‖c i‖ ^ 2) :=
      hs.orthonormal_left.inner_products_summable (x := x)
    obtain ⟨hlim, hbnd⟩ := hφ.tendsto_one_sub_mul_and_abs_le
    have hmem : ∀ i, σ i ^ 2 ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2) :=
      fun i => ⟨pow_pos (hs.pos i) 2, (hs.sq_mem_Icc i).2⟩
    have hser : ∀ α : Set.Ioi (0 : ℝ), ‖x - spectralReg hs φ (hφ.exists_bound_on_spectrum
        hs) α y‖ ^ 2
        = ∑' i, |1 - σ i ^ 2 * φ α (σ i ^ 2)| ^ 2 * ‖c i‖ ^ 2 := by
      intro α
      obtain ⟨-, hsum⟩ := moorePenrose_sub_spectralReg_eq_funCalc (α := α) hs hφ hy
      rw [hs.orthonormal_left.norm_sq_eq_tsum_norm_sq hsum]
      refine tsum_congr fun i => ?_
      rw [norm_mul, RCLike.norm_ofReal, mul_pow]
    have htan : Tendsto (fun α => ∑' i, |1 - σ i ^ 2 * φ α (σ i ^ 2)| ^ 2 * ‖c i‖ ^ 2)
        atBot (𝓝 0) := by
      have h := tendsto_tsum_of_dominated_convergence
        (𝓕 := (atBot : Filter (Set.Ioi (0 : ℝ))))
        (f := fun (α : Set.Ioi (0 : ℝ)) (i : ι) =>
          |1 - σ i ^ 2 * φ α (σ i ^ 2)| ^ 2 * ‖c i‖ ^ 2)
        (g := fun _ : ι => (0 : ℝ))
        (bound := fun i => (1 + C) ^ 2 * ‖c i‖ ^ 2)
        (hsummable.mul_left _)
        (fun i => by
          have h1 := hlim (σ i ^ 2) (hmem i)
          have h2 : Tendsto (fun a => |1 - σ i ^ 2 * φ a (σ i ^ 2)| ^ 2)
              atBot (𝓝 0) := by simpa using h1.abs.pow 2
          simpa using h2.mul_const (‖c i‖ ^ 2))
        (by
          filter_upwards with α i
          have h := hbnd α (σ i ^ 2) (hmem i)
          rw [Real.norm_of_nonneg (by positivity)]
          have h0 := abs_nonneg (1 - σ i ^ 2 * φ α (σ i ^ 2))
          have hsq : |1 - σ i ^ 2 * φ α (σ i ^ 2)| ^ 2 ≤ (1 + C) ^ 2 := by nlinarith
          exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _))
      simpa using h
    have hsq2 : Tendsto
        (fun α : Set.Ioi (0 : ℝ) =>
          ‖x - spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y‖ ^ 2)
        atBot (𝓝 0) :=
      htan.congr fun α => (hser α).symm
    have hn : Tendsto (fun α : Set.Ioi (0 : ℝ) => ‖spectralReg hs φ (hφ.exists_bound_on_spectrum
        hs) α y - x‖) atBot (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq2
      rw [Real.sqrt_zero] at h
      refine h.congr fun α => ?_
      simp only [Function.comp_apply]
      rw [Real.sqrt_sq (norm_nonneg _), norm_sub_rev]
    exact tendsto_iff_norm_sub_tendsto_zero.mpr hn
  exact hreg

/-- For a regularizing filter with `K†` unbounded, `‖R_α y‖ → ∞` as `α → 0` for every
`y ∉ Dom(K†)`.

It holds for every `K`, `K = 0` included. -/
public theorem tendsto_norm_spectralReg_atTop (hs : IsSingularSystem K σ v u)
    {φ : Set.Ioi (0 : ℝ) → ℝ → ℝ} {C : ℝ} (hφ : IsRegularizingFilter K φ C) :
    (¬ ∃ B : ℝ, ∀ y : (moorePenrose K).domain, ‖moorePenrose K y‖ ≤ B * ‖(y : F)‖) →
      ∀ y ∉ mpDomain K,
        Tendsto (fun α : Set.Ioi (0 : ℝ) => ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α
            y‖) atBot atTop := by
  have hC0 : (0 : ℝ) < C := hφ.const_pos
  have hbdd : ∃ B : ℝ, ∀ α : Set.Ioi (0 : ℝ), ‖K ∘L spectralReg hs φ (hφ.exists_bound_on_spectrum
      hs) α‖ ≤ B := by
    refine ⟨C, fun α => ?_⟩
    obtain ⟨h1, h2⟩ := opNorm_comp_spectralReg_le (α := α) hs hφ
    linarith
  exact fun _ y hy =>
    tendsto_norm_atTop_of_notMem_mpDomain (isRegularization_spectralReg hs hφ) hbdd hy

end AutoIp

end _thm_spectral_is_regularization
