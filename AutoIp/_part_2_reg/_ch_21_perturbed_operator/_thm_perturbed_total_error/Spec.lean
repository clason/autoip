/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_12_picard._def_source_set
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_standard_filters
public import AutoIp._part_2_reg._ch_21_perturbed_operator._def_perturbed_problem
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_omega_nu
import AutoIp._part_2_reg._ch_16_tikhonov._lem_tikhonov_normal
import AutoIp._part_2_reg._ch_16_tikhonov._lem_tikhonov_qualification
import AutoIp._part_2_reg._ch_21_perturbed_operator._lem_perturbed_decomposition
import AutoIp._part_2_reg._ch_21_perturbed_operator._lem_tikhonov_operator_perturbation
public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
import AutoIp.Auxiliary.Rpow

section _thm_perturbed_total_error

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K Kh : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F} {ι' : Type*}
variable {σ' : ι' → ℝ} {v' : ι' → E} {u' : ι' → F}

/-- Total error for perturbed Tikhonov: for `(h,δ)`-admissible data `(K_h, y^δ)`,
`x† = K† y ∈ X_{ν,ρ}` with `0 < ν ≤ 2`, and every `α ∈ (0,1]`,
`‖x^{h,δ}_α - x†‖ ≤ C₁ h (‖y‖ + δ) / α^(3/2) + δ / (2√α) + ρ α^(ν/2)`, where
`C₁ = 1 + (2‖K‖ + h)/2` and `x^{h,δ}_α` is the Tikhonov reconstruction from `K_h` and `y^δ`.

The Lean assumes `y ∈ Dom(K†)` rather than `y ∈ Ran(K)`. -/
public theorem norm_spectralReg_sub_moorePenrose_le_perturbed (hs : IsSingularSystem K σ v u)
    (hsh : IsSingularSystem Kh σ' v' u') {y z : F} {h δ ν ρ : ℝ} {α : Set.Ioi (0 : ℝ)}
    (hd : IsAdmissibleData K Kh y z h δ) (hy : y ∈ mpDomain K)
    (hν : 0 < ν) (hν2 : ν ≤ 2) (hρ : 0 < ρ)
    (hx : moorePenrose K ⟨y, hy⟩ ∈ sourceSet hs ν hν ρ hρ) (hα1 : (α : ℝ) ≤ 1) :
    ‖spectralReg hsh tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum
        hsh) α z - moorePenrose K ⟨y, hy⟩‖ ≤
      (1 + (2 * ‖K‖ + h) / 2) * (h * (‖y‖ + δ)) / (α : ℝ) ^ ((3 : ℝ) / 2)
        + δ / (2 * Real.sqrt (α : ℝ))
        + ρ * (α : ℝ) ^ (ν / 2) := by
  have hα : (0 : ℝ) < (α : ℝ) := α.2
  have hh0 : (0 : ℝ) ≤ h := le_trans (norm_nonneg _) hd.opNorm_sub_le
  have hδ0 : (0 : ℝ) ≤ δ := le_trans (norm_nonneg _) hd.norm_sub_le
  have hsq0 : 0 < Real.sqrt (α : ℝ) := Real.sqrt_pos.mpr hα
  have hsqsq : Real.sqrt (α : ℝ) * Real.sqrt (α : ℝ) = (α : ℝ) := Real.mul_self_sqrt hα.le
  have hsq1 : Real.sqrt (α : ℝ) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hα1
  have hα32 := rpow_three_halves hα
  have h32pos : (0 : ℝ) < (α : ℝ) ^ ((3 : ℝ) / 2) := by rw [hα32]; positivity
  have h3 := norm_sub_moorePenrose_le_perturbed hs hsh tikhonovFilter
    (tikhonovFilter_exists_bound_on_spectrum hs) (tikhonovFilter_exists_bound_on_spectrum hsh)
    α hy hd.norm_sub_le
  have hz : ‖z‖ ≤ ‖y‖ + δ := by
    have h1 : ‖z‖ ≤ ‖y‖ + ‖y - z‖ := by
      calc ‖z‖ = ‖y - (y - z)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖y‖ + ‖y - z‖ := norm_sub_le _ _
    linarith [hd.norm_sub_le]
  have hyδ : (0 : ℝ) ≤ ‖y‖ + δ := by positivity
  have hop : ‖(spectralReg hsh tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hsh) α -
      spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) α) z‖
      ≤ (1 + (2 * ‖K‖ + h) / 2) * (h * (‖y‖ + δ)) / (α : ℝ) ^ ((3 : ℝ) / 2) := by
    have h1 : ‖(spectralReg hsh tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hsh) α -
        spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) α) z‖
        ≤ (h / (α : ℝ) + h * (2 * ‖K‖ + h) / (2 * (α : ℝ) ^ ((3 : ℝ) / 2))) * (‖y‖ + δ) := by
      calc ‖(spectralReg hsh tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hsh) α -
          spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) α) z‖
          ≤ ‖spectralReg hsh tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum
              hsh) α - spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) α‖
                * ‖z‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (h / (α : ℝ) + h * (2 * ‖K‖ + h) / (2 * (α : ℝ) ^ ((3 : ℝ) / 2))) * (‖y‖ + δ) :=
            mul_le_mul (opNorm_tikhonov_perturbed_sub_le hs hsh hd.opNorm_sub_le) hz
              (norm_nonneg _) (by positivity)
    refine h1.trans ?_
    -- For `α ≤ 1` the `α⁻¹` of the first summand is dominated by `α^{-3/2}`.
    have h2 : h / (α : ℝ) ≤ h / (α : ℝ) ^ ((3 : ℝ) / 2) := by
      rw [hα32, div_le_div_iff₀ hα (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg hh0 hα.le) (sub_nonneg.mpr hsq1)]
    have hexpand : (1 + (2 * ‖K‖ + h) / 2) * (h * (‖y‖ + δ)) / (α : ℝ) ^ ((3 : ℝ) / 2)
        = (h / (α : ℝ) ^ ((3 : ℝ) / 2)
            + h * (2 * ‖K‖ + h) / (2 * (α : ℝ) ^ ((3 : ℝ) / 2))) * (‖y‖ + δ) := by
      field_simp
    rw [hexpand]
    exact mul_le_mul_of_nonneg_right (by linarith) hyδ
  have hRnorm := opNorm_spectralReg_tikhonov_le (α := α) hs
  have hdata : δ * ‖spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum
      hs) α‖ ≤ δ / (2 * Real.sqrt (α : ℝ)) := by
    calc δ * ‖spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum
        hs) α‖ ≤ δ * (1 / (2 * Real.sqrt (α : ℝ))) :=
        mul_le_mul_of_nonneg_left hRnorm hδ0
      _ = δ / (2 * Real.sqrt (α : ℝ)) := by ring
  have hQ : (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
      lam ^ (ν / 2) * |1 - lam * tikhonovFilter α lam|) ≤ (α : ℝ) ^ (ν / 2) := by
    simpa using iSup_rpow_mul_abs_one_sub_mul_tikhonovFilter_le K hν hν2 α
  have happrox : ‖spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum
      hs) α y - moorePenrose K ⟨y, hy⟩‖ ≤ ρ * (α : ℝ) ^ (ν / 2) := by
    refine (norm_spectralReg_sub_moorePenrose_le (α := α) hs
      (tikhonovFilter_isRegularizingFilter K) hν hρ hy hx).1.trans ?_
    calc (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
          lam ^ (ν / 2) * |1 - lam * tikhonovFilter α lam|) * ρ
        ≤ (α : ℝ) ^ (ν / 2) * ρ := mul_le_mul_of_nonneg_right hQ hρ.le
      _ = ρ * (α : ℝ) ^ (ν / 2) := by ring
  linarith

end AutoIp

end _thm_perturbed_total_error
