/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_qualification.Spec
import all AutoIp._part_2_reg._ch_15_spectral_regularization._def_qualification.Spec
public import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_filter_norm_bound

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- `ν₀ ≤ C` if and only if `ν ≤ C` for every `ν > 0` for which (Q_ν) holds. -/
public theorem qualification_le_iff (K : E →L[𝕜] F) (φ : Set.Ioi (0 : ℝ) → ℝ → ℝ) (C : ℝ≥0∞) :
    qualification K φ ≤ C ↔
      ∀ ν ∈ {ν : ℝ | 0 < ν ∧ ∃ Cν, HasResidualBound K φ ν Cν},
        ENNReal.ofReal ν ≤ C := by
  unfold qualification
  exact iSup₂_le_iff

/-- If (Q_ν) holds for some `ν > 0`, then `ν ≤ ν₀`. -/
public theorem le_qualification (K : E →L[𝕜] F) (φ : Set.Ioi (0 : ℝ) → ℝ → ℝ) {ν : ℝ}
    (hν : 0 < ν)
    (h : ∃ Cν, HasResidualBound K φ ν Cν) :
    ENNReal.ofReal ν ≤ qualification K φ := by
  unfold qualification
  have hmem : ν ∈ {ν : ℝ | 0 < ν ∧ ∃ Cν, HasResidualBound K φ ν Cν} := ⟨hν, h⟩
  exact le_iSup_of_le ν (le_iSup_of_le hmem le_rfl)

/-- The constant of condition (F) is nonnegative. -/
public theorem HasFilterBound.const_nonneg {K : E →L[𝕜] F} {φ : Set.Ioi (0 : ℝ) → ℝ → ℝ} {CF : ℝ}
    (hF : HasFilterBound K φ CF) : 0 ≤ CF :=
  hF.const_pos.le

/-- If `sup_{λ ∈ (0,κ]} |φ_α(λ)| ≤ C_F α⁻¹`, then `‖R_α‖ ≤ √(C_φ C_F) √(α⁻¹)`. -/
public theorem opNorm_spectralReg_le_sqrt [CompleteSpace E] [CompleteSpace F]
    {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F} (hs : IsSingularSystem K σ v u)
    {φ : Set.Ioi (0 : ℝ) → ℝ → ℝ} {Cφ CF : ℝ} (hφ : IsRegularizingFilter K φ Cφ) (hCF : 0 ≤ CF)
    {α : Set.Ioi (0 : ℝ)}
    (hFα : (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |φ α lam|) ≤ CF * (α : ℝ)⁻¹) :
    ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α‖ ≤ Real.sqrt (Cφ * CF) * Real.sqrt (α :
        ℝ)⁻¹ := by
  refine (opNorm_spectralReg_le (α := α) hs hφ).trans ?_
  have h1 : Real.sqrt (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |φ α lam|)
      ≤ Real.sqrt (CF * (α : ℝ)⁻¹) := Real.sqrt_le_sqrt hFα
  refine (mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg Cφ)).trans_eq ?_
  rw [Real.sqrt_mul hCF, Real.sqrt_mul hφ.const_pos.le]
  ring

/-- If `sup_{λ ∈ (0,κ]} |φ_α(λ)| ≤ C_F α⁻¹`, then `‖R_α‖ ≤ √(C_φ C_F) α^{-1/2}`. -/
public theorem opNorm_spectralReg_le_rpow [CompleteSpace E] [CompleteSpace F]
    {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F} (hs : IsSingularSystem K σ v u)
    {φ : Set.Ioi (0 : ℝ) → ℝ → ℝ} {Cφ CF : ℝ} (hφ : IsRegularizingFilter K φ Cφ) (hCF : 0 ≤ CF)
    {α : Set.Ioi (0 : ℝ)}
    (hFα : (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |φ α lam|) ≤ CF * (α : ℝ)⁻¹) :
    ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α‖ ≤ Real.sqrt (Cφ * CF) * (α : ℝ) ^ (-(1
        : ℝ) / 2) := by
  refine (opNorm_spectralReg_le_sqrt hs hφ hCF hFα).trans_eq ?_
  congr 1
  rw [neg_div, Real.rpow_neg α.2.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_inv]

/-- Under condition (F), `‖R_α z - R_α y‖ ≤ √(C_φ C_F) δ α^{-1/2}` for `‖y - z‖ ≤ δ`. -/
public theorem norm_spectralReg_sub_le_mul_rpow [CompleteSpace E] [CompleteSpace F]
    {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F} (hs : IsSingularSystem K σ v u)
    {flt : Set.Ioi (0 : ℝ) → ℝ → ℝ} {Cflt CF : ℝ} (hflt : IsRegularizingFilter K flt Cflt)
    (hF : HasFilterBound K flt CF)
    {y z : F} {δ : ℝ} (hz : ‖y - z‖ ≤ δ) {α : Set.Ioi (0 : ℝ)} :
    ‖spectralReg hs flt (hflt.exists_bound_on_spectrum
        hs) α z - spectralReg hs flt (hflt.exists_bound_on_spectrum hs) α y‖
      ≤ Real.sqrt (Cflt * CF) * δ * (α : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hCF0 : (0 : ℝ) ≤ CF := hF.const_pos.le
  have h1 : spectralReg hs flt (hflt.exists_bound_on_spectrum
      hs) α z - spectralReg hs flt (hflt.exists_bound_on_spectrum hs) α y
      = spectralReg hs flt (hflt.exists_bound_on_spectrum hs) α (z - y) := (map_sub _ _ _).symm
  have h3 : ‖z - y‖ ≤ δ := by rw [norm_sub_rev]; exact hz
  have h4 : (0 : ℝ) ≤ Real.sqrt (Cflt * CF) * (α : ℝ) ^ (-(1 : ℝ) / 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg α.2.le _)
  rw [h1]
  calc ‖spectralReg hs flt (hflt.exists_bound_on_spectrum hs) α (z - y)‖
      ≤ ‖spectralReg hs flt (hflt.exists_bound_on_spectrum
          hs) α‖ * ‖z - y‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ Real.sqrt (Cflt * CF) * (α : ℝ) ^ (-(1 : ℝ) / 2) * δ :=
        mul_le_mul (opNorm_spectralReg_le_rpow hs hflt hCF0 (hF.iSup_le α)) h3
          (norm_nonneg _) h4
    _ = Real.sqrt (Cflt * CF) * δ * (α : ℝ) ^ (-(1 : ℝ) / 2) := by ring

end AutoIp
