/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_filter
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
public import AutoIp._part_2_reg._ch_19_general_source_conditions._def_general_qualification
public import AutoIp._part_2_reg._ch_19_general_source_conditions._def_general_source
public import AutoIp._part_2_reg._ch_19_general_source_conditions._def_theta_function
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_qualification
import AutoIp._part_2_reg._ch_13_regularization._lem_error_decomposition
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_filter_norm_bound
import AutoIp._part_2_reg._ch_19_general_source_conditions._lem_general_omega
import Mathlib.Tactic.Positivity.Finset

section _thm_general_apriori_rate

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Rate for an a priori rule at a general index function: if the filter satisfies (F) with
constant `C_F` and (Q_φ) with constant `C^q_φ`, `y ∈ Dom(K†)` with `x† ∈ X_{φ,ρ}`, and
`α(δ) := Θ_φ⁻¹(δ/ρ)`, then `‖x^δ_{α(δ)} - x†‖ ≤ (√(C_φ C_F) + C^q_φ) ρ φ(α(δ))` for every
`y^δ` with `‖y - y^δ‖ ≤ δ`.

The rule is given as a parameter `α ∈ (0, κ]` with `Θ_φ(α) = δ/ρ`, which exists exactly when
`0 < δ/ρ ≤ Θ_φ(κ)`, in place of that hypothesis. -/
public theorem norm_spectralReg_sub_moorePenrose_le_apriori_index (hs : IsSingularSystem K σ v u)
    {flt : Set.Ioi (0 : ℝ) → ℝ → ℝ}
    {Cflt : ℝ} (hflt : IsRegularizingFilter K flt Cflt) {φ : ℝ → ℝ} {ρ CF Cq : ℝ}
    (hφ : IsIndexFunction (‖K‖ ^ 2) φ) (hρ : 0 < ρ)
    (hF : HasFilterBound K flt CF)
    (hQ : HasQualification K flt φ Cq)
    {y : F} (hy : y ∈ mpDomain K)
    (hx : moorePenrose K ⟨y, hy⟩ ∈ sourceSetIndex hs φ (hφ.exists_bound_on_spectrum hs) ρ hρ)
    {δ : ℝ} {z : F} (hz : ‖y - z‖ ≤ δ)
    {α : Set.Ioi (0 : ℝ)} (hαle : (α : ℝ) ≤ ‖K‖ ^ 2)
    (hαΘ : thetaIndex φ α = δ / ρ) :
    ‖spectralReg hs flt (hflt.exists_bound_on_spectrum hs) α z - moorePenrose K ⟨y, hy⟩‖ ≤
      (Real.sqrt (Cflt * CF) + Cq) * ρ * φ α :=
  by
  have hα : (0:ℝ) < (α : ℝ) := α.2
  have hδ0 : (0:ℝ) ≤ δ := (norm_nonneg _).trans hz
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have hk0 : (0:ℝ) ≤ ‖K‖ ^ 2 := by positivity
  have hsqα : (0:ℝ) < Real.sqrt (α : ℝ) := Real.sqrt_pos.mpr hα
  have hsq0 : Real.sqrt (α : ℝ) ≠ 0 := hsqα.ne'
  have hΘ : Real.sqrt (α : ℝ) * φ α = δ / ρ := by rw [← thetaIndex_apply]; exact hαΘ
  have hδeq : δ = ρ * (Real.sqrt (α : ℝ) * φ α) := by
    rw [hΘ]
    field_simp
  have hkeyδ : δ * Real.sqrt (α : ℝ)⁻¹ = ρ * φ α := by
    rw [Real.sqrt_inv, hδeq]
    field_simp
  have hΦ0 : (0 : ℝ) ≤ ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |flt α lam| :=
    Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _
  have hFα := hF.iSup_le α
  have hCF0 : (0 : ℝ) ≤ CF := by
    by_contra hcon
    push Not at hcon
    have hlt : CF * (α : ℝ)⁻¹ < 0 := mul_neg_of_neg_of_pos hcon (by positivity)
    linarith
  have hRnorm : ‖spectralReg hs flt (hflt.exists_bound_on_spectrum hs) α‖ ≤ Real.sqrt (Cflt *
      CF) * Real.sqrt (α : ℝ)⁻¹ :=
    opNorm_spectralReg_le_sqrt hs hflt hCF0 hFα
  have hdata : δ * ‖spectralReg hs flt (hflt.exists_bound_on_spectrum hs) α‖ ≤ Real.sqrt (Cflt *
      CF) * (ρ * φ α) := by
    calc δ * ‖spectralReg hs flt (hflt.exists_bound_on_spectrum hs) α‖
        ≤ δ * (Real.sqrt (Cflt * CF) * Real.sqrt (α : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left hRnorm hδ0
      _ = Real.sqrt (Cflt * CF) * (δ * Real.sqrt (α : ℝ)⁻¹) := by ring
      _ = Real.sqrt (Cflt * CF) * (ρ * φ α) := by rw [hkeyδ]
  have happrox : ‖spectralReg hs flt (hflt.exists_bound_on_spectrum hs) α y - moorePenrose K ⟨y,
      hy⟩‖ ≤ Cq * (ρ * φ α) := by
    refine (norm_spectralReg_sub_moorePenrose_le_iSup (α := α) hs hflt hφ hρ hy hx).trans ?_
    have hQα := hQ.omega_le α hαle
    calc (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), φ lam * |1 - lam * flt α lam|) * ρ
        ≤ (Cq * φ α) * ρ := mul_le_mul_of_nonneg_right hQα hρ.le
      _ = Cq * (ρ * φ α) := by ring
  have hsplit := norm_sub_moorePenrose_le (T := K) (spectralReg hs flt
      (hflt.exists_bound_on_spectrum hs)) (α := α) hy hz
  have hgoal : (Real.sqrt (Cflt * CF) + Cq) * ρ * φ α
      = Real.sqrt (Cflt * CF) * (ρ * φ α) + Cq * (ρ * φ α) := by ring
  rw [hgoal]
  linarith

end AutoIp

end _thm_general_apriori_rate
