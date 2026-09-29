/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_filter
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
public import AutoIp._part_2_reg._ch_19_general_source_conditions._def_general_source
public import AutoIp._part_2_reg._ch_22_balancing._def_balancing
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_qualification
import AutoIp.Auxiliary.Geometric
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_filter_norm_bound
import AutoIp._part_2_reg._ch_19_general_source_conditions._lem_general_omega
import AutoIp._part_2_reg._ch_22_balancing._lem_balancing_nonempty

section _lem_balancing_le_star

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- The error of each reconstruction splits into bias and data error: for an index function `φ`,
`x† ∈ X_{φ,ρ}` and every `α > 0`, `‖x^δ_α - x†‖ ≤ ω_φ(α) ρ + Δ(α)`, where
`ω_φ(α) = sup_{λ ∈ (0,κ]} φ(λ) |1 - λ φ_α(λ)|` and `Δ(α) = C_R δ α^(-1/2)` with `C_R = √(C_φ C_F)`.
At the grid points this is `‖xᵢ - x†‖ ≤ ωᵢ + Δᵢ`. -/
public theorem norm_spectralReg_sub_moorePenrose_le_bias_add (hs : IsSingularSystem K σ v u)
    {flt : Set.Ioi (0 : ℝ) → ℝ → ℝ} {Cflt CF : ℝ} (hflt : IsRegularizingFilter K flt Cflt)
    (hF : HasFilterBound K flt CF) {φ : ℝ → ℝ} {ρ : ℝ} (hφ : IsIndexFunction (‖K‖ ^ 2) φ)
    (hρ : 0 < ρ) {y : F} (hy : y ∈ mpDomain K)
    (hx : moorePenrose K ⟨y, hy⟩ ∈ sourceSetIndex hs φ (hφ.exists_bound_on_spectrum hs) ρ hρ)
    {δ : ℝ} {z : F} (hz : ‖y - z‖ ≤ δ) (α : Set.Ioi (0 : ℝ)) :
    ‖spectralReg hs flt (hflt.exists_bound_on_spectrum hs) α z - moorePenrose K ⟨y, hy⟩‖ ≤
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), φ lam * |1 - lam * flt α lam|) * ρ
        + Real.sqrt (Cflt * CF) * δ * (α : ℝ) ^ (-(1 : ℝ) / 2) := by
  have h1 := norm_spectralReg_sub_moorePenrose_le_iSup (α := α) hs hflt hφ hρ hy hx
  have h2 := norm_spectralReg_sub_le_mul_rpow (α := α) hs hflt hF hz
  have h3 := norm_sub_le_norm_sub_add_norm_sub
    (spectralReg hs flt (hflt.exists_bound_on_spectrum hs) α z)
    (spectralReg hs flt (hflt.exists_bound_on_spectrum hs) α y) (moorePenrose K ⟨y, hy⟩)
  linarith

/-- The balancing index does not overshoot: for an index function `φ`, `x† ∈ X_{φ,ρ}` and
`ωⱼ = ω_φ(αⱼ) ρ`, if `i_* ≤ N` is an index with `ωⱼ ≤ Δⱼ` for every `j ≥ i_*`, then
`i₊ ≤ i_*`. Here `Δⱼ = C_R δ αⱼ^(-1/2)` with `C_R = √(C_φ C_F)`. -/
public
theorem balancingIndex_le_of_bias_le (hs : IsSingularSystem K σ v u) {flt : Set.Ioi (0 : ℝ) → ℝ →
    ℝ} {Cflt CF : ℝ}
    (hflt : IsRegularizingFilter K flt Cflt)
    (hF : HasFilterBound K flt CF)
    {φ : ℝ → ℝ} {ρ : ℝ} (hφ : IsIndexFunction (‖K‖ ^ 2) φ) (hρ : 0 < ρ)
    {y : F} (hy : y ∈ mpDomain K)
    (hx : moorePenrose K ⟨y, hy⟩ ∈ sourceSetIndex hs φ (hφ.exists_bound_on_spectrum hs) ρ hρ)
    {δ : ℝ} (hδ : 0 ≤ δ) {z : F} (hz : ‖y - z‖ ≤ δ)
    {N : ℕ} {grid : ℕ → Set.Ioi (0 : ℝ)} {q : ℝ} (hq : 1 < q)
    (hgeom : ∀ i, i + 1 ≤ N → (grid i : ℝ) = q * (grid (i + 1) : ℝ))
    {istar : ℕ} (histar : istar ≤ N)
    (hstar : ∀ j, istar ≤ j → j ≤ N →
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), φ lam * |1 - lam * flt (grid j) lam|) * ρ ≤
        Real.sqrt (Cflt * CF) * δ * (grid j : ℝ) ^ (-(1 : ℝ) / 2)) :
    balancingIndex (spectralReg hs flt (hflt.exists_bound_on_spectrum hs)) (Real.sqrt (Cflt *
        CF)) δ (mul_nonneg (Real.sqrt_nonneg _) hδ) N grid z ≤ istar := by
  have hCR0 : (0 : ℝ) ≤ Real.sqrt (Cflt * CF) := Real.sqrt_nonneg _
  have hCF0 : (0 : ℝ) ≤ CF := hF.const_pos.le
  have hΔ : ∀ i j, i ≤ j → j ≤ N →
      (grid i : ℝ) ^ (-(1 : ℝ) / 2) ≤ (grid j : ℝ) ^ (-(1 : ℝ) / 2) :=
    fun i j hij hjN => rpow_neg_half_le_of_geometric hq hgeom hij hjN
  have herr : ∀ i, i ≤ N → ‖spectralReg hs flt (hflt.exists_bound_on_spectrum hs) (grid
      i) z - moorePenrose K ⟨y, hy⟩‖ ≤
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), φ lam * |1 - lam * flt (grid i) lam|) * ρ
        + Real.sqrt (Cflt * CF) * δ * (grid i : ℝ) ^ (-(1 : ℝ) / 2) :=
    fun i _ => norm_spectralReg_sub_moorePenrose_le_bias_add hs hflt hF hφ hρ hy hx hz (grid i)
  refine balancingIndex_le _ histar fun j hj hjN => ?_
  have h1 := herr istar histar
  have h2 := herr j hjN
  have h3 := hstar istar le_rfl histar
  have h4 := hstar j hj hjN
  have h5 : Real.sqrt (Cflt * CF) * δ * (grid istar : ℝ) ^ (-(1 : ℝ) / 2)
      ≤ Real.sqrt (Cflt * CF) * δ * (grid j : ℝ) ^ (-(1 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_left (hΔ istar j hj hjN) (mul_nonneg hCR0 hδ)
  have h6 := norm_sub_le_norm_sub_add_norm_sub (spectralReg hs flt (hflt.exists_bound_on_spectrum
      hs) (grid istar) z)
    (moorePenrose K ⟨y, hy⟩) (spectralReg hs flt (hflt.exists_bound_on_spectrum hs) (grid j) z)
  rw [norm_sub_rev (moorePenrose K ⟨y, hy⟩)] at h6
  linarith

end AutoIp

end _lem_balancing_le_star
