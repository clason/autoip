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

section _lem_residual_constant

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable {K : E →L[𝕜] F}

/-- The residual constant: for a regularizing filter and
`C_r := sup_{α > 0, λ ∈ (0,κ]} |r_α(λ)|` with `r_α(λ) = 1 − λ φ_α(λ)`,
`1 ≤ C_r ≤ 1 + C_φ` and `‖y − K R_α y‖ ≤ C_r ‖y‖` for all `y ∈ Y` and all `α > 0`. -/
public
theorem one_le_iSup_abs_one_sub_mul_and_norm_residual_le [CompleteSpace E] [CompleteSpace F]
    {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F} (hs : IsSingularSystem K σ v u) (hK : K ≠ 0)
    {φ : Set.Ioi (0 : ℝ) → ℝ → ℝ} {C : ℝ} (hφ : IsRegularizingFilter K φ C) :
    1 ≤ (⨆ a : Set.Ioi (0 : ℝ), ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |1 - lam * φ a lam|) ∧
      (⨆ a : Set.Ioi (0 : ℝ), ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |1 - lam * φ a lam|) ≤
        1 + C ∧
      ∀ (y : F), ∀ α : Set.Ioi (0 : ℝ), ‖y - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs)
          α y)‖ ≤
        (⨆ a : Set.Ioi (0 : ℝ), ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |1 - lam * φ a lam|) *
          ‖y‖ := by
  have hKn : ‖K‖ ≠ 0 := norm_ne_zero_iff.mpr hK
  have hκ : (0 : ℝ) < ‖K‖ ^ 2 := by positivity
  have hC0 : (0 : ℝ) < C := hφ.const_pos
  have h1C : (0 : ℝ) ≤ 1 + C := by linarith
  have hbound : ∀ (a : Set.Ioi (0 : ℝ)), ∀ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
      |1 - lam * φ a lam| ≤ 1 + C := by
    intro a lam hlam
    have h := hφ.mul_abs_le a lam hlam
    have habs : |lam * φ a lam| ≤ C := by
      rw [abs_mul, abs_of_pos hlam.1]; exact h
    rw [abs_le] at habs ⊢
    constructor <;> linarith [habs.1, habs.2]
  set Cr := ⨆ a : Set.Ioi (0 : ℝ), ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |1 - lam * φ a lam|
    with hCrdef
  have hupper : Cr ≤ 1 + C :=
    Real.iSup_le (fun a =>
      Real.iSup_le (fun lam => Real.iSup_le (fun hlam => hbound a lam hlam) h1C) h1C) h1C
  have hCr0 : 0 ≤ Cr :=
    Real.iSup_nonneg fun _ =>
      Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _
  have hbddInner : ∀ a : Set.Ioi (0 : ℝ), BddAbove (Set.range (fun lam : ℝ =>
      ⨆ _ : lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |1 - lam * φ a lam|)) := by
    intro a
    refine ⟨1 + C, ?_⟩
    rintro _ ⟨lam, rfl⟩
    exact Real.iSup_le (fun hlam => hbound a lam hlam) h1C
  have hbddOuter : BddAbove (Set.range (fun a : Set.Ioi (0 : ℝ) =>
      ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |1 - lam * φ a lam|)) := by
    refine ⟨1 + C, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact Real.iSup_le (fun lam => Real.iSup_le (fun hlam => hbound a lam hlam) h1C) h1C
  have hdom : ∀ (a : Set.Ioi (0 : ℝ)), ∀ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
      |1 - lam * φ a lam| ≤ Cr := by
    intro a lam hlam
    have h1 := le_ciSup hbddOuter a
    have h2 := le_ciSup (hbddInner a) lam
    rw [ciSup_pos hlam] at h2
    linarith
  have hlow : 1 ≤ Cr := by
    by_contra hcon
    push Not at hcon
    set ε := (1 - Cr) / 2 with hεdef
    have hε0 : 0 < ε := by rw [hεdef]; linarith
    have hone : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.2 one_pos
    obtain ⟨B, hB⟩ := hφ.bddOn ⟨1, hone⟩
    have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 ⟨le_rfl, by positivity⟩)
    set lam := min (‖K‖ ^ 2) (ε / (B + 1)) with hlamdef
    have hlam0 : 0 < lam := lt_min hκ (by positivity)
    have hlamIoc : lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2) := ⟨hlam0, min_le_left _ _⟩
    have habs : |φ ⟨1, hone⟩ lam| ≤ B := hB lam ⟨hlam0.le, min_le_left _ _⟩
    have hprod : lam * |φ ⟨1, hone⟩ lam| ≤ ε := by
      have h1 : lam ≤ ε / (B + 1) := min_le_right _ _
      calc lam * |φ ⟨1, hone⟩ lam| ≤ (ε / (B + 1)) * B :=
            mul_le_mul h1 habs (abs_nonneg _) (by positivity)
        _ ≤ ε := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < B + 1)]
            nlinarith
    have hge : 1 - ε ≤ |1 - lam * φ ⟨1, hone⟩ lam| := by
      have h1 : lam * φ ⟨1, hone⟩ lam ≤ lam * |φ ⟨1, hone⟩ lam| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hlam0.le
      have h2 := le_abs_self (1 - lam * φ ⟨1, hone⟩ lam)
      linarith
    have h3 := hdom ⟨1, hone⟩ lam hlamIoc
    rw [hεdef] at hge
    linarith
  refine ⟨hlow, hupper, ?_⟩
  intro y α
  obtain ⟨-, hr, hresn⟩ := hasSum_starProjection_sub_apply_spectralReg_and_norm_sq (α := α) hs
    (hφ.exists_bound_on_spectrum hs) y
  obtain ⟨hc, hyn⟩ := hasSum_norm_sq_inner_starProjection_range hs y
  have hsum1 : Summable (fun i => ‖(inner 𝕜 (u i) y : 𝕜)‖ ^ 2) :=
    hs.orthonormal_right.inner_products_summable (x := y)
  have hti : ∀ i, |1 - σ i ^ 2 * φ α (σ i ^ 2)| ^ 2 * ‖(inner 𝕜 (u i) y : 𝕜)‖ ^ 2
      ≤ Cr ^ 2 * ‖(inner 𝕜 (u i) y : 𝕜)‖ ^ 2 := by
    intro i
    have h := hdom α (σ i ^ 2) ⟨pow_pos (hs.pos i) 2, (hs.sq_mem_Icc i).2⟩
    have h0 := abs_nonneg (1 - σ i ^ 2 * φ α (σ i ^ 2))
    have hsq : |1 - σ i ^ 2 * φ α (σ i ^ 2)| ^ 2 ≤ Cr ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hsum2 : Summable (fun i => |1 - σ i ^ 2 * φ α (σ i ^ 2)| ^ 2 *
      ‖(inner 𝕜 (u i) y : 𝕜)‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun i => by positivity) hti (hsum1.mul_left (Cr ^ 2))
  have hts := Summable.tsum_le_tsum hti hsum2 (hsum1.mul_left (Cr ^ 2))
  rw [hsum1.tsum_mul_left] at hts
  have hCr2 : 1 ≤ Cr ^ 2 := by nlinarith
  have hfinal : ‖y - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y)‖ ^ 2 ≤ (Cr *
      ‖y‖) ^ 2 := by
    rw [hresn, ← hr.tsum_eq, mul_pow, hyn, ← hc.tsum_eq]
    have hA : (0:ℝ)
        ≤ ‖y - K.toLinearMap.range.topologicalClosure.starProjection y‖ ^ 2 :=
      sq_nonneg _
    nlinarith [hts, hA, mul_nonneg (by linarith : (0:ℝ) ≤ Cr ^ 2 - 1) hA]
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hfinal

/-- The residual constant: `C_r ≤ 1 + C_φ`. This needs neither a singular system nor
`K ≠ 0`. -/
public theorem iSup_abs_one_sub_mul_le_one_add {φ : Set.Ioi (0 : ℝ) → ℝ → ℝ} {Cφ : ℝ}
    (hφ : IsRegularizingFilter K φ Cφ) :
    (⨆ b : Set.Ioi (0 : ℝ), ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |1 - lam * φ b lam|)
      ≤ 1 + Cφ := by
  have h0 : (0 : ℝ) ≤ 1 + Cφ := by linarith [hφ.const_pos]
  exact Real.iSup_le (fun b =>
    Real.iSup_le (fun lam => Real.iSup_le
      (fun hlam => abs_one_sub_mul_le_one_add hφ ⟨hlam.1.le, hlam.2⟩) h0) h0) h0

end AutoIp

end _lem_residual_constant
