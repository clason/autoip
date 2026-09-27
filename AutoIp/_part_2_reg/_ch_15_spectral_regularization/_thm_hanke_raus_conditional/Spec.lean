/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_12_picard._def_source_set
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_filter
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_hanke_raus
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_abs_norm
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._thm_interpolation
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_equations
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_approx_error_spectral
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_filter_norm_bound
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_omega_nu
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_residual_constant
import AutoIp._part_2_reg._ch_15_spectral_regularization._thm_hanke_raus_conditional.Helpers
public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_qualification

section _thm_hanke_raus_conditional

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Conditional error estimate for Hanke–Raus: for a regularizing filter satisfying (F) and
(Q_{ν+1}), with `ν > 0`, there is `c > 0` such that for every `ρ > 0`, every `δ > 0`, every
`y ∈ Ran(K)` with `‖y‖ > δ` and `x† := K†y ∈ X_{ν,ρ}`, every `y^δ ∈ B_δ(y)`, and every
minimiser `α* ∈ (0, κ]` of `Ψ` with `δ* := ‖K x^δ_{α*} − y^δ‖ > 0`,
`‖x^δ_{α*} − x†‖ ≤ c (1 + δ/δ*) max{δ, δ*}^{ν/(ν+1)} ρ^{1/(ν+1)}`. Of the prose's hypotheses
on the filter only (F) and (Q_{ν+1}) are assumed, which is what `ν ∈ (0, ν₀ − 1]` provides.
(Q_{ν+1}) is asked for every `α > 0` rather than on `(0, κ]`, which for a regularizing filter
changes only the constant. -/
public
theorem norm_spectralReg_sub_moorePenrose_le_hankeRaus (hs : IsSingularSystem K σ v u)
    {φ : Set.Ioi (0 : ℝ) → ℝ → ℝ} {Cφ : ℝ}
    (hφ : IsRegularizingFilter K φ Cφ) {ν : ℝ}
    (hF : ∃ CF > (0 : ℝ), HasFilterBound K φ CF)
    (hQ : ∃ Cν > (0 : ℝ), ∀ α : Set.Ioi (0 : ℝ),
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
        lam ^ ((ν + 1) / 2) * |1 - lam * φ α lam|) ≤ Cν * (α : ℝ) ^ ((ν + 1) / 2))
    (hν : 0 < ν) :
    ∃ c > (0 : ℝ), ∀ (ρ : ℝ) (hρ : 0 < ρ), ∀ δ > (0 : ℝ),
      ∀ y, ∀ hy : y ∈ K.toLinearMap.range, δ < ‖y‖ →
        moorePenrose K ⟨y, (Submodule.mem_sup_left hy)⟩ ∈ sourceSet hs ν hν ρ hρ →
        ∀ z : F, ‖y - z‖ ≤ δ → ∀ α, IsHankeRausChoiceOnSpectrum hs φ (hφ.exists_bound_on_spectrum
            hs) z α →
          0 < ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z) - z‖ →
            ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z - moorePenrose K ⟨y,
                (Submodule.mem_sup_left hy)⟩‖ ≤
              c * (1 + δ / ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z) - z‖) *
                (max δ ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z) - z‖) ^ (ν / (ν
                    + 1)) *
                ρ ^ (1 / (ν + 1)) := by
  have hν0 : (0 : ℝ) < ν := hν
  have hν1 : (0 : ℝ) < ν + 1 := by linarith
  have hCφ0 : (0 : ℝ) < Cφ := hφ.const_pos
  obtain ⟨CF, hCF0, hCF⟩ := hF
  obtain ⟨Cν1, hCν10, hCν1⟩ := hQ
  set B := 1 + Cφ with hBdef
  have hB1 : (1 : ℝ) ≤ B := by rw [hBdef]; linarith [hφ.const_pos]
  have hBub : ∀ (b : Set.Ioi (0 : ℝ)), ∀ s ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2),
      |1 - s * φ b s| ≤ B :=
    fun _ _ hsm => abs_one_sub_mul_le_one_add hφ hsm
  have hB0 : (0 : ℝ) ≤ B := by linarith
  set S := Real.sqrt (Cφ * CF) with hSdef
  have hS0 : 0 < S := Real.sqrt_pos.mpr (by positivity)
  set c1 := (1 + B) ^ (ν / (ν + 1)) * B ^ (1 / (ν + 1)) with hc1def
  set c2 := S * (Cν1 + B) with hc2def
  have hc10 : (0 : ℝ) ≤ c1 :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hB0 _)
  have hc20 : (0 : ℝ) < c2 := mul_pos hS0 (by linarith)
  refine ⟨c1 + c2, by linarith, ?_⟩
  intro ρ hρ δ hδ y hyrange hδy hxsrc z hz α hHR hds
  obtain ⟨hακ, hαmin⟩ := hHR
  have hα : (0 : ℝ) < (α : ℝ) := α.2
  have hκ0 : (0 : ℝ) < ‖K‖ ^ 2 := lt_of_lt_of_le hα hακ
  have hK : K ≠ 0 := by
    intro h
    rw [h] at hκ0
    simp at hκ0
  have hCrB : (⨆ b : Set.Ioi (0 : ℝ), ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
      |1 - lam * φ b lam|) ≤ B := iSup_abs_one_sub_mul_le_one_add hφ
  have hres : ∀ β : Set.Ioi (0 : ℝ), ∀ p q : F,
      ‖p - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β p)‖
        ≤ ‖q - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β q)‖ + B * ‖p - q‖ :=
    fun β p q => norm_residual_le_add hs hK hφ hCrB p q
  have hymem : y ∈ mpDomain K := Submodule.mem_sup_left hyrange
  have hKxd : K (moorePenrose K ⟨y, hymem⟩) = y := by
    rw [apply_moorePenrose ⟨_, hymem⟩]
    exact Submodule.starProjection_eq_self_iff.2
      (K.toLinearMap.range.le_topologicalClosure hyrange)
  obtain ⟨w, hwρ, hw⟩ := (mem_sourceSet_iff _ _ _ _ _).1 hxsrc
  have hwn : ‖w‖ ≤ ρ := hwρ
  set ds := ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z) - z‖ with hdsdef
  set M := max δ ds with hMdef
  have hδM : δ ≤ M := le_max_left _ _
  have hdsM : ds ≤ M := le_max_right _ _
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le hδ hδM
  have hdsrev : ‖z - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α
      z)‖ = ds := by rw [hdsdef, norm_sub_rev]
  obtain ⟨ξ, hξB, hkey⟩ :=
    exists_norm_le_and_sub_eq_absRpow (α := α) hs hφ hB1 hBub hν0 hymem hw
  have hξn : ‖ξ‖ ≤ B * ρ := hξB.trans (mul_le_mul_of_nonneg_left hwn hB0)
  have hnu1 : ‖hs.absRpow (ν + 1) (by linarith : (0:ℝ) ≤ ν + 1) ξ‖
      = ‖y - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y)‖ := by
    rw [hs.absRpow_congr (show ν + 1 = 1 + ν by ring) (by linarith) (by linarith),
      hs.absRpow_add one_pos hν0,
      ContinuousLinearMap.comp_apply, hs.norm_absRpow_one_apply_eq_norm_map, ← hkey, map_sub, hKxd]
  have hAres : ‖y - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y)‖ ≤ (1 + B) * M := by
    have h := hres α y z
    rw [hdsrev] at h
    have h2 : B * ‖y - z‖ ≤ B * M := mul_le_mul_of_nonneg_left (hz.trans hδM) hB0
    nlinarith [hdsM]
  have hexp : 1 - ν / (ν + 1) = 1 / (ν + 1) := by field_simp; ring
  have hinterp := hs.norm_absRpow_le_rpow_mul_rpow hν0.le (by linarith : ν < ν + 1) ξ
  rw [hexp, hnu1] at hinterp
  have hA : ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y - moorePenrose K ⟨y, hymem⟩‖
      ≤ c1 * (M ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1))) := by
    have hrev : ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y - moorePenrose K ⟨y,
        hymem⟩‖ = ‖hs.absRpow ν hν0.le ξ‖ := by
      rw [← hkey, norm_sub_rev]
    rw [hrev]
    refine hinterp.trans ?_
    have h1 : ‖y - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y)‖ ^ (ν / (ν + 1))
        ≤ ((1 + B) * M) ^ (ν / (ν + 1)) :=
      Real.rpow_le_rpow (norm_nonneg _) hAres (by positivity)
    have h2 : ‖ξ‖ ^ (1 / (ν + 1)) ≤ (B * ρ) ^ (1 / (ν + 1)) :=
      Real.rpow_le_rpow (norm_nonneg _) hξn (by positivity)
    have h3 : ((1 + B) * M) ^ (ν / (ν + 1)) * (B * ρ) ^ (1 / (ν + 1))
        = c1 * (M ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1))) := by
      rw [Real.mul_rpow (by linarith) hM0.le, Real.mul_rpow hB0 hρ.le, hc1def]
      ring
    calc ‖y - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y)‖ ^ (ν / (ν +
        1)) * ‖ξ‖ ^ (1 / (ν + 1))
        ≤ ((1 + B) * M) ^ (ν / (ν + 1)) * (B * ρ) ^ (1 / (ν + 1)) :=
          mul_le_mul h1 h2 (Real.rpow_nonneg (norm_nonneg _) _)
            (Real.rpow_nonneg (by positivity) _)
      _ = c1 * (M ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1))) := h3
  have ht : (0 : ℝ) < δ / ρ := div_pos hδ hρ
  obtain ⟨β, hβdef⟩ : ∃ β : Set.Ioi (0 : ℝ), (β : ℝ) = (δ / ρ) ^ (2 / (ν + 1)) :=
    ⟨⟨_, Set.mem_Ioi.2 (Real.rpow_pos_of_pos ht _)⟩, rfl⟩
  have hβ0 : (0 : ℝ) < (β : ℝ) := β.2
  have hβpow1 : (β : ℝ) ^ ((ν + 1) / 2) = δ / ρ := by
    rw [hβdef, ← Real.rpow_mul ht.le,
      show 2 / (ν + 1) * ((ν + 1) / 2) = 1 by field_simp, Real.rpow_one]
  have hβpowm : (β : ℝ) ^ (-(1 : ℝ) / 2) = (δ / ρ) ^ (-(1 : ℝ) / (ν + 1)) := by
    have hee : 2 / (ν + 1) * (-(1 : ℝ) / 2) = -(1 : ℝ) / (ν + 1) := by
      field_simp
    rw [hβdef, ← Real.rpow_mul ht.le, hee]
  have hyle : ‖y‖ ≤ (‖K‖ ^ 2) ^ ((ν + 1) / 2) * ρ :=
    norm_le_rpow_of_absRpow_eq hs hK hν0 hymem hKxd hw hwn
  have hβκ : (β : ℝ) ≤ ‖K‖ ^ 2 := by
    have hlt : δ / ρ < (‖K‖ ^ 2) ^ ((ν + 1) / 2) := by
      rw [div_lt_iff₀ hρ]
      linarith
    have h := Real.rpow_lt_rpow ht.le hlt (by positivity : (0 : ℝ) < 2 / (ν + 1))
    rw [← hβdef] at h
    refine h.le.trans ?_
    rw [← Real.rpow_mul hκ0.le, show (ν + 1) / 2 * (2 / (ν + 1)) = 1 by field_simp,
      Real.rpow_one]
  have key1 : δ * (δ / ρ) ^ (-(1 : ℝ) / (ν + 1))
      = δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1)) := by
    have h1 : (δ / ρ) ^ (-(1 : ℝ) / (ν + 1))
        = δ ^ (-(1 : ℝ) / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1)) := by
      rw [Real.div_rpow hδ.le hρ.le, div_eq_mul_inv]
      congr 1
      rw [show (-(1 : ℝ) / (ν + 1)) = -((1 : ℝ) / (ν + 1)) by ring, Real.rpow_neg hρ.le,
        inv_inv]
    rw [h1, ← mul_assoc]
    congr 1
    nth_rewrite 1 [← Real.rpow_one δ]
    rw [← Real.rpow_add hδ]
    congr 1
    field_simp; ring
  have hΨβ : (β : ℝ) ^ (-(1 : ℝ) / 2) * ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β
      z) - z‖
      ≤ (Cν1 + B) * (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))) := by
    obtain ⟨-, hom⟩ :=
      norm_spectralReg_sub_moorePenrose_le (α := β) hs hφ hν0 hρ hymem hxsrc
    rw [hKxd] at hom
    have hom2 : ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β y) - y‖ ≤ Cν1 * (β :
        ℝ) ^ ((ν + 1) / 2) * ρ :=
      hom.trans (mul_le_mul_of_nonneg_right (hCν1 β) hρ.le)
    have hzres : ‖z - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β z)‖
        ≤ ‖y - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β y)‖ + B * δ := by
      have h := hres β z y
      have h2 : B * ‖z - y‖ ≤ B * δ := by
        refine mul_le_mul_of_nonneg_left ?_ hB0
        rw [norm_sub_rev]; exact hz
      linarith
    have hyres : ‖y - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β
        y)‖ = ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β y) - y‖ :=
      norm_sub_rev _ _
    have hzres2 : ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β z) - z‖ ≤ Cν1 * (δ /
        ρ) * ρ + B * δ := by
      have hrev : ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β
          z) - z‖ = ‖z - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β z)‖ :=
        norm_sub_rev _ _
      rw [hβpow1] at hom2
      rw [hyres] at hzres
      rw [hrev]
      linarith
    have hfin : ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β z) - z‖ ≤ (Cν1 +
        B) * δ := by
      have hcancel : Cν1 * (δ / ρ) * ρ = Cν1 * δ := by field_simp
      rw [hcancel] at hzres2
      linarith
    have hβm0 : (0 : ℝ) ≤ (β : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hβ0.le _
    calc (β : ℝ) ^ (-(1 : ℝ) / 2) * ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β z) - z‖
        ≤ (β : ℝ) ^ (-(1 : ℝ) / 2) * ((Cν1 + B) * δ) :=
          mul_le_mul_of_nonneg_left hfin hβm0
      _ = (Cν1 + B) * (δ * (δ / ρ) ^ (-(1 : ℝ) / (ν + 1))) := by rw [hβpowm]; ring
      _ = (Cν1 + B) * (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))) := by rw [key1]
  have hΨα : (α : ℝ) ^ (-(1 : ℝ) / 2) * ds
      ≤ (Cν1 + B) * (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))) :=
    (hαmin β hβκ).trans hΨβ
  have hRnorm : ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α‖ ≤ S * (α : ℝ) ^ (-(1 : ℝ) /
      2) := by
    rw [hSdef]
    exact opNorm_spectralReg_le_rpow hs hφ hCF0.le (hCF.iSup_le α)
  have hBd : ‖spectralReg hs φ (hφ.exists_bound_on_spectrum
      hs) α z - spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y‖
      ≤ c2 * (δ / ds) * (M ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1))) := by
    have h1 : ‖spectralReg hs φ (hφ.exists_bound_on_spectrum
        hs) α z - spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y‖
          ≤ ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α‖ * δ := by
      have he : spectralReg hs φ (hφ.exists_bound_on_spectrum
          hs) α z - spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y
            = spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α (z - y) := by
        rw [map_sub]
      rw [he]
      refine ((spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α).le_opNorm _).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [norm_sub_rev]; exact hz
    have h2 : ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α‖ * δ ≤ S * ((α : ℝ) ^ (-(1 :
        ℝ) / 2) * δ) := by
      have := mul_le_mul_of_nonneg_right hRnorm hδ.le
      linarith [this]
    have h3 : (α : ℝ) ^ (-(1 : ℝ) / 2) * δ
        = (δ / ds) * ((α : ℝ) ^ (-(1 : ℝ) / 2) * ds) := by
      field_simp
    have h4 : (δ / ds) * ((α : ℝ) ^ (-(1 : ℝ) / 2) * ds)
        ≤ (δ / ds) * ((Cν1 + B) * (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1)))) :=
      mul_le_mul_of_nonneg_left hΨα (by positivity)
    have h5 : δ ^ (ν / (ν + 1)) ≤ M ^ (ν / (ν + 1)) :=
      Real.rpow_le_rpow hδ.le hδM (by positivity)
    have h6 : (0 : ℝ) ≤ ρ ^ ((1 : ℝ) / (ν + 1)) := Real.rpow_nonneg hρ.le _
    have h7 : (0 : ℝ) ≤ δ / ds := by positivity
    have h8 : (0 : ℝ) ≤ Cν1 + B := by linarith
    have h9 : δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))
        ≤ M ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1)) :=
      mul_le_mul_of_nonneg_right h5 h6
    have h10 : (δ / ds) * ((Cν1 + B) * (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))))
        ≤ (δ / ds) * ((Cν1 + B) * (M ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1)))) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h9 h8) h7
    calc ‖spectralReg hs φ (hφ.exists_bound_on_spectrum
        hs) α z - spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y‖
        ≤ ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α‖ * δ := h1
      _ ≤ S * ((α : ℝ) ^ (-(1 : ℝ) / 2) * δ) := h2
      _ = S * ((δ / ds) * ((α : ℝ) ^ (-(1 : ℝ) / 2) * ds)) := by rw [h3]
      _ ≤ S * ((δ / ds) * ((Cν1 + B) * (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))))) :=
          mul_le_mul_of_nonneg_left h4 hS0.le
      _ ≤ S * ((δ / ds) * ((Cν1 + B) * (M ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))))) :=
          mul_le_mul_of_nonneg_left h10 hS0.le
      _ = c2 * (δ / ds) * (M ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1))) := by rw [hc2def]; ring
  have hsplit : ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z - moorePenrose K ⟨y, hymem⟩‖
      ≤ ‖spectralReg hs φ (hφ.exists_bound_on_spectrum
          hs) α z - spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y‖
        + ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y - moorePenrose K ⟨y, hymem⟩‖ := by
    simpa using norm_add_le (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z - spectralReg
        hs φ (hφ.exists_bound_on_spectrum hs) α y)
      (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y - moorePenrose K ⟨y, hymem⟩)
  have hP0 : (0 : ℝ) ≤ M ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1)) :=
    mul_nonneg (Real.rpow_nonneg hM0.le _) (Real.rpow_nonneg hρ.le _)
  have ht0 : (0 : ℝ) ≤ δ / ds := div_nonneg hδ.le hds.le
  have hid : (c1 + c2) * (1 + δ / ds) * M ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1))
      = c1 * (M ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1)))
        + c2 * (δ / ds) * (M ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1)))
        + (c1 * (δ / ds) * (M ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1)))
          + c2 * (M ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1)))) := by ring
  rw [hid]
  linarith [hsplit, hA, hBd, mul_nonneg (mul_nonneg hc10 ht0) hP0,
    mul_nonneg hc20.le hP0]

end AutoIp

end _thm_hanke_raus_conditional
