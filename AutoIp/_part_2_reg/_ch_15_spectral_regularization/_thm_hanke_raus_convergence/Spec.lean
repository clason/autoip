/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_12_picard._def_source_set
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_filter
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_hanke_raus
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_qualification
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound
import AutoIp._part_2_reg._ch_11_moore_penrose._thm_mp_inverse
import AutoIp._part_2_reg._ch_12_picard._lem_source_in_kerperp
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_filter_norm_bound
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_omega_nu
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_residual_constant
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_spectral_residual_form
import AutoIp.Auxiliary.Rpow
import AutoIp._part_2_reg._ch_15_spectral_regularization._thm_hanke_raus_conditional
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

section _thm_hanke_raus_convergence

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Convergence of Hanke–Raus on data bounded away from the range: for a regularizing filter
satisfying (F) and (Q_{ν+1}), with `α ↦ φ_α(λ)` continuous on `(0,∞)` for each `λ ∈ (0, κ]`,
`ε > 0`, and `x† ∈ X_{ν,ρ}` with `ν, ρ > 0`, write `y^δ = Kx† + η` and `P_R` for the
orthogonal projection onto the closure of `Ran(K)`; then `A(y^δ) ≠ ∅` for every
`y^δ ≠ Kx†` with `‖(Id − P_R)η‖ ≥ ε‖η‖`, and
`lim_{δ→0} sup {‖R_{α*} y^δ − x†‖ : y^δ ∈ N_ε, ‖y^δ − Kx†‖ = δ, α* ∈ A(y^δ)} = 0`. Of the
prose's hypotheses on the filter only (F) and (Q_{ν+1}) are assumed, which is what
`ν ∈ (0, ν₀ − 1]` provides. (Q_{ν+1}) is asked for every `α > 0` rather than on `(0, κ]`,
which for a regularizing filter changes only the constant. -/
public theorem hankeRaus_convergence (hs : IsSingularSystem K σ v u) (hK : K ≠ 0)
    {φ : Set.Ioi (0 : ℝ) → ℝ → ℝ} {Cφ : ℝ}
    (hφ : IsRegularizingFilter K φ Cφ) {ν : ℝ}
    (hF : ∃ CF > (0 : ℝ), HasFilterBound K φ CF)
    (hQ : ∃ Cν > (0 : ℝ), ∀ α : Set.Ioi (0 : ℝ),
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
        lam ^ ((ν + 1) / 2) * |1 - lam * φ α lam|) ≤ Cν * (α : ℝ) ^ ((ν + 1) / 2))
    (hcont : ∀ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
      Continuous (fun a : Set.Ioi (0 : ℝ) => φ a lam))
    {ε : ℝ} (hε : 0 < ε) {ρ : ℝ} (hν : 0 < ν) (hρ : 0 < ρ)
    {x : E} (hx : x ∈ sourceSet hs ν hν ρ hρ) :
    (∀ z : F, z ≠ K x →
        ε * ‖z - K x‖ ≤
          ‖(z - K x) -
            K.toLinearMap.range.topologicalClosure.starProjection (z - K x)‖ →
        ∃ α, IsHankeRausChoiceOnSpectrum hs φ (hφ.exists_bound_on_spectrum hs) z α) ∧
    ∀ tol > (0 : ℝ), ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo (0 : ℝ) δ₀, ∀ z : F, ‖z - K x‖ = δ →
      ε * ‖z - K x‖ ≤
        ‖(z - K x) -
          K.toLinearMap.range.topologicalClosure.starProjection (z - K x)‖ →
        ∀ α, IsHankeRausChoiceOnSpectrum hs φ (hφ.exists_bound_on_spectrum
            hs) z α → ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z - x‖ < tol := by
  have hν0 : (0 : ℝ) < ν := hν
  have hν1 : (0 : ℝ) < ν + 1 := by linarith
  have he0 : (0 : ℝ) < ν / (ν + 1) := div_pos hν0 hν1
  have hCφ0 : (0 : ℝ) < Cφ := hφ.const_pos
  obtain ⟨CF, hCF0, hCFb⟩ := id hF
  obtain ⟨Cν1, hCν10, hCν1⟩ := id hQ
  set B := 1 + Cφ with hBdef
  have hB1 : (1 : ℝ) ≤ B := by rw [hBdef]; linarith [hφ.const_pos]
  have hBub : ∀ (b : Set.Ioi (0 : ℝ)), ∀ s ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2),
      |1 - s * φ b s| ≤ B :=
    fun _ _ hsm => abs_one_sub_mul_le_one_add hφ hsm
  -- The parameter of the family is positive, but the continuity argument below runs over
  -- the reals, so the proof reads the family through `ψ`, which agrees with it everywhere.
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ → ℝ → ℝ,
      ∀ (a : ℝ) (ha : 0 < a), ψ a = φ ⟨a, Set.mem_Ioi.2 ha⟩ :=
    ⟨fun a => if h : 0 < a then φ ⟨a, Set.mem_Ioi.2 h⟩ else 0, fun _ ha => by simp [ha]⟩
  have hψ' : ∀ a : Set.Ioi (0 : ℝ), ψ (a : ℝ) = φ a := fun a => hψ (a : ℝ) a.2
  have hψcont : ∀ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
      ContinuousOn (fun a : ℝ => ψ a lam) (Set.Ioi (0 : ℝ)) := by
    intro lam hlam
    rw [continuousOn_iff_continuous_domRestrict]
    exact (hcont lam hlam).congr fun a => (congrFun (hψ' a) lam).symm
  have hB0 : (0 : ℝ) ≤ B := by linarith
  have hκ0 : (0 : ℝ) < ‖K‖ ^ 2 := pow_pos (norm_pos_iff.mpr hK) 2
  obtain ⟨hCr1, hCrle, hresid⟩ := one_le_iSup_abs_one_sub_mul_and_norm_residual_le hs hK hφ
  have hCrB : (⨆ b : Set.Ioi (0 : ℝ), ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
      |1 - lam * φ b lam|) ≤ B := iSup_abs_one_sub_mul_le_one_add hφ
  obtain ⟨κ, hκ⟩ : ∃ κ : Set.Ioi (0 : ℝ), (κ : ℝ) = ‖K‖ ^ 2 := ⟨⟨_, Set.mem_Ioi.2 hκ0⟩, rfl⟩
  have hres : ∀ β : Set.Ioi (0 : ℝ), ∀ p q : F,
      ‖p - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β p)‖
        ≤ ‖q - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β q)‖ + B * ‖p - q‖ :=
    fun β p q => norm_residual_le_add hs hK hφ hCrB p q
  have hxperp : x ∈ (K.toLinearMap.ker)ᗮ := sourceSet_subset_orthogonal_ker hs hν0 hρ hx
  have hmpKx : moorePenrose K ⟨(K x), (Submodule.mem_sup_left ⟨x,
      rfl⟩)⟩ = x := moorePenrose_apply_apply_of_mem_orthogonal hxperp
  have hKxrange : (K x : F) ∈ K.toLinearMap.range := ⟨x, rfl⟩
  have hxsrc : moorePenrose K ⟨(K x), (Submodule.mem_sup_left ⟨x,
      rfl⟩)⟩ ∈ sourceSet hs ν hν ρ hρ := by rw [hmpKx]; exact hx
  obtain ⟨w, hwρ, hw⟩ := (mem_sourceSet_iff _ _ _ _ _).1 hx
  have hwn : ‖w‖ ≤ ρ := hwρ
  have hQeq : ∀ q : F,
      q - K.toLinearMap.range.topologicalClosure.starProjection q
        = (K.toLinearMap.range.topologicalClosure)ᗮ.starProjection q := fun q =>
    (eq_sub_of_add_eq' (Submodule.starProjection_add_starProjection_orthogonal
      (K := K.toLinearMap.range.topologicalClosure) q)).symm
  have hQnorm : ∀ q : F,
      ‖(K.toLinearMap.range.topologicalClosure)ᗮ.starProjection q‖ ≤ ‖q‖ := by
    intro q
    have h := Submodule.norm_sq_eq_add_norm_sq_starProjection q
      K.toLinearMap.range.topologicalClosure
    have hb2 : ‖(K.toLinearMap.range.topologicalClosure)ᗮ.starProjection q‖ ^ 2
        ≤ ‖q‖ ^ 2 := by
      rw [h]
      linarith [sq_nonneg
        ‖K.toLinearMap.range.topologicalClosure.starProjection q‖]
    exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hb2
  have hQvanish : ∀ q : F, q ∈ K.toLinearMap.range.topologicalClosure →
      (K.toLinearMap.range.topologicalClosure)ᗮ.starProjection q = 0 := by
    intro q hq
    rw [← hQeq, Submodule.starProjection_eq_self_iff.2 hq, sub_self]
  have hKxN : (K x : F) ∈ K.toLinearMap.range.topologicalClosure :=
    K.toLinearMap.range.le_topologicalClosure hKxrange
  have hlowres : ∀ (z : F) (a : Set.Ioi (0 : ℝ)),
      ‖(z - K x) - K.toLinearMap.range.topologicalClosure.starProjection
          (z - K x)‖ ≤ ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) a z) - z‖ := by
    intro z a
    have hKRN : (K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) a z) : F)
        ∈ K.toLinearMap.range.topologicalClosure :=
      K.toLinearMap.range.le_topologicalClosure ⟨spectralReg hs φ
          (hφ.exists_bound_on_spectrum hs) a z, rfl⟩
    rw [hQeq, map_sub, hQvanish _ hKxN, sub_zero]
    calc ‖(K.toLinearMap.range.topologicalClosure)ᗮ.starProjection z‖
        = ‖(K.toLinearMap.range.topologicalClosure)ᗮ.starProjection
            (K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) a z) - z)‖ := by
          rw [map_sub, hQvanish _ hKRN, zero_sub, norm_neg]
      _ ≤ ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) a z) - z‖ := hQnorm _
  have hexist : ∀ (d : ℝ), 0 < d → ∀ z : F, ‖z - K x‖ = d →
      ε * ‖z - K x‖ ≤
        ‖(z - K x) - K.toLinearMap.range.topologicalClosure.starProjection
          (z - K x)‖ →
      ∃ α, IsHankeRausChoiceOnSpectrum hs φ (hφ.exists_bound_on_spectrum hs) z α := by
    intro d hd z hzd hzlow
    have hlb : ∀ a : Set.Ioi (0 : ℝ), ε * d ≤ ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum
        hs) a z) - z‖ := by
      intro a
      rw [← hzd]
      exact hzlow.trans (hlowres z a)
    -- The residual depends on the parameter only through `φ a`, so the Hanke--Raus
    -- functional is a function of a *real* parameter, where the continuity argument lives.
    obtain ⟨Θ, hΘ⟩ : ∃ Θ : ℝ → ℝ, ∀ a : ℝ, Θ a =
        Real.sqrt (‖z - K.toLinearMap.range.topologicalClosure.starProjection z‖ ^ 2
          + ∑' i, |1 - σ i ^ 2 * ψ a (σ i ^ 2)| ^ 2 * ‖(inner 𝕜 (u i) z : 𝕜)‖ ^ 2) :=
      ⟨_, fun _ => rfl⟩
    have hsq : ∀ a : Set.Ioi (0 : ℝ),
        ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) a z) - z‖ = Θ (a : ℝ) := by
      intro a
      obtain ⟨-, hr, hresn⟩ := hasSum_starProjection_sub_apply_spectralReg_and_norm_sq (α := a) hs
        (hφ.exists_bound_on_spectrum hs) z
      rw [← hr.tsum_eq] at hresn
      rw [hΘ, hψ' a, norm_sub_rev, ← hresn, Real.sqrt_sq (norm_nonneg _)]
    have hsummable : Summable (fun i => B ^ 2 * ‖(inner 𝕜 (u i) z : 𝕜)‖ ^ 2) :=
      (hs.orthonormal_right.inner_products_summable (x := z)).mul_left _
    have htsum : ContinuousOn
        (fun a => ∑' i, |1 - σ i ^ 2 * ψ a (σ i ^ 2)| ^ 2 * ‖(inner 𝕜 (u i) z : 𝕜)‖ ^ 2)
        (Set.Ioi (0 : ℝ)) := by
      refine continuousOn_tsum ?_ hsummable ?_
      · intro i
        have hci := hψcont (σ i ^ 2) ⟨pow_pos (hs.pos i) 2, (hs.sq_mem_Icc i).2⟩
        exact ((((continuousOn_const.sub (continuousOn_const.mul hci)).abs).pow 2).mul
          continuousOn_const)
      · intro i a ha
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hψ a ha]
        have hb := hBub ⟨a, Set.mem_Ioi.2 ha⟩ (σ i ^ 2) (hs.sq_mem_Icc i)
        have hsq2 : |1 - σ i ^ 2 * φ ⟨a, Set.mem_Ioi.2 ha⟩ (σ i ^ 2)| ^ 2 ≤ B ^ 2 := by
          have h0 := abs_nonneg (1 - σ i ^ 2 * φ ⟨a, Set.mem_Ioi.2 ha⟩ (σ i ^ 2))
          exact pow_le_pow_left₀ h0 hb 2
        exact mul_le_mul_of_nonneg_right hsq2 (by positivity)
    have hθcont : ContinuousOn Θ (Set.Ioi (0 : ℝ)) :=
      (Real.continuous_sqrt.comp_continuousOn (continuousOn_const.add htsum)).congr
        (fun a _ => hΘ a)
    have hrpowcont : ContinuousOn (fun a : ℝ => a ^ (-(1 : ℝ) / 2)) (Set.Ioi (0 : ℝ)) :=
      fun a ha => (Real.continuousAt_rpow_const a _ (Or.inl (ne_of_gt ha))).continuousWithinAt
    have hΨcont : ContinuousOn (fun a : ℝ => a ^ (-(1 : ℝ) / 2) * Θ a)
        (Set.Ioi (0 : ℝ)) := hrpowcont.mul hθcont
    have hΘ0 : ∀ a : ℝ, (0 : ℝ) ≤ Θ a := fun a => by rw [hΘ]; positivity
    have hΨlb : ∀ a : ℝ, ∀ ha : 0 < a,
        ε * d * a ^ (-(1 : ℝ) / 2) ≤ a ^ (-(1 : ℝ) / 2) * Θ a := by
      intro a ha
      have h := hlb ⟨a, Set.mem_Ioi.2 ha⟩
      rw [hsq ⟨a, Set.mem_Ioi.2 ha⟩] at h
      have hp : (0 : ℝ) ≤ a ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg ha.le _
      calc ε * d * a ^ (-(1 : ℝ) / 2) = a ^ (-(1 : ℝ) / 2) * (ε * d) := by ring
        _ ≤ a ^ (-(1 : ℝ) / 2) * Θ a := mul_le_mul_of_nonneg_left h hp
    have hΨκ0 : (0 : ℝ) ≤ (‖K‖ ^ 2) ^ (-(1 : ℝ) / 2) * Θ (‖K‖ ^ 2) :=
      mul_nonneg (Real.rpow_nonneg hκ0.le _) (hΘ0 _)
    set Ψκ := (‖K‖ ^ 2) ^ (-(1 : ℝ) / 2) * Θ (‖K‖ ^ 2) with hΨκdef
    have hCpos : (0 : ℝ) < Ψκ + 1 := by linarith
    set β₀ := min (‖K‖ ^ 2) ((ε * d / (Ψκ + 1)) ^ 2) with hβ₀def
    have hβ₀0 : 0 < β₀ := lt_min hκ0 (pow_pos (div_pos (mul_pos hε hd) hCpos) 2)
    have hβ₀κ : β₀ ≤ ‖K‖ ^ 2 := min_le_left _ _
    have hsub : Set.Icc β₀ (‖K‖ ^ 2) ⊆ Set.Ioi (0 : ℝ) :=
      fun b hb => lt_of_lt_of_le hβ₀0 hb.1
    obtain ⟨α₀, hα₀mem, hα₀min⟩ :=
      (isCompact_Icc (a := β₀) (b := ‖K‖ ^ 2)).exists_isMinOn
        ⟨‖K‖ ^ 2, ⟨hβ₀κ, le_rfl⟩⟩ (hΨcont.mono hsub)
    refine ⟨⟨α₀, Set.mem_Ioi.2 (lt_of_lt_of_le hβ₀0 hα₀mem.1)⟩, hα₀mem.2, ?_⟩
    intro b hbκ
    rw [hsq, hsq]
    rcases le_or_gt β₀ (b : ℝ) with hbge | hblt
    · exact hα₀min ⟨hbge, hbκ⟩
    · have hΨκle : α₀ ^ (-(1 : ℝ) / 2) * Θ α₀ ≤ Ψκ := hα₀min ⟨hβ₀κ, le_rfl⟩
      have hb0 : (0 : ℝ) < (b : ℝ) := b.2
      have hbsq : (b : ℝ) < (ε * d / (Ψκ + 1)) ^ 2 := lt_of_lt_of_le hblt (min_le_right _ _)
      have hbrp : (b : ℝ) ^ (-(1 : ℝ) / 2) = (Real.sqrt (b : ℝ))⁻¹ := by
        rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring, Real.rpow_neg hb0.le,
          ← Real.sqrt_eq_rpow]
      have hsb : 0 < Real.sqrt (b : ℝ) := Real.sqrt_pos.mpr hb0
      have hsblt : Real.sqrt (b : ℝ) < ε * d / (Ψκ + 1) := by
        have h := Real.sqrt_lt_sqrt hb0.le hbsq
        rwa [Real.sqrt_sq (div_pos (mul_pos hε hd) hCpos).le] at h
      have hstep : Ψκ + 1 < ε * d / Real.sqrt (b : ℝ) := by
        rw [lt_div_iff₀ hsb]
        rw [lt_div_iff₀ hCpos] at hsblt
        linarith
      have hfin : Ψκ < ε * d * (b : ℝ) ^ (-(1 : ℝ) / 2) := by
        rw [hbrp, ← div_eq_mul_inv]
        linarith
      linarith [hΨlb (b : ℝ) hb0]
  refine ⟨fun z hz hlow =>
    hexist ‖z - K x‖ (norm_pos_iff.mpr (sub_ne_zero_of_ne hz)) z rfl hlow, ?_⟩
  obtain ⟨c, hc0, hcb⟩ := norm_spectralReg_sub_moorePenrose_le_hankeRaus hs hφ hF hQ hν
  intro tol htol
  by_cases hx0 : (K x : F) = 0
  · have hxzero : x = 0 := by
      have hmem : x ∈ K.toLinearMap.ker ⊓ (K.toLinearMap.ker)ᗮ :=
        ⟨by simpa using hx0, hxperp⟩
      rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hmem
    set Λ := Real.sqrt (Cφ * CF) * ((‖K‖ ^ 2) ^ (-(1 : ℝ) / 2) * B / ε) with hΛdef
    have hΛ0 : (0 : ℝ) ≤ Λ :=
      mul_nonneg (Real.sqrt_nonneg _)
        (div_nonneg (mul_nonneg (Real.rpow_nonneg hκ0.le _) hB0) hε.le)
    refine ⟨tol / (Λ + 1), div_pos htol (by linarith), ?_⟩
    intro δ hδ z hzd hzlow
    have hδ0 : 0 < δ := hδ.1
    intro α hHR
    obtain ⟨hακ, hαmin⟩ := hHR
    have hα : (0 : ℝ) < (α : ℝ) := α.2
    have hzn : ‖z‖ = δ := by rw [← hzd, hx0, sub_zero]
    have hlbα : ε * δ ≤ ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z) - z‖ := by
      rw [← hzd]
      exact hzlow.trans (hlowres z α)
    have hubκ : ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) κ z) - z‖ ≤ B * δ := by
      have h := hres κ z z
      have h2 := hresid z κ
      have h3 : (⨆ b : Set.Ioi (0 : ℝ), ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
          |1 - lam * φ b lam|) * ‖z‖ ≤ B * ‖z‖ :=
        mul_le_mul_of_nonneg_right hCrB (norm_nonneg _)
      rw [norm_sub_rev]
      rw [hzn] at h2 h3
      linarith
    have hmin := hαmin κ hκ.le
    rw [hκ] at hmin
    have hαinv : (α : ℝ) ^ (-(1 : ℝ) / 2) * (ε * δ)
        ≤ (‖K‖ ^ 2) ^ (-(1 : ℝ) / 2) * (B * δ) := by
      have hp : (0 : ℝ) ≤ (α : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hα.le _
      have hpκ : (0 : ℝ) ≤ (‖K‖ ^ 2) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hκ0.le _
      calc (α : ℝ) ^ (-(1 : ℝ) / 2) * (ε * δ)
          ≤ (α : ℝ) ^ (-(1 : ℝ) / 2) * ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α
              z) - z‖ :=
            mul_le_mul_of_nonneg_left hlbα hp
        _ ≤ (‖K‖ ^ 2) ^ (-(1 : ℝ) / 2) * ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) κ
            z) - z‖ := hmin
        _ ≤ (‖K‖ ^ 2) ^ (-(1 : ℝ) / 2) * (B * δ) := mul_le_mul_of_nonneg_left hubκ hpκ
    have hαinv2 : (α : ℝ) ^ (-(1 : ℝ) / 2) ≤ (‖K‖ ^ 2) ^ (-(1 : ℝ) / 2) * B / ε := by
      rw [le_div_iff₀ hε]
      have hmul : (α : ℝ) ^ (-(1 : ℝ) / 2) * ε * δ
          ≤ (‖K‖ ^ 2) ^ (-(1 : ℝ) / 2) * B * δ := by
        have e1 : (α : ℝ) ^ (-(1 : ℝ) / 2) * ε * δ
            = (α : ℝ) ^ (-(1 : ℝ) / 2) * (ε * δ) := by ring
        have e2 : (‖K‖ ^ 2) ^ (-(1 : ℝ) / 2) * B * δ
            = (‖K‖ ^ 2) ^ (-(1 : ℝ) / 2) * (B * δ) := by ring
        rw [e1, e2]
        exact hαinv
      exact le_of_mul_le_mul_right hmul hδ0
    have hRnorm : ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α‖ ≤ Real.sqrt (Cφ *
        CF) * (α : ℝ) ^ (-(1 : ℝ) / 2) :=
      opNorm_spectralReg_le_rpow hs hφ hCF0.le (hCFb.iSup_le α)
    have hfinal : ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z - x‖ ≤ Λ * δ := by
      rw [hxzero, sub_zero]
      have h1 : ‖spectralReg hs φ (hφ.exists_bound_on_spectrum
          hs) α z‖ ≤ ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α‖ * δ := by
        rw [← hzn]
        exact (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α).le_opNorm z
      have h2 : ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α‖ * δ
          ≤ Real.sqrt (Cφ * CF) * (α : ℝ) ^ (-(1 : ℝ) / 2) * δ :=
        mul_le_mul_of_nonneg_right hRnorm hδ0.le
      have h3 : Real.sqrt (Cφ * CF) * (α : ℝ) ^ (-(1 : ℝ) / 2) * δ ≤ Λ * δ := by
        rw [hΛdef]
        refine mul_le_mul_of_nonneg_right ?_ hδ0.le
        exact mul_le_mul_of_nonneg_left hαinv2 (Real.sqrt_nonneg _)
      linarith
    have hlt : Λ * δ < tol := by
      have h1 : δ < tol / (Λ + 1) := hδ.2
      have h2 : (0 : ℝ) < Λ + 1 := by linarith
      rw [lt_div_iff₀ h2] at h1
      linarith
    linarith
  · have hKx0 : 0 < ‖K x‖ := norm_pos_iff.mpr hx0
    have hyle : ‖K x‖ ≤ (‖K‖ ^ 2) ^ ((ν + 1) / 2) * ρ := by
      have h1 : ‖hs.absRpow ν hν0.le w‖ ≤ (‖K‖ ^ 2) ^ (ν / 2) * ρ :=
        le_trans ((hs.absRpow ν hν0.le).le_opNorm w)
          (mul_le_mul (hs.norm_absRpow_le hν0) hwn (norm_nonneg _)
            (Real.rpow_nonneg (sq_nonneg _) _))
      rw [hw] at h1
      calc ‖K x‖ ≤ ‖K‖ * ‖x‖ := K.le_opNorm x
        _ ≤ ‖K‖ * ((‖K‖ ^ 2) ^ (ν / 2) * ρ) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = (‖K‖ ^ 2) ^ ((ν + 1) / 2) * ρ := by
            rw [← mul_assoc, mul_rpow_sq_div_two (norm_pos_iff.mpr hK)]
    set G := Real.sqrt (‖K‖ ^ 2) * (Cν1 + B) * ρ ^ ((1 : ℝ) / (ν + 1)) with hGdef
    set T := c * (1 + 1 / ε) * ρ ^ ((1 : ℝ) / (ν + 1)) with hTdef
    have hcontbd : Continuous
        (fun dd : ℝ => T * (max dd (G * dd ^ (ν / (ν + 1)))) ^ (ν / (ν + 1))) := by
      have hcr : Continuous (fun dd : ℝ => dd ^ (ν / (ν + 1))) :=
        Real.continuous_rpow_const he0.le
      exact continuous_const.mul (hcr.comp (continuous_id.max (continuous_const.mul hcr)))
    have hval : T * (max (0 : ℝ) (G * (0 : ℝ) ^ (ν / (ν + 1)))) ^ (ν / (ν + 1)) = 0 := by
      rw [Real.zero_rpow he0.ne', mul_zero, max_self, Real.zero_rpow he0.ne', mul_zero]
    have hlim : Tendsto
        (fun dd : ℝ => T * (max dd (G * dd ^ (ν / (ν + 1)))) ^ (ν / (ν + 1))) (𝓝 0) (𝓝 0) := by
      have h := hcontbd.tendsto 0
      rwa [hval] at h
    obtain ⟨δ₁, hδ₁0, hδ₁⟩ :=
      Metric.eventually_nhds_iff.mp (hlim.eventually (gt_mem_nhds htol))
    refine ⟨min δ₁ ‖K x‖, lt_min hδ₁0 hKx0, ?_⟩
    intro δ hδ z hzd hzlow
    have hδ0 : 0 < δ := hδ.1
    have hδlt : δ < ‖K x‖ := lt_of_lt_of_le hδ.2 (min_le_right _ _)
    have hδ1lt : δ < δ₁ := lt_of_lt_of_le hδ.2 (min_le_left _ _)
    intro α hHR
    obtain ⟨hακ, hαmin⟩ := hHR
    have hα : (0 : ℝ) < (α : ℝ) := α.2
    have hyz : ‖K x - z‖ ≤ δ := by rw [norm_sub_rev, hzd]
    have hlbα : ε * δ ≤ ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z) - z‖ := by
      rw [← hzd]
      exact hzlow.trans (hlowres z α)
    have hds0 : (0 : ℝ) < ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z) - z‖ :=
      lt_of_lt_of_le (mul_pos hε hδ0) hlbα
    have htt : (0 : ℝ) < δ / ρ := div_pos hδ0 hρ
    have hβd0 : (0 : ℝ) < (δ / ρ) ^ (2 / (ν + 1)) := Real.rpow_pos_of_pos htt _
    obtain ⟨βd, hβd⟩ : ∃ βd : Set.Ioi (0 : ℝ), (βd : ℝ) = (δ / ρ) ^ (2 / (ν + 1)) :=
      ⟨⟨_, Set.mem_Ioi.2 hβd0⟩, rfl⟩
    have hβdpow1 : (βd : ℝ) ^ ((ν + 1) / 2) = δ / ρ := by
      rw [hβd, ← Real.rpow_mul htt.le,
        show 2 / (ν + 1) * ((ν + 1) / 2) = 1 by field_simp, Real.rpow_one]
    have hβdpowm : (βd : ℝ) ^ (-(1 : ℝ) / 2)
        = (δ / ρ) ^ (-(1 : ℝ) / (ν + 1)) := by
      have hee : 2 / (ν + 1) * (-(1 : ℝ) / 2) = -(1 : ℝ) / (ν + 1) := by
        field_simp
      rw [hβd, ← Real.rpow_mul htt.le, hee]
    have hβdκ : (βd : ℝ) ≤ ‖K‖ ^ 2 := by
      rw [hβd]
      have hlt : δ / ρ < (‖K‖ ^ 2) ^ ((ν + 1) / 2) := by
        rw [div_lt_iff₀ hρ]
        linarith
      have h := Real.rpow_lt_rpow htt.le hlt (by positivity : (0 : ℝ) < 2 / (ν + 1))
      refine h.le.trans ?_
      rw [← Real.rpow_mul hκ0.le, show (ν + 1) / 2 * (2 / (ν + 1)) = 1 by field_simp,
        Real.rpow_one]
    have key1 : δ * (δ / ρ) ^ (-(1 : ℝ) / (ν + 1))
        = δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1)) := by
      have h1 : (δ / ρ) ^ (-(1 : ℝ) / (ν + 1))
          = δ ^ (-(1 : ℝ) / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1)) := by
        rw [Real.div_rpow hδ0.le hρ.le, div_eq_mul_inv]
        congr 1
        rw [show (-(1 : ℝ) / (ν + 1)) = -((1 : ℝ) / (ν + 1)) by ring, Real.rpow_neg hρ.le,
          inv_inv]
      rw [h1, ← mul_assoc]
      congr 1
      nth_rewrite 1 [← Real.rpow_one δ]
      rw [← Real.rpow_add hδ0]
      congr 1
      field_simp; ring
    have hΨβd : (βd : ℝ) ^ (-(1 : ℝ) / 2) *
        ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) βd z) - z‖
        ≤ (Cν1 + B) * (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))) := by
      obtain ⟨-, hom⟩ := norm_spectralReg_sub_moorePenrose_le (α := βd) hs hφ hν0 hρ
        (Submodule.mem_sup_left hKxrange) hxsrc
      rw [hmpKx] at hom
      have hom2 : ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) βd (K x)) - K x‖
          ≤ Cν1 * (βd : ℝ) ^ ((ν + 1) / 2) * ρ :=
        hom.trans (mul_le_mul_of_nonneg_right (hCν1 βd) hρ.le)
      have hzres : ‖z - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) βd z)‖
          ≤ ‖K x - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) βd (K x))‖ + B * δ := by
        have h := hres βd z (K x)
        have h2 : B * ‖z - K x‖ ≤ B * δ := by
          refine mul_le_mul_of_nonneg_left ?_ hB0
          rw [hzd]
        linarith
      have hyres : ‖K x - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) βd (K x))‖
          = ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) βd (K
              x)) - K x‖ := norm_sub_rev _ _
      have hzres2 : ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) βd z) - z‖
          ≤ Cν1 * (δ / ρ) * ρ + B * δ := by
        have hrev : ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) βd z) - z‖
            = ‖z - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) βd z)‖ := norm_sub_rev _ _
        rw [hβdpow1] at hom2
        rw [hyres] at hzres
        rw [hrev]
        linarith
      have hfin : ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) βd z) - z‖ ≤ (Cν1 +
          B) * δ := by
        have hcancel : Cν1 * (δ / ρ) * ρ = Cν1 * δ := by field_simp
        rw [hcancel] at hzres2
        linarith
      have hβm0 : (0 : ℝ) ≤ (βd : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg βd.2.le _
      calc (βd : ℝ) ^ (-(1 : ℝ) / 2) * ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) βd
          z) - z‖
          ≤ (βd : ℝ) ^ (-(1 : ℝ) / 2) * ((Cν1 + B) * δ) :=
            mul_le_mul_of_nonneg_left hfin hβm0
        _ = (Cν1 + B) * (δ * (δ / ρ) ^ (-(1 : ℝ) / (ν + 1))) := by rw [hβdpowm]; ring
        _ = (Cν1 + B) * (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))) := by rw [key1]
    have hdsbound : ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z) - z‖ ≤ G * δ ^ (ν
        / (ν + 1)) := by
      have hαpow : (α : ℝ) ^ ((1 : ℝ) / 2) *
          ((α : ℝ) ^ (-(1 : ℝ) / 2) * ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z)
              - z‖)
          = ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z) - z‖ := by
        rw [← mul_assoc, ← Real.rpow_add hα,
          show (1 : ℝ) / 2 + -(1 : ℝ) / 2 = 0 by ring, Real.rpow_zero, one_mul]
      have hΨle : (α : ℝ) ^ (-(1 : ℝ) / 2) * ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum
          hs) α z) - z‖
          ≤ (Cν1 + B) * (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))) :=
        (hαmin βd hβdκ).trans hΨβd
      have hαsq : (α : ℝ) ^ ((1 : ℝ) / 2) ≤ (‖K‖ ^ 2) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow hα.le hακ (by norm_num)
      calc ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z) - z‖
          = (α : ℝ) ^ ((1 : ℝ) / 2) *
              ((α : ℝ) ^ (-(1 : ℝ) / 2) * ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α
                  z) - z‖) := hαpow.symm
        _ ≤ (‖K‖ ^ 2) ^ ((1 : ℝ) / 2) *
              ((Cν1 + B) * (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1)))) :=
            mul_le_mul hαsq hΨle
              (mul_nonneg (Real.rpow_nonneg hα.le _) (norm_nonneg _))
              (Real.rpow_nonneg hκ0.le _)
        _ = G * δ ^ (ν / (ν + 1)) := by
            rw [hGdef, ← Real.sqrt_eq_rpow]; ring
    have hratio : δ / ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z) - z‖ ≤ 1 / ε := by
      rw [div_le_div_iff₀ hds0 hε]
      linarith
    have hmaxle : max δ ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z) - z‖
        ≤ max δ (G * δ ^ (ν / (ν + 1))) := max_le_max le_rfl hdsbound
    have hbound := hcb ρ hρ δ hδ0 (K x) hKxrange hδlt hxsrc z hyz α ⟨hακ, hαmin⟩ hds0
    rw [hmpKx] at hbound
    have hstep : c * (1 + δ / ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z) - z‖) *
          (max δ ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z) - z‖) ^ (ν / (ν +
              1)) * ρ ^ (1 / (ν + 1))
        ≤ T * (max δ (G * δ ^ (ν / (ν + 1)))) ^ (ν / (ν + 1)) := by
      have h3 : (max δ ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z) - z‖) ^ (ν / (ν
          + 1))
          ≤ (max δ (G * δ ^ (ν / (ν + 1)))) ^ (ν / (ν + 1)) :=
        Real.rpow_le_rpow (le_trans hδ0.le (le_max_left _ _)) hmaxle he0.le
      have h4 : (0 : ℝ) ≤ ρ ^ ((1 : ℝ) / (ν + 1)) := Real.rpow_nonneg hρ.le _
      have h2 : c * (1 + δ / ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z) -
          z‖) ≤ c * (1 + 1 / ε) := by
        have : (1 : ℝ) + δ / ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α
            z) - z‖ ≤ 1 + 1 / ε := by linarith
        exact mul_le_mul_of_nonneg_left this hc0.le
      have h5 : (0 : ℝ) ≤ c * (1 + 1 / ε) :=
        mul_nonneg hc0.le (by positivity)
      have h6 : c * (1 + δ / ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z) - z‖) *
            (max δ ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z) - z‖) ^ (ν / (ν + 1))
          ≤ c * (1 + 1 / ε) * (max δ (G * δ ^ (ν / (ν + 1)))) ^ (ν / (ν + 1)) :=
        mul_le_mul h2 h3 (Real.rpow_nonneg (le_trans hδ0.le (le_max_left _ _)) _) h5
      calc c * (1 + δ / ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z) - z‖) *
              (max δ ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z) - z‖) ^ (ν / (ν +
                  1)) * ρ ^ (1 / (ν + 1))
          ≤ c * (1 + 1 / ε) * (max δ (G * δ ^ (ν / (ν + 1)))) ^ (ν / (ν + 1)) *
              ρ ^ (1 / (ν + 1)) := mul_le_mul_of_nonneg_right h6 h4
        _ = T * (max δ (G * δ ^ (ν / (ν + 1)))) ^ (ν / (ν + 1)) := by rw [hTdef]; ring
    have hlast : T * (max δ (G * δ ^ (ν / (ν + 1)))) ^ (ν / (ν + 1)) < tol := by
      refine hδ₁ ?_
      rw [Real.dist_eq, sub_zero, abs_of_pos hδ0]
      exact hδ1lt
    linarith

end AutoIp

end _thm_hanke_raus_convergence
