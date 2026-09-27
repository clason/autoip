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
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_bounded
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_hom
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_approx_error_spectral

section _lem_general_omega

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Approximation error at a general index function: for `y ∈ Dom(K†)` with
`x† ∈ X_{φ,ρ}`, `φ` an index function and `ρ > 0`, the spectral regularization
`x_α := R_α y` satisfies `‖x_α - x†‖ ≤ ω_φ(α) ρ` for every `α > 0`. -/
public
theorem norm_spectralReg_sub_moorePenrose_le_iSup (hs : IsSingularSystem K σ v u) {flt : Set.Ioi
    (0 : ℝ) → ℝ → ℝ}
    {Cflt : ℝ} (hflt : IsRegularizingFilter K flt Cflt) {φ : ℝ → ℝ} {ρ : ℝ} {α : Set.Ioi (0 : ℝ)}
    (hφ : IsIndexFunction (‖K‖ ^ 2) φ) (hρ : 0 < ρ)
    {y : F} (hy : y ∈ mpDomain K)
    (hx : moorePenrose K ⟨y, hy⟩ ∈ sourceSetIndex hs φ (hφ.exists_bound_on_spectrum hs) ρ hρ) :
    ‖spectralReg hs flt (hflt.exists_bound_on_spectrum hs) α y - moorePenrose K ⟨y, hy⟩‖ ≤
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), φ lam * |1 - lam * flt α lam|) * ρ :=
  by
  have hC0 : (0:ℝ) < Cflt := hflt.const_pos
  have h1C : (0:ℝ) ≤ 1 + Cflt := by linarith
  have hk0 : (0:ℝ) ≤ ‖K‖ ^ 2 := by positivity
  have hkmem : (‖K‖ ^ 2) ∈ Set.Icc (0:ℝ) (‖K‖ ^ 2) := ⟨hk0, le_rfl⟩
  have hr : ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |1 - t * flt α t| ≤ 1 + Cflt := by
    intro t ht
    rcases ht.1.lt_or_eq with h0 | h0
    · have h := hflt.mul_abs_le α t ⟨h0, ht.2⟩
      have habs : |t * flt α t| ≤ Cflt := by rw [abs_mul, abs_of_pos h0]; exact h
      rw [abs_le] at habs ⊢
      constructor <;> linarith [habs.1, habs.2]
    · rw [← h0]
      simp only [zero_mul, sub_zero, abs_one]
      linarith
  have hφmono : ∀ t ∈ Set.Icc (0:ℝ) (‖K‖ ^ 2), φ t ≤ φ (‖K‖ ^ 2) :=
    fun t ht => hφ.strictMonoOn.monotoneOn ht hkmem ht.2
  set ω := ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), φ lam * |1 - lam * flt α lam| with hωdef
  have hω0 : (0:ℝ) ≤ ω :=
    Real.iSup_nonneg fun lam => Real.iSup_nonneg fun hl =>
      mul_nonneg (hφ.nonneg lam ⟨hl.1.le, hl.2⟩) (abs_nonneg _)
  have hbdd : BddAbove (Set.range (fun lam : ℝ =>
      ⨆ _ : lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), φ lam * |1 - lam * flt α lam|)) := by
    refine ⟨φ (‖K‖ ^ 2) * (1 + Cflt), ?_⟩
    rintro _ ⟨lam, rfl⟩
    refine Real.iSup_le (fun hl => ?_) (mul_nonneg (hφ.nonneg _ hkmem) h1C)
    exact mul_le_mul (hφmono lam ⟨hl.1.le, hl.2⟩) (hr lam ⟨hl.1.le, hl.2⟩)
      (abs_nonneg _) (hφ.nonneg _ hkmem)
  have hωle : ∀ i, φ (σ i ^ 2) * |1 - σ i ^ 2 * flt α (σ i ^ 2)| ≤ ω := by
    intro i
    have h1 := le_ciSup hbdd (σ i ^ 2)
    rwa [ciSup_pos (show σ i ^ 2 ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2) from
      ⟨pow_pos (hs.pos i) 2, (hs.sq_mem_Icc i).2⟩)] at h1
  rw [mem_sourceSetIndex_iff] at hx
  obtain ⟨w, hw, hxw⟩ := hx
  obtain ⟨hh1, -⟩ := moorePenrose_sub_spectralReg_eq_funCalc (α := α) hs hflt hy
  have hbr : ∃ cc, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2),
      |(fun lam => 1 - lam * flt α lam) t| ≤ cc := ⟨1 + Cflt, hr⟩
  have hbpsi : ∃ cc, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |φ t| ≤ cc :=
    ⟨φ (‖K‖ ^ 2), fun t ht => by
      rw [abs_of_nonneg (hφ.nonneg t ht)]; exact hφmono t ht⟩
  have hbrsq := hs.exists_bound_sq hbr
  have hbpsisq := hφ.exists_bound_on_spectrum hs
  set g : ℝ → ℝ := (fun lam => 1 - lam * flt α lam) * φ with hgdef
  have hbg : ∃ cc, ∀ i, |g (σ i ^ 2)| ≤ cc := exists_forall_abs_mul_sq_le hbrsq hbpsisq
  have hkey : moorePenrose K ⟨y, hy⟩ - spectralReg hs flt (hflt.exists_bound_on_spectrum
      hs) α y = hs.funCalc g hbg w := by
    have h2 : hs.funCalc g hbg w
        = hs.funCalc (fun lam => 1 - lam * flt α lam) hbrsq (hs.funCalc φ hbpsisq w) :=
      congrArg (fun T : E →L[𝕜] E => T w) (hs.funCalc_mul' hbrsq hbpsisq)
    rw [h2, show hs.funCalc φ hbpsisq w = moorePenrose K ⟨y, hy⟩ from hxw]
    exact hh1
  have hg0 : g 0 = 0 := by
    rw [hgdef]
    simp [hφ.map_zero]
  have hgval : ∀ i, |g (σ i ^ 2)| = φ (σ i ^ 2) * |1 - σ i ^ 2 * flt α (σ i ^ 2)| := by
    intro i
    rw [hgdef]
    simp only [Pi.mul_apply]
    rw [abs_mul, abs_of_nonneg (hφ.nonneg _ (hs.sq_mem_Icc i))]
    ring
  have hn := hs.norm_funCalc_le g ω (fun i => by rw [hgval i]; exact hωle i)
  rw [hg0, abs_zero, max_eq_left hω0] at hn
  rw [norm_sub_rev, hkey]
  calc ‖hs.funCalc g hbg w‖ ≤ ‖hs.funCalc g hbg‖ * ‖w‖ := (hs.funCalc g hbg).le_opNorm w
    _ ≤ ω * ρ := mul_le_mul hn hw (norm_nonneg w) hω0

end AutoIp

end _lem_general_omega
