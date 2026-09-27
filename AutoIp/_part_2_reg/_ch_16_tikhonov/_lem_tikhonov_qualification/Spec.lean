/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_qualification
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_standard_filters

section _lem_tikhonov_qualification

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Condition (F) for the Tikhonov filter with constant `C_F = 1`:
`sup_{λ ∈ (0,κ]} |φ_α(λ)| ≤ 1 · α⁻¹` for every `α > 0`.

It holds for every `K`, including `K = 0`, which the chapter excludes. -/
public theorem iSup_abs_tikhonovFilter_le (K : E →L[𝕜] F) :
    ∀ α : Set.Ioi (0 : ℝ),
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |tikhonovFilter α lam|) ≤ 1 * (α : ℝ)⁻¹ := by
  intro α
  have hα : (0 : ℝ) < (α : ℝ) := α.2
  have hc : (0 : ℝ) ≤ 1 * (α : ℝ)⁻¹ := by positivity
  refine Real.iSup_le (fun lam => Real.iSup_le (fun h => ?_) hc) hc
  have hs : (0 : ℝ) < lam + (α : ℝ) := by linarith [h.1]
  rw [tikhonovFilter_apply, abs_of_nonneg (inv_nonneg.mpr hs.le), one_mul]
  gcongr
  · linarith [h.1]

/-- Condition (Q_ν) for the Tikhonov filter with constant `C_ν = 1`, at every `ν ∈ (0,2]`:
`ω_ν(α) ≤ 1 · α^(ν/2)`.

The bound is stated for every `α > 0`, not only on `(0,κ]` as (Q_ν) asks, and for every `K`,
including `K = 0`. -/
public theorem iSup_rpow_mul_abs_one_sub_mul_tikhonovFilter_le (K : E →L[𝕜] F) {ν : ℝ}
    (hν : 0 < ν) (hν2 : ν ≤ 2) :
    ∀ α : Set.Ioi (0 : ℝ),
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
        lam ^ (ν / 2) * |1 - lam * tikhonovFilter α lam|) ≤ 1 * (α : ℝ) ^ (ν / 2) := by
  have hpt : ∀ (α : Set.Ioi (0 : ℝ)) (lam : ℝ), 0 < lam →
      lam ^ (ν / 2) * |1 - lam * tikhonovFilter α lam| ≤ 1 * (α : ℝ) ^ (ν / 2) := by
    intro α lam hlam
    have hα : (0 : ℝ) < (α : ℝ) := α.2
    set t := ν / 2 with ht
    have ht0 : 0 < t := by rw [ht]; linarith
    have ht1 : t ≤ 1 := by rw [ht]; linarith
    have hsum : (0 : ℝ) < lam + (α : ℝ) := by linarith
    have hyoung : lam ^ t * (α : ℝ) ^ (1 - t) ≤ t * lam + (1 - t) * (α : ℝ) :=
      Real.geom_mean_le_arith_mean2_weighted ht0.le (by linarith) hlam.le hα.le (by ring)
    have hle : lam ^ t * (α : ℝ) ^ (1 - t) ≤ lam + (α : ℝ) := by nlinarith [hyoung]
    have hα1 : (α : ℝ) ^ (1 - t) * (α : ℝ) ^ t = (α : ℝ) := by
      rw [← Real.rpow_add hα, show (1 - t) + t = (1 : ℝ) by ring, Real.rpow_one]
    have hptn : (0 : ℝ) ≤ (α : ℝ) ^ t := Real.rpow_nonneg hα.le t
    have hgoal : lam ^ t * (α : ℝ) ≤ (α : ℝ) ^ t * (lam + (α : ℝ)) := by
      calc lam ^ t * (α : ℝ) = (lam ^ t * (α : ℝ) ^ (1 - t)) * (α : ℝ) ^ t := by
            rw [mul_assoc, hα1]
        _ ≤ (lam + (α : ℝ)) * (α : ℝ) ^ t := mul_le_mul_of_nonneg_right hle hptn
        _ = (α : ℝ) ^ t * (lam + (α : ℝ)) := by ring
    rw [abs_one_sub_mul_tikhonovFilter hlam, one_mul, ← mul_div_assoc, div_le_iff₀ hsum]
    exact hgoal
  intro α
  have hα : (0 : ℝ) < (α : ℝ) := α.2
  have hc : (0 : ℝ) ≤ 1 * (α : ℝ) ^ (ν / 2) := by
    rw [one_mul]; exact Real.rpow_nonneg hα.le _
  exact Real.iSup_le (fun lam => Real.iSup_le (fun h => hpt α lam h.1) hc) hc

/-- Tikhonov has qualification `2`: it satisfies (F) with `C_F = 1`, (Q_ν) with `C_ν = 1` for
every `ν ∈ (0,2]`, and its qualification is `ν₀ = 2`.

(F) and (Q_ν) appear as their bounds alone, and (Q_ν) is stated for every `α > 0` rather than
only on `(0,κ]`. -/
public theorem tikhonov_qualification {K : E →L[𝕜] F} (hK : K ≠ 0) :
    (∀ α : Set.Ioi (0 : ℝ),
        (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |tikhonovFilter α lam|) ≤ 1 * (α : ℝ)⁻¹) ∧
      (∀ ν ∈ Set.Ioc (0 : ℝ) 2, ∀ α : Set.Ioi (0 : ℝ),
        (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
          lam ^ (ν / 2) * |1 - lam * tikhonovFilter α lam|) ≤ 1 * (α : ℝ) ^ (ν / 2)) ∧
      qualification K tikhonovFilter = (2 : ℝ≥0∞) := by
  have hKn : ‖K‖ ≠ 0 := norm_ne_zero_iff.mpr hK
  have hκ : (0 : ℝ) < ‖K‖ ^ 2 := by positivity
  have hres : ∀ (α : Set.Ioi (0 : ℝ)) (lam : ℝ), 0 < lam →
      |1 - lam * tikhonovFilter α lam| = (α : ℝ) / (lam + (α : ℝ)) :=
    fun _ _ hlam => abs_one_sub_mul_tikhonovFilter hlam
  refine ⟨iSup_abs_tikhonovFilter_le K,
    fun ν hν => iSup_rpow_mul_abs_one_sub_mul_tikhonovFilter_le K hν.1 hν.2, ?_⟩
  refine le_antisymm ?_ ?_
  · -- No `ν > 2` satisfies (Q_ν): evaluate `ω_ν` at `λ = κ` and let `α → 0⁺`.
    refine (qualification_le_iff K tikhonovFilter 2).2 fun ν hν => ?_
    obtain ⟨hν0, Cν, hCle⟩ := hν
    have hC0 : 0 < Cν := hCle.const_pos
    have hle2 : ν ≤ 2 := by
      by_contra hcon
      push Not at hcon
      set s := ν / 2 - 1 with hsdef
      have hs0 : 0 < s := by rw [hsdef]; linarith
      have hlow : ∀ a : ℝ, 0 < a → a ≤ ‖K‖ ^ 2 →
          (‖K‖ ^ 2) ^ (ν / 2) * (a / (‖K‖ ^ 2 + a)) ≤ Cν * a ^ (ν / 2) := by
        intro a ha haκ
        obtain ⟨α, rfl⟩ : ∃ α : Set.Ioi (0 : ℝ), (α : ℝ) = a := ⟨⟨a, Set.mem_Ioi.2 ha⟩, rfl⟩
        have hbd : ∀ lam : ℝ,
            (⨆ _ : lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
              lam ^ (ν / 2) * |1 - lam * tikhonovFilter α lam|)
              ≤ (‖K‖ ^ 2) ^ (ν / 2) := by
          intro lam
          refine Real.iSup_le (fun h => ?_) (Real.rpow_nonneg hκ.le _)
          rw [hres α lam h.1]
          have h1 : lam ^ (ν / 2) ≤ (‖K‖ ^ 2) ^ (ν / 2) :=
            Real.rpow_le_rpow h.1.le h.2 (by linarith)
          have h2 : (α : ℝ) / (lam + (α : ℝ)) ≤ 1 := by
            rw [div_le_one (by linarith [h.1])]; linarith [h.1]
          have h3 : (0 : ℝ) ≤ (α : ℝ) / (lam + (α : ℝ)) :=
            div_nonneg ha.le (by linarith [h.1] : (0 : ℝ) ≤ lam + (α : ℝ))
          nlinarith [Real.rpow_nonneg h.1.le (ν / 2)]
        have hbdd : BddAbove (Set.range (fun lam : ℝ =>
            (⨆ _ : lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
              lam ^ (ν / 2) * |1 - lam * tikhonovFilter α lam|))) := by
          refine ⟨(‖K‖ ^ 2) ^ (ν / 2), ?_⟩
          rintro _ ⟨lam, rfl⟩
          exact hbd lam
        have h1 := le_ciSup hbdd (‖K‖ ^ 2)
        rw [ciSup_pos (show (‖K‖ ^ 2) ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2) from ⟨hκ, le_rfl⟩),
          hres α _ hκ] at h1
        exact le_trans h1 (hCle.omega_le α haκ)
      set D := 2 * Cν * ‖K‖ ^ 2 / (‖K‖ ^ 2) ^ (ν / 2) with hDdef
      have hκp : (0 : ℝ) < (‖K‖ ^ 2) ^ (ν / 2) := Real.rpow_pos_of_pos hκ _
      have hD0 : 0 < D := by rw [hDdef]; positivity
      have hkey : ∀ α, 0 < α → α ≤ ‖K‖ ^ 2 → 1 ≤ D * α ^ s := by
        intro α hα hακ
        have h := hlow α hα hακ
        have hsum : (0 : ℝ) < ‖K‖ ^ 2 + α := by linarith
        have h2 : α / (2 * ‖K‖ ^ 2) ≤ α / (‖K‖ ^ 2 + α) := by
          apply div_le_div_of_nonneg_left hα.le hsum
          linarith
        have hαne : α ≠ 0 := hα.ne'
        have hexp : α * α ^ s = α ^ (ν / 2) := by
          rw [hsdef, Real.rpow_sub hα, Real.rpow_one]
          field_simp
        have h3 : (‖K‖ ^ 2) ^ (ν / 2) * (α / (2 * ‖K‖ ^ 2)) ≤ Cν * (α * α ^ s) := by
          rw [hexp]
          nlinarith [h, h2, hκp]
        have hαs : (0 : ℝ) < α ^ s := Real.rpow_pos_of_pos hα _
        have h4 : (‖K‖ ^ 2) ^ (ν / 2) * α ≤ Cν * (α * α ^ s) * (2 * ‖K‖ ^ 2) := by
          rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ‖K‖ ^ 2)] at h3
          exact h3
        rw [hDdef, div_mul_eq_mul_div, le_div_iff₀ hκp]
        nlinarith [h4, hα, hκ]
      -- but `α ^ s → 0` as `α → 0⁺`, so `1 ≤ D α^s` cannot hold for all small `α`
      set c : ℝ := ((2 * D)⁻¹) ^ (1 / s) with hcdef
      have hc0 : 0 < c := Real.rpow_pos_of_pos (by positivity) _
      set α := min (‖K‖ ^ 2) c with hαdef
      have hα0 : 0 < α := lt_min hκ hc0
      have hακ : α ≤ ‖K‖ ^ 2 := min_le_left _ _
      have hαc : α ≤ c := min_le_right _ _
      have hcs : c ^ s = (2 * D)⁻¹ := by
        rw [hcdef, ← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hs0.ne',
          Real.rpow_one]
      have hαs : α ^ s ≤ (2 * D)⁻¹ := by
        rw [← hcs]; exact Real.rpow_le_rpow hα0.le hαc hs0.le
      have hfin := hkey α hα0 hακ
      have hD2 : D * (2 * D)⁻¹ = 1 / 2 := by field_simp
      nlinarith [hfin, hαs, hD0]
    calc ENNReal.ofReal ν ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hle2
      _ = 2 := by simp
  · -- `ν = 2` is admissible, with `C_ν = 1`.
    calc (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by simp
      _ ≤ _ := le_qualification K tikhonovFilter two_pos
          ⟨1, ⟨1, tikhonovFilter_isRegularizingFilter K⟩, one_pos, fun α _ =>
            iSup_rpow_mul_abs_one_sub_mul_tikhonovFilter_le K two_pos le_rfl α⟩

/-- The qualification of the Tikhonov filter is `ν₀ = 2`. -/
public
theorem qualification_tikhonovFilter {K : E →L[𝕜] F} (hK : K ≠ 0) :
    qualification K tikhonovFilter = (2 : ℝ≥0∞) :=
  (tikhonov_qualification hK).2.2

end AutoIp

end _lem_tikhonov_qualification
