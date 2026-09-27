module

import AutoIp._part_2_reg._ch_15_spectral_regularization._thm_hanke_raus_conditional.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.norm_spectralReg_sub_moorePenrose_le_hankeRaus` can hold together. -/
theorem AutoIp.norm_spectralReg_sub_moorePenrose_le_hankeRaus_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (φ : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (Cφ : ℝ), ∃ (ν : ℝ), (IsSingularSystem K σ v u) ∧ (AutoIp.IsRegularizingFilter K φ Cφ) ∧ (∃ CF > (0 : ℝ), AutoIp.HasFilterBound K φ CF) ∧ (∃ Cν > (0 : ℝ),
  ∀ (α : (↑(Set.Ioi (0 : ℝ)) : Type)),
    ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), lam ^ ((ν + (1 : ℝ)) / (2 : ℝ)) * |(1 : ℝ) - lam * φ α lam| ≤
      Cν * (↑α : ℝ) ^ ((ν + (1 : ℝ)) / (2 : ℝ))) ∧ ((0 : ℝ) < ν) :=
  by
  classical
  have hone : IsSingularSystem (ι := Unit) (1 : ℝ →L[ℝ] ℝ)
      (fun _ => 1) (fun _ => 1) (fun _ => 1) :=
    { pos := fun _ => one_pos
      orthonormal_left := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      orthonormal_right := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      span_left := Witnesses.Identity.span_left _ fun _ => rfl
      span_right := Witnesses.Identity.span_right _ fun _ => rfl
      map_left := fun _ => (one_mul (1 : ℝ)).symm
      map_right := fun _ =>
        (Witnesses.Identity.adjoint_one_apply 1).trans (one_mul (1 : ℝ)).symm }
  set φ : Set.Ioi (0 : ℝ) → ℝ → ℝ := fun α lam => (max (α : ℝ) lam)⁻¹ with hφdef
  have hφa : ∀ (α : Set.Ioi (0 : ℝ)) (lam : ℝ), φ α lam = (max (α : ℝ) lam)⁻¹ :=
    fun _ _ => rfl
  have hmax : ∀ (α : Set.Ioi (0 : ℝ)) (lam : ℝ), 0 < max (α : ℝ) lam := fun α lam =>
    lt_max_of_lt_left α.2
  have habs : ∀ (α : Set.Ioi (0 : ℝ)) (lam : ℝ), |φ α lam| ≤ (α : ℝ)⁻¹ := fun α lam => by
    rw [hφa, abs_of_pos (inv_pos.2 (hmax α lam))]
    exact inv_anti₀ α.2 (le_max_left _ _)
  have hres : ∀ (α : Set.Ioi (0 : ℝ)) (lam : ℝ), 0 < lam →
      |1 - lam * φ α lam| ≤ 1 ∧ ((α : ℝ) ≤ lam → 1 - lam * φ α lam = 0) := by
    intro α lam hlam
    have hm := hmax α lam
    have hle : lam * φ α lam ≤ 1 := by
      rw [hφa, ← div_eq_mul_inv, div_le_one hm]; exact le_max_right _ _
    have hnn : 0 ≤ lam * φ α lam := mul_nonneg hlam.le (inv_nonneg.2 hm.le)
    refine ⟨by rw [abs_le]; constructor <;> linarith, fun h => ?_⟩
    rw [hφa, max_eq_right h, mul_inv_cancel₀ hlam.ne', sub_self]
  have hflt : AutoIp.IsRegularizingFilter (1 : ℝ →L[ℝ] ℝ) φ 1 :=
    { const_pos := one_pos
      bddOn := fun α => ⟨(α : ℝ)⁻¹, fun t _ => habs α t⟩
      tendsto_inv := by
        intro lam hlam
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_le_atBot (⟨lam, hlam.1⟩ : Set.Ioi (0 : ℝ))] with α hα
        have hα' : (α : ℝ) ≤ lam := hα
        rw [hφa, max_eq_right hα']
      mul_abs_le := by
        intro α lam hlam
        rw [abs_of_pos (inv_pos.2 (hmax α lam)), ← div_eq_mul_inv, div_le_one (hmax α lam)]
        exact le_max_right _ _ }
  have hfb : AutoIp.HasFilterBound (1 : ℝ →L[ℝ] ℝ) φ 1 :=
    ⟨⟨1, hflt⟩, one_pos, fun α => by
      rw [one_mul]
      exact Real.iSup_le (fun lam => Real.iSup_le (fun _ => habs α lam)
        (inv_nonneg.2 (le_of_lt α.2))) (inv_nonneg.2 (le_of_lt α.2))⟩
  have hqual : ∀ ν : ℝ, 0 < ν → ∀ α : Set.Ioi (0 : ℝ),
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ)),
        lam ^ (ν / (2 : ℝ)) * |(1 : ℝ) - lam * φ α lam|) ≤ 1 * (α : ℝ) ^ (ν / (2 : ℝ)) := by
    intro ν hν α
    have h0 : 0 ≤ (α : ℝ) ^ (ν / (2 : ℝ)) := Real.rpow_nonneg (le_of_lt α.2) _
    rw [one_mul]
    refine Real.iSup_le (fun lam => Real.iSup_le (fun hlam => ?_) h0) h0
    obtain ⟨h1, h2⟩ := hres α lam hlam.1
    rcases le_or_gt (α : ℝ) lam with h | h
    · rw [h2 h, abs_zero, mul_zero]; exact h0
    · have hp : lam ^ (ν / (2 : ℝ)) ≤ (α : ℝ) ^ (ν / (2 : ℝ)) :=
        Real.rpow_le_rpow hlam.1.le h.le (by positivity)
      have hp0 : 0 ≤ lam ^ (ν / (2 : ℝ)) := Real.rpow_nonneg hlam.1.le _
      calc lam ^ (ν / (2 : ℝ)) * |(1 : ℝ) - lam * φ α lam| ≤ lam ^ (ν / (2 : ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left h1 hp0
        _ ≤ (α : ℝ) ^ (ν / (2 : ℝ)) := by rw [mul_one]; exact hp
  have hsupres : (⨆ (a : Set.Ioi (0 : ℝ)), ⨆ lam ∈ Set.Ioc (0 : ℝ)
      (‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ)), |(1 : ℝ) - lam * φ a lam|) < 2 := by
    have h : (⨆ (a : Set.Ioi (0 : ℝ)), ⨆ lam ∈ Set.Ioc (0 : ℝ)
        (‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ)), |(1 : ℝ) - lam * φ a lam|) ≤ 1 :=
      Real.iSup_le (fun a => Real.iSup_le (fun lam => Real.iSup_le
        (fun hlam => (hres a lam hlam.1).1) zero_le_one) zero_le_one) zero_le_one
    linarith
  exact ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1, φ, 1, 1,
    hone, hflt, ⟨1, one_pos, hfb⟩, ⟨1, one_pos, hqual (1 + 1) (by norm_num)⟩, one_pos⟩

/-- The hypotheses of `AutoIp.norm_spectralReg_sub_moorePenrose_le_hankeRaus` can fail. -/
theorem AutoIp.norm_spectralReg_sub_moorePenrose_le_hankeRaus_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (φ : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (Cφ : ℝ), ∃ (ν : ℝ), ¬ ((IsSingularSystem K σ v u) ∧ (AutoIp.IsRegularizingFilter K φ Cφ) ∧ (∃ CF > (0 : ℝ), AutoIp.HasFilterBound K φ CF) ∧ (∃ Cν > (0 : ℝ),
  ∀ (α : (↑(Set.Ioi (0 : ℝ)) : Type)),
    ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), lam ^ ((ν + (1 : ℝ)) / (2 : ℝ)) * |(1 : ℝ) - lam * φ α lam| ≤
      Cν * (↑α : ℝ) ^ ((ν + (1 : ℝ)) / (2 : ℝ))) ∧ ((0 : ℝ) < ν)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, fun _ _ => 0, 1, 1
    , ?_⟩
  rintro ⟨H, _, _, _, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)
