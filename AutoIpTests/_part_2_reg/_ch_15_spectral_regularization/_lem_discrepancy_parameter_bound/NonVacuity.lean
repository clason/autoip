module

import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_discrepancy_parameter_bound.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity
import AutoIpTests.Witnesses.Zero

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.discrepancy_param_ge` can hold together. -/
theorem AutoIp.discrepancy_param_ge_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (φ : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (Cφ : ℝ), ∃ (hφ : AutoIp.IsRegularizingFilter K φ Cφ), ∃ (ν₀ : ℝ), ∃ (τ : ℝ), ∃ (a : AutoIp.ParameterChoice F), ∃ (ν : ℝ), (K ≠ (0 : E →L[𝕜] F)) ∧ (∀ ν ∈ Set.Ioc (0 : ℝ) ν₀,
  ∃ Cν > (0 : ℝ),
    ∀ (α : (↑(Set.Ioi (0 : ℝ)) : Type)),
      ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), lam ^ (ν / (2 : ℝ)) * |(1 : ℝ) - lam * φ α lam| ≤
        Cν * (↑α : ℝ) ^ (ν / (2 : ℝ))) ∧ (⨆ (a : (↑(Set.Ioi (0 : ℝ)) : Type)), ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |(1 : ℝ) - lam * φ a lam| < τ) ∧ (AutoIp.IsDiscrepancyPrinciple K (AutoIp.spectralReg hs φ (AutoIp.IsRegularizingFilter.exists_bound_on_spectrum hs hφ)) τ
  a) ∧ (ν ∈ Set.Ioc (0 : ℝ) (ν₀ - (1 : ℝ))) :=
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
  have hR : ∀ (α : Set.Ioi (0 : ℝ)) (z : ℝ),
      AutoIp.spectralReg hone φ (AutoIp.IsRegularizingFilter.exists_bound_on_spectrum hone hflt)
        α z = (max (α : ℝ) 1)⁻¹ * z := by
    intro α z
    have hsum := AutoIp.hasSum_spectralReg hone φ
      (AutoIp.IsRegularizingFilter.exists_bound_on_spectrum hone hflt) α z
    rw [hsum.unique (hasSum_fintype _)]
    simp [hφa]
  -- the discrepancy principle for `τ = 2`: the residual `(1 - (max α 1)⁻¹) |z|` crosses
  -- `2 δ` at `α = |z| / (|z| - 2 δ)`
  let a : AutoIp.ParameterChoice ℝ :=
    ⟨fun δ z => if 2 * (δ : ℝ) < |z| then |z| / (|z| - 2 * (δ : ℝ)) else 1, fun δ z => by
      split_ifs with h
      · exact div_pos (lt_trans (by have h0 : (0 : ℝ) < δ := δ.2; linarith) h) (by linarith)
      · exact one_pos⟩
  have hdp : AutoIp.IsDiscrepancyPrinciple (1 : ℝ →L[ℝ] ℝ)
      (AutoIp.spectralReg hone φ (AutoIp.IsRegularizingFilter.exists_bound_on_spectrum hone hflt))
      2 a := by
    refine ⟨by norm_num, fun δ hδ z hz => ?_⟩
    have hz' : 2 * δ < |z| := by rwa [Real.norm_eq_abs] at hz
    have hzpos : 0 < |z| := lt_trans (by linarith) hz'
    have hd : 0 < |z| - 2 * δ := by linarith
    have ha : a ⟨δ, hδ⟩ z = |z| / (|z| - 2 * δ) := by
      show (if 2 * δ < |z| then |z| / (|z| - 2 * δ) else 1) = _
      simp [hz']
    have ha1 : 1 ≤ |z| / (|z| - 2 * δ) := by
      rw [le_div_iff₀ hd]; linarith
    have hres : ∀ α : Set.Ioi (0 : ℝ), 1 ≤ (α : ℝ) →
        ‖(1 : ℝ →L[ℝ] ℝ) (AutoIp.spectralReg hone φ
          (AutoIp.IsRegularizingFilter.exists_bound_on_spectrum hone hflt) α z) - z‖ =
          (1 - (α : ℝ)⁻¹) * |z| := by
      intro α hα
      rw [one_apply_eq_self, hR, max_eq_left hα, Real.norm_eq_abs]
      have h1 : (α : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hα
      rw [show (α : ℝ)⁻¹ * z - z = -((1 - (α : ℝ)⁻¹) * z) by ring, abs_neg, abs_mul,
        abs_of_nonneg (by linarith)]
    constructor
    · have hp : ((a.param ⟨δ, hδ⟩ z : Set.Ioi (0 : ℝ)) : ℝ) = |z| / (|z| - 2 * δ) := ha
      rw [hres _ (hp ▸ ha1), hp, inv_div]
      have : (1 - (|z| - 2 * δ) / |z|) * |z| = 2 * δ := by field_simp; ring
      rw [this]
    · intro α hα
      rw [ha] at hα
      have hα1 : 1 ≤ (α : ℝ) := le_trans ha1 hα.le
      rw [hres α hα1]
      have hαpos : (0 : ℝ) < α := α.2
      have key : (1 - (|z| / (|z| - 2 * δ))⁻¹) * |z| = 2 * δ := by
        rw [inv_div]; field_simp; ring
      have hlt : (|z| / (|z| - 2 * δ))⁻¹ > (α : ℝ)⁻¹ :=
        inv_strictAnti₀ (lt_of_lt_of_le one_pos ha1) hα
      nlinarith
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1, hone, φ, 1, hflt,
    3, 2, a, 1, Witnesses.Identity.one_ne_zero', fun ν hν => ⟨1, one_pos, hqual ν hν.1⟩,
    hsupres, hdp, by norm_num⟩

/-- The hypotheses of `AutoIp.discrepancy_param_ge` can fail. -/
theorem AutoIp.discrepancy_param_ge_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (φ : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (Cφ : ℝ), ∃ (hφ : AutoIp.IsRegularizingFilter K φ Cφ), ∃ (ν₀ : ℝ), ∃ (τ : ℝ), ∃ (a : AutoIp.ParameterChoice F), ∃ (ν : ℝ), ¬ ((K ≠ (0 : E →L[𝕜] F)) ∧ (∀ ν ∈ Set.Ioc (0 : ℝ) ν₀,
  ∃ Cν > (0 : ℝ),
    ∀ (α : (↑(Set.Ioi (0 : ℝ)) : Type)),
      ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), lam ^ (ν / (2 : ℝ)) * |(1 : ℝ) - lam * φ α lam| ≤
        Cν * (↑α : ℝ) ^ (ν / (2 : ℝ))) ∧ (⨆ (a : (↑(Set.Ioi (0 : ℝ)) : Type)), ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |(1 : ℝ) - lam * φ a lam| < τ) ∧ (AutoIp.IsDiscrepancyPrinciple K (AutoIp.spectralReg hs φ (AutoIp.IsRegularizingFilter.exists_bound_on_spectrum hs hφ)) τ
  a) ∧ (ν ∈ Set.Ioc (0 : ℝ) (ν₀ - (1 : ℝ)))) :=
  by
  classical
  have hss : IsSingularSystem (ι := Empty) (0 : ℝ →L[ℝ] ℝ)
      (fun _ => 0) (fun _ => 0) (fun _ => 0) :=
    { pos := fun i => i.elim
      orthonormal_left := ⟨fun i => i.elim, fun {i _} _ => i.elim⟩
      orthonormal_right := ⟨fun i => i.elim, fun {i _} _ => i.elim⟩
      span_left := Witnesses.Zero.span_left _
      span_right := Witnesses.Zero.span_right _
      map_left := fun i => i.elim
      map_right := fun i => i.elim }
  have hflt : AutoIp.IsRegularizingFilter (0 : ℝ →L[ℝ] ℝ) (fun _ _ => 0) 1 :=
    ⟨one_pos, fun _ => ⟨0, fun t _ => by simp⟩,
      fun lam hlam => absurd hlam (by simp),
      fun _ lam hlam => absurd hlam (by simp)⟩
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Empty, fun _ => 0, fun _ => 0, fun _ => 0, hss,
    fun _ _ => 0, 1, hflt, 1, 2, ⟨fun _ _ => 1, fun _ _ => one_pos⟩, 0, ?_⟩
  rintro ⟨-, -, -, -, h, -⟩
  exact lt_irrefl 0 h
