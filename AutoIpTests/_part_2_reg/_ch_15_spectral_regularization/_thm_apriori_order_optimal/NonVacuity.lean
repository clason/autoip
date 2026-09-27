module

import AutoIp._part_2_reg._ch_15_spectral_regularization._thm_apriori_order_optimal.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.norm_spectralReg_sub_moorePenrose_le_apriori` can hold together. -/
theorem AutoIp.norm_spectralReg_sub_moorePenrose_le_apriori_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (φ : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (Cφ : ℝ), ∃ (ν : ℝ), ∃ (ρ : ℝ), ∃ (CF : ℝ), ∃ (Cν : ℝ), ∃ (cl : ℝ), ∃ (cu : ℝ), ∃ (hν : (0 : ℝ) < ν), ∃ (hρ : (0 : ℝ) < ρ), ∃ (a : AutoIp.ParameterChoice F), ∃ (y : F), ∃ (hy : y ∈ AutoIp.mpDomain K), ∃ (δ : ℝ), ∃ (z : F), (AutoIp.IsRegularizingFilter K φ Cφ) ∧ (AutoIp.HasFilterBound K φ CF) ∧ (∀ (α : (↑(Set.Ioi (0 : ℝ)) : Type)),
  ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), lam ^ (ν / (2 : ℝ)) * |(1 : ℝ) - lam * φ α lam| ≤
    Cν * (↑α : ℝ) ^ (ν / (2 : ℝ))) ∧ ((0 : ℝ) < cl) ∧ ((0 : ℝ) < cu) ∧ (∀ (δ : (↑(Set.Ioi (0 : ℝ)) : Type)) (z : F),
  cl * ((↑δ : ℝ) / ρ) ^ ((2 : ℝ) / (ν + (1 : ℝ))) ≤ (a : (↑(Set.Ioi (0 : ℝ)) : Type) → F → ℝ) δ z ∧
    (a : (↑(Set.Ioi (0 : ℝ)) : Type) → F → ℝ) δ z ≤ cu * ((↑δ : ℝ) / ρ) ^ ((2 : ℝ) / (ν + (1 : ℝ)))) ∧ ((↑(AutoIp.moorePenrose K) : ↥(LinearPMap.domain (AutoIp.moorePenrose K)) → E) ⟨y, hy⟩ ∈ AutoIp.sourceSet hs ν hν ρ hρ) ∧ ((0 : ℝ) < δ) ∧ (‖y - z‖ ≤ δ) :=
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
  have hres : ∀ (α : Set.Ioi (0 : ℝ)) (lam : ℝ), 0 < lam →
      |1 - lam * φ α lam| ≤ 1 ∧ ((α : ℝ) ≤ lam → 1 - lam * φ α lam = 0) := by
    intro α lam hlam
    have hm := hmax α lam
    have hle : lam * φ α lam ≤ 1 := by
      rw [hφa, ← div_eq_mul_inv, div_le_one hm]; exact le_max_right _ _
    have hnn : 0 ≤ lam * φ α lam := mul_nonneg hlam.le (inv_nonneg.2 hm.le)
    refine ⟨by rw [abs_le]; constructor <;> linarith, fun h => ?_⟩
    rw [hφa, max_eq_right h, mul_inv_cancel₀ hlam.ne', sub_self]
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
  -- the a-priori rule `α(δ) = (δ/ρ)^{2/(ν+1)}` with `ν = ρ = 1`
  let a : AutoIp.ParameterChoice ℝ :=
    ⟨fun δ _ => ((δ : ℝ) / 1) ^ ((2 : ℝ) / (1 + 1)),
      fun δ _ => Real.rpow_pos_of_pos (div_pos δ.2 one_pos) _⟩
  have ha : ∀ (δ : Set.Ioi (0 : ℝ)) (z : ℝ),
      1 * ((δ : ℝ) / 1) ^ ((2 : ℝ) / (1 + 1)) ≤ a δ z ∧
        a δ z ≤ 1 * ((δ : ℝ) / 1) ^ ((2 : ℝ) / (1 + 1)) := fun δ z => by
    rw [one_mul]; exact ⟨le_rfl, le_rfl⟩
  have hdom : ∀ y : ℝ, y ∈ AutoIp.mpDomain (1 : ℝ →L[ℝ] ℝ) := fun y =>
    Submodule.mem_sup_left (LinearMap.mem_range.2 ⟨y, rfl⟩)
  have hmp : ∀ (y : ℝ) (hy : y ∈ AutoIp.mpDomain (1 : ℝ →L[ℝ] ℝ)),
      AutoIp.moorePenrose (1 : ℝ →L[ℝ] ℝ) ⟨y, hy⟩ = y := by
    intro y hy
    have heq := (AutoIp.moorePenrose_isMinimumNorm ⟨y, hy⟩).isLeastSquares y
    simp only [ContinuousLinearMap.one_apply, sub_self, norm_zero] at heq
    exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm heq (norm_nonneg _)))
  have habs1 : ∀ (ν : ℝ) (hν : 0 ≤ ν), hone.absRpow ν hν 1 = 1 := by
    intro ν hν
    have hb : ∃ C, ∀ i : Unit, |(fun t : ℝ => t ^ (ν / 2)) ((1 : ℝ) ^ 2)| ≤ C :=
      ⟨1, fun _ => by simp⟩
    rw [hone.absRpow_def ν hν hb]
    have h := hone.funCalc_apply_v (φ := fun t : ℝ => t ^ (ν / 2)) hb ()
    simpa using h
  have hsrc : ∀ (ν : ℝ) (hν : 0 < ν),
      (1 : ℝ) ∈ AutoIp.sourceSet hone ν hν 1 one_pos :=
    fun ν hν => (AutoIp.mem_sourceSet_iff _ _ _ _ _).2 ⟨1, by rw [norm_one], habs1 ν hν.le⟩
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1, hone,
    φ, 1, 1, 1, 1, 1, 1, 1, one_pos, one_pos, a, 1, hdom 1, 1, 1,
    hflt, hfb, hqual 1 one_pos, one_pos, one_pos, ha, ?_, one_pos, ?_⟩
  · rw [hmp]
    exact hsrc 1 one_pos
  · rw [sub_self, norm_zero]
    exact zero_le_one

/-- The hypotheses of `AutoIp.norm_spectralReg_sub_moorePenrose_le_apriori` can fail. -/
theorem AutoIp.norm_spectralReg_sub_moorePenrose_le_apriori_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (φ : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (Cφ : ℝ), ∃ (ν : ℝ), ∃ (ρ : ℝ), ∃ (CF : ℝ), ∃ (Cν : ℝ), ∃ (cl : ℝ), ∃ (cu : ℝ), ∃ (hν : (0 : ℝ) < ν), ∃ (hρ : (0 : ℝ) < ρ), ∃ (a : AutoIp.ParameterChoice F), ∃ (y : F), ∃ (hy : y ∈ AutoIp.mpDomain K), ∃ (δ : ℝ), ∃ (z : F), ¬ ((AutoIp.IsRegularizingFilter K φ Cφ) ∧ (AutoIp.HasFilterBound K φ CF) ∧ (∀ (α : (↑(Set.Ioi (0 : ℝ)) : Type)),
  ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), lam ^ (ν / (2 : ℝ)) * |(1 : ℝ) - lam * φ α lam| ≤
    Cν * (↑α : ℝ) ^ (ν / (2 : ℝ))) ∧ ((0 : ℝ) < cl) ∧ ((0 : ℝ) < cu) ∧ (∀ (δ : (↑(Set.Ioi (0 : ℝ)) : Type)) (z : F),
  cl * ((↑δ : ℝ) / ρ) ^ ((2 : ℝ) / (ν + (1 : ℝ))) ≤ (a : (↑(Set.Ioi (0 : ℝ)) : Type) → F → ℝ) δ z ∧
    (a : (↑(Set.Ioi (0 : ℝ)) : Type) → F → ℝ) δ z ≤ cu * ((↑δ : ℝ) / ρ) ^ ((2 : ℝ) / (ν + (1 : ℝ)))) ∧ ((↑(AutoIp.moorePenrose K) : ↥(LinearPMap.domain (AutoIp.moorePenrose K)) → E) ⟨y, hy⟩ ∈ AutoIp.sourceSet hs ν hν ρ hρ) ∧ ((0 : ℝ) < δ) ∧ (‖y - z‖ ≤ δ)) :=
  by
  classical
  have hsub : ∀ p q : Submodule ℝ Unit, p = q := fun p q => Subsingleton.elim p q
  have hss : IsSingularSystem (ι := Empty) (0 : Unit →L[ℝ] Unit)
      (fun _ => 0) (fun _ => ()) (fun _ => ()) :=
    { pos := fun i => i.elim
      orthonormal_left := ⟨fun i => i.elim, fun {i _} _ => i.elim⟩
      orthonormal_right := ⟨fun i => i.elim, fun {i _} _ => i.elim⟩
      span_left := hsub _ _
      span_right := hsub _ _
      map_left := fun i => i.elim
      map_right := fun i => i.elim }
  have hI : Set.Ioc (0 : ℝ) (‖(0 : Unit →L[ℝ] Unit)‖ ^ (2 : ℕ)) = ∅ := by
    rw [norm_zero]; simp
  have hflt : AutoIp.IsRegularizingFilter (0 : Unit →L[ℝ] Unit) (fun _ _ => 0) 1 :=
    ⟨one_pos, fun _ => ⟨0, fun t _ => by simp⟩,
      fun lam hlam => by rw [hI] at hlam; exact hlam.elim,
      fun _ lam hlam => by rw [hI] at hlam; exact hlam.elim⟩
  have hsup : ∀ f : ℝ → ℝ, (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖(0 : Unit →L[ℝ] Unit)‖ ^ (2 : ℕ)),
      f lam) = 0 := by
    intro f
    rw [hI]
    simp
  have hfb : AutoIp.HasFilterBound (0 : Unit →L[ℝ] Unit) (fun _ _ => 0) 1 :=
    ⟨⟨1, hflt⟩, one_pos, fun α => by
      rw [hsup]
      exact mul_nonneg zero_le_one (inv_nonneg.2 (le_of_lt α.2))⟩
  let a : AutoIp.ParameterChoice Unit :=
    ⟨fun δ _ => ((δ : ℝ) / 1) ^ ((2 : ℝ) / (1 + 1)),
      fun δ _ => Real.rpow_pos_of_pos (div_pos δ.2 one_pos) _⟩
  have ha : ∀ (δ : Set.Ioi (0 : ℝ)) (z : Unit),
      1 * ((δ : ℝ) / 1) ^ ((2 : ℝ) / (1 + 1)) ≤ a δ z ∧
        a δ z ≤ 1 * ((δ : ℝ) / 1) ^ ((2 : ℝ) / (1 + 1)) := fun δ z => by
    rw [one_mul]; exact ⟨le_rfl, le_rfl⟩
  have hqual : ∀ α : Set.Ioi (0 : ℝ), (⨆ lam ∈ Set.Ioc (0 : ℝ)
      (‖(0 : Unit →L[ℝ] Unit)‖ ^ (2 : ℕ)), lam ^ ((1 : ℝ) / (2 : ℝ)) *
        |(1 : ℝ) - lam * (fun _ _ => (0 : ℝ)) α lam|) ≤ 1 * (α : ℝ) ^ ((1 : ℝ) / (2 : ℝ)) :=
    fun α => by
      rw [hsup, one_mul]
      exact Real.rpow_nonneg (le_of_lt α.2) _
  have hy : (() : Unit) ∈ AutoIp.mpDomain (0 : Unit →L[ℝ] Unit) := by
    rw [Subsingleton.elim () 0]; exact Submodule.zero_mem _
  have hsrc : ∀ x : Unit, x ∈ AutoIp.sourceSet hss 1 one_pos 1 one_pos := fun x =>
    (AutoIp.mem_sourceSet_iff _ _ _ _ _).2 ⟨0, by rw [norm_zero]; exact zero_le_one,
      Subsingleton.elim _ _⟩
  refine ⟨ℝ, inferInstance, Unit, Unit, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, 0, Empty, fun _ => 0, fun _ => (),
    fun _ => (), hss, fun _ _ => 0, 1, 1, 1, 1, 1, 1, 1, one_pos, one_pos, a, (), hy, 0, (), ?_⟩
  rintro ⟨-, -, -, -, -, -, -, h, -⟩
  exact lt_irrefl 0 h

/-- The hypotheses of `AutoIp.isRegularizationMethod_apriori` can hold together. -/
theorem AutoIp.isRegularizationMethod_apriori_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (φ : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (Cφ : ℝ), ∃ (hφ : AutoIp.IsRegularizingFilter K φ Cφ), ∃ (ν : ℝ), ∃ (ρ : ℝ), ∃ (CF : ℝ), ∃ (cl : ℝ), ∃ (cu : ℝ), ∃ (a : AutoIp.ParameterChoice F), (AutoIp.IsRegularization K (AutoIp.spectralReg hs φ (AutoIp.IsRegularizingFilter.exists_bound_on_spectrum hs hφ))) ∧ ((0 : ℝ) < ν) ∧ ((0 : ℝ) < ρ) ∧ (AutoIp.HasFilterBound K φ CF) ∧ (AutoIp.ParameterChoice.IsAPriori a) ∧ ((0 : ℝ) < cl) ∧ (∀ (δ : (↑(Set.Ioi (0 : ℝ)) : Type)) (z : F),
  cl * ((↑δ : ℝ) / ρ) ^ ((2 : ℝ) / (ν + (1 : ℝ))) ≤ (a : (↑(Set.Ioi (0 : ℝ)) : Type) → F → ℝ) δ z ∧
    (a : (↑(Set.Ioi (0 : ℝ)) : Type) → F → ℝ) δ z ≤ cu * ((↑δ : ℝ) / ρ) ^ ((2 : ℝ) / (ν + (1 : ℝ)))) :=
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
  have hres : ∀ (α : Set.Ioi (0 : ℝ)) (lam : ℝ), 0 < lam →
      |1 - lam * φ α lam| ≤ 1 ∧ ((α : ℝ) ≤ lam → 1 - lam * φ α lam = 0) := by
    intro α lam hlam
    have hm := hmax α lam
    have hle : lam * φ α lam ≤ 1 := by
      rw [hφa, ← div_eq_mul_inv, div_le_one hm]; exact le_max_right _ _
    have hnn : 0 ≤ lam * φ α lam := mul_nonneg hlam.le (inv_nonneg.2 hm.le)
    refine ⟨by rw [abs_le]; constructor <;> linarith, fun h => ?_⟩
    rw [hφa, max_eq_right h, mul_inv_cancel₀ hlam.ne', sub_self]
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
  -- the a-priori rule `α(δ) = (δ/ρ)^{2/(ν+1)}` with `ν = ρ = 1`
  let a : AutoIp.ParameterChoice ℝ :=
    ⟨fun δ _ => ((δ : ℝ) / 1) ^ ((2 : ℝ) / (1 + 1)),
      fun δ _ => Real.rpow_pos_of_pos (div_pos δ.2 one_pos) _⟩
  have ha : ∀ (δ : Set.Ioi (0 : ℝ)) (z : ℝ),
      1 * ((δ : ℝ) / 1) ^ ((2 : ℝ) / (1 + 1)) ≤ a δ z ∧
        a δ z ≤ 1 * ((δ : ℝ) / 1) ^ ((2 : ℝ) / (1 + 1)) := fun δ z => by
    rw [one_mul]; exact ⟨le_rfl, le_rfl⟩
  have hdom : ∀ y : ℝ, y ∈ AutoIp.mpDomain (1 : ℝ →L[ℝ] ℝ) := fun y =>
    Submodule.mem_sup_left (LinearMap.mem_range.2 ⟨y, rfl⟩)
  have hmp : ∀ (y : ℝ) (hy : y ∈ AutoIp.mpDomain (1 : ℝ →L[ℝ] ℝ)),
      AutoIp.moorePenrose (1 : ℝ →L[ℝ] ℝ) ⟨y, hy⟩ = y := by
    intro y hy
    have heq := (AutoIp.moorePenrose_isMinimumNorm ⟨y, hy⟩).isLeastSquares y
    simp only [ContinuousLinearMap.one_apply, sub_self, norm_zero] at heq
    exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm heq (norm_nonneg _)))
  have habs1 : ∀ (ν : ℝ) (hν : 0 ≤ ν), hone.absRpow ν hν 1 = 1 := by
    intro ν hν
    have hb : ∃ C, ∀ i : Unit, |(fun t : ℝ => t ^ (ν / 2)) ((1 : ℝ) ^ 2)| ≤ C :=
      ⟨1, fun _ => by simp⟩
    rw [hone.absRpow_def ν hν hb]
    have h := hone.funCalc_apply_v (φ := fun t : ℝ => t ^ (ν / 2)) hb ()
    simpa using h
  have hsrc : ∀ (ν : ℝ) (hν : 0 < ν),
      (1 : ℝ) ∈ AutoIp.sourceSet hone ν hν 1 one_pos :=
    fun ν hν => (AutoIp.mem_sourceSet_iff _ _ _ _ _).2 ⟨1, by rw [norm_one], habs1 ν hν.le⟩
  have hreg : AutoIp.IsRegularization (1 : ℝ →L[ℝ] ℝ) (AutoIp.spectralReg hone φ
      (AutoIp.IsRegularizingFilter.exists_bound_on_spectrum hone hflt)) := by
    intro y hy
    rw [hmp]
    have hR : ∀ α : Set.Ioi (0 : ℝ), AutoIp.spectralReg hone φ
        (AutoIp.IsRegularizingFilter.exists_bound_on_spectrum hone hflt) α y = φ α 1 * y := by
      intro α
      have h := AutoIp.hasSum_spectralReg hone φ
        (AutoIp.IsRegularizingFilter.exists_bound_on_spectrum hone hflt) α y
      rw [h.unique (hasSum_fintype _)]
      simp
    simp only [hR]
    have h1 : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) (‖(1 : ℝ →L[ℝ] ℝ)‖ ^ 2) := by
      rw [Witnesses.Identity.norm_one']; norm_num
    simpa using (hflt.tendsto_inv 1 h1).mul_const y
  exact ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1, hone,
    φ, 1, hflt, 1, 1, 1, 1, 1, a, hreg, one_pos, one_pos, hfb, fun _ _ _ => rfl, one_pos, ha⟩

/-- The hypotheses of `AutoIp.isRegularizationMethod_apriori` can fail. -/
theorem AutoIp.isRegularizationMethod_apriori_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (φ : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (Cφ : ℝ), ∃ (hφ : AutoIp.IsRegularizingFilter K φ Cφ), ∃ (ν : ℝ), ∃ (ρ : ℝ), ∃ (CF : ℝ), ∃ (cl : ℝ), ∃ (cu : ℝ), ∃ (a : AutoIp.ParameterChoice F), ¬ ((AutoIp.IsRegularization K (AutoIp.spectralReg hs φ (AutoIp.IsRegularizingFilter.exists_bound_on_spectrum hs hφ))) ∧ ((0 : ℝ) < ν) ∧ ((0 : ℝ) < ρ) ∧ (AutoIp.HasFilterBound K φ CF) ∧ (AutoIp.ParameterChoice.IsAPriori a) ∧ ((0 : ℝ) < cl) ∧ (∀ (δ : (↑(Set.Ioi (0 : ℝ)) : Type)) (z : F),
  cl * ((↑δ : ℝ) / ρ) ^ ((2 : ℝ) / (ν + (1 : ℝ))) ≤ (a : (↑(Set.Ioi (0 : ℝ)) : Type) → F → ℝ) δ z ∧
    (a : (↑(Set.Ioi (0 : ℝ)) : Type) → F → ℝ) δ z ≤ cu * ((↑δ : ℝ) / ρ) ^ ((2 : ℝ) / (ν + (1 : ℝ))))) :=
  by
  classical
  have hsub : ∀ p q : Submodule ℝ Unit, p = q := fun p q => Subsingleton.elim p q
  have hss : IsSingularSystem (ι := Empty) (0 : Unit →L[ℝ] Unit)
      (fun _ => 0) (fun _ => ()) (fun _ => ()) :=
    { pos := fun i => i.elim
      orthonormal_left := ⟨fun i => i.elim, fun {i _} _ => i.elim⟩
      orthonormal_right := ⟨fun i => i.elim, fun {i _} _ => i.elim⟩
      span_left := hsub _ _
      span_right := hsub _ _
      map_left := fun i => i.elim
      map_right := fun i => i.elim }
  have hI : Set.Ioc (0 : ℝ) (‖(0 : Unit →L[ℝ] Unit)‖ ^ (2 : ℕ)) = ∅ := by
    rw [norm_zero]; simp
  have hflt : AutoIp.IsRegularizingFilter (0 : Unit →L[ℝ] Unit) (fun _ _ => 0) 1 :=
    ⟨one_pos, fun _ => ⟨0, fun t _ => by simp⟩,
      fun lam hlam => by rw [hI] at hlam; exact hlam.elim,
      fun _ lam hlam => by rw [hI] at hlam; exact hlam.elim⟩
  have hsup : ∀ f : ℝ → ℝ, (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖(0 : Unit →L[ℝ] Unit)‖ ^ (2 : ℕ)),
      f lam) = 0 := by
    intro f
    rw [hI]
    simp
  have hfb : AutoIp.HasFilterBound (0 : Unit →L[ℝ] Unit) (fun _ _ => 0) 1 :=
    ⟨⟨1, hflt⟩, one_pos, fun α => by
      rw [hsup]
      exact mul_nonneg zero_le_one (inv_nonneg.2 (le_of_lt α.2))⟩
  let a : AutoIp.ParameterChoice Unit :=
    ⟨fun δ _ => ((δ : ℝ) / 1) ^ ((2 : ℝ) / (1 + 1)),
      fun δ _ => Real.rpow_pos_of_pos (div_pos δ.2 one_pos) _⟩
  have ha : ∀ (δ : Set.Ioi (0 : ℝ)) (z : Unit),
      1 * ((δ : ℝ) / 1) ^ ((2 : ℝ) / (1 + 1)) ≤ a δ z ∧
        a δ z ≤ 1 * ((δ : ℝ) / 1) ^ ((2 : ℝ) / (1 + 1)) := fun δ z => by
    rw [one_mul]; exact ⟨le_rfl, le_rfl⟩
  have hqual : ∀ α : Set.Ioi (0 : ℝ), (⨆ lam ∈ Set.Ioc (0 : ℝ)
      (‖(0 : Unit →L[ℝ] Unit)‖ ^ (2 : ℕ)), lam ^ ((1 : ℝ) / (2 : ℝ)) *
        |(1 : ℝ) - lam * (fun _ _ => (0 : ℝ)) α lam|) ≤ 1 * (α : ℝ) ^ ((1 : ℝ) / (2 : ℝ)) :=
    fun α => by
      rw [hsup, one_mul]
      exact Real.rpow_nonneg (le_of_lt α.2) _
  have hy : (() : Unit) ∈ AutoIp.mpDomain (0 : Unit →L[ℝ] Unit) := by
    rw [Subsingleton.elim () 0]; exact Submodule.zero_mem _
  have hsrc : ∀ x : Unit, x ∈ AutoIp.sourceSet hss 1 one_pos 1 one_pos := fun x =>
    (AutoIp.mem_sourceSet_iff _ _ _ _ _).2 ⟨0, by rw [norm_zero]; exact zero_le_one,
      Subsingleton.elim _ _⟩
  refine ⟨ℝ, inferInstance, Unit, Unit, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, 0, Empty, fun _ => 0, fun _ => (),
    fun _ => (), hss, fun _ _ => 0, 1, hflt, 0, 1, 1, 1, 1, a, ?_⟩
  rintro ⟨-, h, -⟩
  exact lt_irrefl 0 h

/-- The hypotheses of `AutoIp.isOrderOptimal_apriori` can hold together. -/
theorem AutoIp.isOrderOptimal_apriori_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (φ : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (Cφ : ℝ), ∃ (ν : ℝ), ∃ (ρ : ℝ), ∃ (CF : ℝ), ∃ (Cν : ℝ), ∃ (cl : ℝ), ∃ (cu : ℝ), ∃ (a : AutoIp.ParameterChoice F), (IsSingularSystem K σ v u) ∧ (AutoIp.IsRegularizingFilter K φ Cφ) ∧ ((0 : ℝ) < ν) ∧ ((0 : ℝ) < ρ) ∧ (AutoIp.HasFilterBound K φ CF) ∧ (∀ (α : (↑(Set.Ioi (0 : ℝ)) : Type)),
  ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), lam ^ (ν / (2 : ℝ)) * |(1 : ℝ) - lam * φ α lam| ≤
    Cν * (↑α : ℝ) ^ (ν / (2 : ℝ))) ∧ ((0 : ℝ) < cl) ∧ ((0 : ℝ) < cu) ∧ (∀ (δ : (↑(Set.Ioi (0 : ℝ)) : Type)) (z : F),
  cl * ((↑δ : ℝ) / ρ) ^ ((2 : ℝ) / (ν + (1 : ℝ))) ≤ (a : (↑(Set.Ioi (0 : ℝ)) : Type) → F → ℝ) δ z ∧
    (a : (↑(Set.Ioi (0 : ℝ)) : Type) → F → ℝ) δ z ≤ cu * ((↑δ : ℝ) / ρ) ^ ((2 : ℝ) / (ν + (1 : ℝ)))) :=
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
  have hres : ∀ (α : Set.Ioi (0 : ℝ)) (lam : ℝ), 0 < lam →
      |1 - lam * φ α lam| ≤ 1 ∧ ((α : ℝ) ≤ lam → 1 - lam * φ α lam = 0) := by
    intro α lam hlam
    have hm := hmax α lam
    have hle : lam * φ α lam ≤ 1 := by
      rw [hφa, ← div_eq_mul_inv, div_le_one hm]; exact le_max_right _ _
    have hnn : 0 ≤ lam * φ α lam := mul_nonneg hlam.le (inv_nonneg.2 hm.le)
    refine ⟨by rw [abs_le]; constructor <;> linarith, fun h => ?_⟩
    rw [hφa, max_eq_right h, mul_inv_cancel₀ hlam.ne', sub_self]
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
  -- the a-priori rule `α(δ) = (δ/ρ)^{2/(ν+1)}` with `ν = ρ = 1`
  let a : AutoIp.ParameterChoice ℝ :=
    ⟨fun δ _ => ((δ : ℝ) / 1) ^ ((2 : ℝ) / (1 + 1)),
      fun δ _ => Real.rpow_pos_of_pos (div_pos δ.2 one_pos) _⟩
  have ha : ∀ (δ : Set.Ioi (0 : ℝ)) (z : ℝ),
      1 * ((δ : ℝ) / 1) ^ ((2 : ℝ) / (1 + 1)) ≤ a δ z ∧
        a δ z ≤ 1 * ((δ : ℝ) / 1) ^ ((2 : ℝ) / (1 + 1)) := fun δ z => by
    rw [one_mul]; exact ⟨le_rfl, le_rfl⟩
  exact ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1,
    φ, 1, 1, 1, 1, 1, 1, 1, a, hone, hflt, one_pos, one_pos, hfb, hqual 1 one_pos,
    one_pos, one_pos, ha⟩

/-- The hypotheses of `AutoIp.isOrderOptimal_apriori` can fail. -/
theorem AutoIp.isOrderOptimal_apriori_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (φ : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (Cφ : ℝ), ∃ (ν : ℝ), ∃ (ρ : ℝ), ∃ (CF : ℝ), ∃ (Cν : ℝ), ∃ (cl : ℝ), ∃ (cu : ℝ), ∃ (a : AutoIp.ParameterChoice F), ¬ ((IsSingularSystem K σ v u) ∧ (AutoIp.IsRegularizingFilter K φ Cφ) ∧ ((0 : ℝ) < ν) ∧ ((0 : ℝ) < ρ) ∧ (AutoIp.HasFilterBound K φ CF) ∧ (∀ (α : (↑(Set.Ioi (0 : ℝ)) : Type)),
  ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), lam ^ (ν / (2 : ℝ)) * |(1 : ℝ) - lam * φ α lam| ≤
    Cν * (↑α : ℝ) ^ (ν / (2 : ℝ))) ∧ ((0 : ℝ) < cl) ∧ ((0 : ℝ) < cu) ∧ (∀ (δ : (↑(Set.Ioi (0 : ℝ)) : Type)) (z : F),
  cl * ((↑δ : ℝ) / ρ) ^ ((2 : ℝ) / (ν + (1 : ℝ))) ≤ (a : (↑(Set.Ioi (0 : ℝ)) : Type) → F → ℝ) δ z ∧
    (a : (↑(Set.Ioi (0 : ℝ)) : Type) → F → ℝ) δ z ≤ cu * ((↑δ : ℝ) / ρ) ^ ((2 : ℝ) / (ν + (1 : ℝ))))) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, fun _ _ => 0, 1,
    1, 1, 0, 0, 1, 1, ⟨fun _ _ => 1, fun _ _ => one_pos⟩, ?_⟩
  rintro ⟨H, _, _, _, _, _, _, _, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)
