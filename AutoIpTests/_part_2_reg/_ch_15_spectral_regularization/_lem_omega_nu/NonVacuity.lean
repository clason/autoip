module

import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_omega_nu.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity
import AutoIpTests.Witnesses.Zero

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.norm_spectralReg_sub_moorePenrose_le` can hold together. -/
theorem AutoIp.norm_spectralReg_sub_moorePenrose_le_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (φ : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (C : ℝ), ∃ (ν : ℝ), ∃ (ρ : ℝ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ∃ (hν : (0 : ℝ) < ν), ∃ (hρ : (0 : ℝ) < ρ), ∃ (y : F), ∃ (hy : y ∈ AutoIp.mpDomain K), (AutoIp.IsRegularizingFilter K φ C) ∧ ((↑(AutoIp.moorePenrose K) : ↥(LinearPMap.domain (AutoIp.moorePenrose K)) → E) ⟨y, hy⟩ ∈ AutoIp.sourceSet hs ν hν ρ hρ) :=
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
    φ, 1, 1, 1, ⟨1, Set.mem_Ioi.2 one_pos⟩, one_pos, one_pos, 1, hdom 1, hflt, ?_⟩
  rw [hmp]
  exact hsrc 1 one_pos

/-- The hypotheses of `AutoIp.norm_spectralReg_sub_moorePenrose_le` can fail. -/
theorem AutoIp.norm_spectralReg_sub_moorePenrose_le_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (φ : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (C : ℝ), ∃ (ν : ℝ), ∃ (ρ : ℝ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ∃ (hν : (0 : ℝ) < ν), ∃ (hρ : (0 : ℝ) < ρ), ∃ (y : F), ∃ (hy : y ∈ AutoIp.mpDomain K), ¬ ((AutoIp.IsRegularizingFilter K φ C) ∧ ((↑(AutoIp.moorePenrose K) : ↥(LinearPMap.domain (AutoIp.moorePenrose K)) → E) ⟨y, hy⟩ ∈ AutoIp.sourceSet hs ν hν ρ hρ)) :=
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
  have hy : (0 : ℝ) ∈ AutoIp.mpDomain (0 : ℝ →L[ℝ] ℝ) := Submodule.zero_mem _
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Empty, fun _ => 0, fun _ => 0, fun _ => 0, hss,
    fun _ _ => 0, 0, 1, 1, ⟨1, Set.mem_Ioi.2 one_pos⟩, one_pos, one_pos, 0, hy, ?_⟩
  rintro ⟨H, -⟩
  exact absurd H.const_pos (lt_irrefl 0)
