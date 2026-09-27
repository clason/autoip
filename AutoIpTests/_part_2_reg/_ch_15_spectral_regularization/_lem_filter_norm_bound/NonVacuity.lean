module

import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_filter_norm_bound.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.opNorm_spectralReg_le` can hold together. -/
theorem AutoIp.opNorm_spectralReg_le_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (φ : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (C : ℝ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), (IsSingularSystem K σ v u) ∧ (AutoIp.IsRegularizingFilter K φ C) :=
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
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1,
    φ, 1, ⟨1, Set.mem_Ioi.2 one_pos⟩, ?_⟩
  exact ⟨hone, hflt⟩

/-- The hypotheses of `AutoIp.opNorm_spectralReg_le` can fail. -/
theorem AutoIp.opNorm_spectralReg_le_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (φ : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (C : ℝ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ¬ ((IsSingularSystem K σ v u) ∧ (AutoIp.IsRegularizingFilter K φ C)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, fun _ _ => 0, 1, ⟨1, Set.mem_Ioi.2 one_pos⟩
    , ?_⟩
  rintro ⟨H, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)
