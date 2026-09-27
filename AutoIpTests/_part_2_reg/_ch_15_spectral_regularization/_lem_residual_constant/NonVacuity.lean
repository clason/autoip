module

import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_residual_constant.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.one_le_iSup_abs_one_sub_mul_and_norm_residual_le` can hold together. -/
theorem AutoIp.one_le_iSup_abs_one_sub_mul_and_norm_residual_le_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (x9 : CompleteSpace E), ∃ (x10 : CompleteSpace F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (φ : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (C : ℝ), (IsSingularSystem K σ v u) ∧ (K ≠ (0 : E →L[𝕜] F)) ∧ (AutoIp.IsRegularizingFilter K φ C) :=
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
  have hflt : AutoIp.IsRegularizingFilter (1 : ℝ →L[ℝ] ℝ)
      (fun α lam => (lam + (α : ℝ))⁻¹) 1 :=
    { const_pos := one_pos
      bddOn := by
        rintro ⟨α, hα⟩
        replace hα : (0 : ℝ) < α := hα
        refine ⟨α⁻¹, fun t ht => ?_⟩
        have h : 0 < t + α := by linarith [ht.1]
        rw [abs_of_nonneg (inv_nonneg.mpr h.le)]
        gcongr
        · linarith [ht.1]
      tendsto_inv := by
        intro lam hlam
        have hc : ContinuousAt (fun α : ℝ => (lam + α)⁻¹) 0 :=
          ContinuousAt.inv₀ (by fun_prop) (by simpa using hlam.1.ne')
        have h := hc.tendsto
        simp only [add_zero] at h
        have hv : Tendsto (fun α : Set.Ioi (0 : ℝ) => (α : ℝ)) atBot (𝓝 0) := by
          refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun α => lt_trans ha α.2,
            fun b hb => ?_⟩
          filter_upwards [eventually_le_atBot (⟨b / 2, by simp; linarith⟩ : Set.Ioi (0 : ℝ))]
            with α hα
          have : (α : ℝ) ≤ b / 2 := hα
          linarith
        exact h.comp hv
      mul_abs_le := by
        rintro ⟨α, hα⟩ lam hlam
        replace hα : (0 : ℝ) < α := hα
        have h : 0 < lam + α := by linarith [hlam.1]
        rw [abs_of_nonneg (inv_nonneg.mpr h.le), ← div_eq_mul_inv, div_le_one h]
        linarith }
  exact ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    1, inferInstance, inferInstance, Unit, fun _ => 1, fun _ => 1, fun _ => 1, _, 1,
    hone, Witnesses.Identity.one_ne_zero', hflt⟩

/-- The hypotheses of `AutoIp.one_le_iSup_abs_one_sub_mul_and_norm_residual_le` can fail. -/
theorem AutoIp.one_le_iSup_abs_one_sub_mul_and_norm_residual_le_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (x9 : CompleteSpace E), ∃ (x10 : CompleteSpace F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (φ : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (C : ℝ), ¬ ((IsSingularSystem K σ v u) ∧ (K ≠ (0 : E →L[𝕜] F)) ∧ (AutoIp.IsRegularizingFilter K φ C)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    0, inferInstance, inferInstance, Unit, fun _ => 0, fun _ => 0, fun _ => 0, fun _ _ => 0, 1
    , ?_⟩
  rintro ⟨H, _, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)

/-- The hypotheses of `AutoIp.iSup_abs_one_sub_mul_le_one_add` can hold together. -/
theorem AutoIp.iSup_abs_one_sub_mul_le_one_add_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (φ : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (Cφ : ℝ), AutoIp.IsRegularizingFilter K φ Cφ :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 0,
    fun _ _ => 0, 1, ?_⟩
  exact ⟨one_pos, fun _ => ⟨0, fun t _ => by simp⟩,
    fun lam hlam => absurd hlam (by simp),
    fun _ lam hlam => absurd hlam (by simp)⟩

/-- The hypotheses of `AutoIp.iSup_abs_one_sub_mul_le_one_add` can fail. -/
theorem AutoIp.iSup_abs_one_sub_mul_le_one_add_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (φ : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (Cφ : ℝ), ¬ (AutoIp.IsRegularizingFilter K φ Cφ) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 0,
    fun _ _ => 0, 0, ?_⟩
  intro H
  exact absurd H.const_pos (lt_irrefl 0)
