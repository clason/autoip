module

import AutoIp._part_2_reg._ch_17_landweber._thm_landweber_order_optimal.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.landweberFilter_iSup_abs_le_inv_mul` can hold together. -/
theorem AutoIp.landweberFilter_iSup_abs_le_inv_mul_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (ω : ℝ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), (0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) < (1 : ℝ) :=
  by
  have hω : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) * ‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ) < 1 := by
    rw [Witnesses.Identity.norm_one']; norm_num
  exact ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 1,
    1 / 2, ⟨1, Set.mem_Ioi.2 one_pos⟩, hω⟩

/-- The hypotheses of `AutoIp.landweberFilter_iSup_abs_le_inv_mul` can fail. -/
theorem AutoIp.landweberFilter_iSup_abs_le_inv_mul_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (ω : ℝ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ¬ ((0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) < (1 : ℝ)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 0,
    0, ⟨1, Set.mem_Ioi.2 one_pos⟩, ?_⟩
  rintro ⟨H, _⟩
  exact absurd H (lt_irrefl 0)

/-- The hypotheses of `AutoIp.landweberFilter_iSup_rpow_mul_residual_le` can hold together. -/
theorem AutoIp.landweberFilter_iSup_rpow_mul_residual_le_satisfiable : ∃ (ω : ℝ), ∃ (κ : ℝ), ∃ (ν : ℝ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ((0 : ℝ) < ω) ∧ (ω * κ ≤ (1 : ℝ)) ∧ ((0 : ℝ) < ν) :=
  by
  refine ⟨1, 0, 1, ⟨1, Set.mem_Ioi.2 one_pos⟩, ?_⟩
  exact ⟨by norm_num, by simp, by norm_num⟩

/-- The hypotheses of `AutoIp.landweberFilter_iSup_rpow_mul_residual_le` can fail. -/
theorem AutoIp.landweberFilter_iSup_rpow_mul_residual_le_nontrivial : ∃ (ω : ℝ), ∃ (κ : ℝ), ∃ (ν : ℝ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ¬ (((0 : ℝ) < ω) ∧ (ω * κ ≤ (1 : ℝ)) ∧ ((0 : ℝ) < ν)) :=
  by
  refine ⟨0, 0, 1, ⟨1, Set.mem_Ioi.2 one_pos⟩, ?_⟩
  rintro ⟨H, _, _⟩
  exact absurd H (lt_irrefl 0)

/-- The hypotheses of `AutoIp.landweberFilter_hasFilterBound_and_hasResidualBound` can hold together. -/
theorem AutoIp.landweberFilter_hasFilterBound_and_hasResidualBound_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (ω : ℝ), (0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) < (1 : ℝ) :=
  by
  have hω : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) * ‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ) < 1 := by
    rw [Witnesses.Identity.norm_one']; norm_num
  exact ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 1,
    1 / 2, hω⟩

/-- The hypotheses of `AutoIp.landweberFilter_hasFilterBound_and_hasResidualBound` can fail. -/
theorem AutoIp.landweberFilter_hasFilterBound_and_hasResidualBound_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (ω : ℝ), ¬ ((0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) < (1 : ℝ)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 0,
    0, ?_⟩
  rintro ⟨H, _⟩
  exact absurd H (lt_irrefl 0)

/-- The hypotheses of `AutoIp.qualification_landweberFilter_eq_top` can hold together. -/
theorem AutoIp.qualification_landweberFilter_eq_top_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (ω : ℝ), (0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) < (1 : ℝ) :=
  by
  have hω : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) * ‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ) < 1 := by
    rw [Witnesses.Identity.norm_one']; norm_num
  exact ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 1,
    1 / 2, hω⟩

/-- The hypotheses of `AutoIp.qualification_landweberFilter_eq_top` can fail. -/
theorem AutoIp.qualification_landweberFilter_eq_top_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (ω : ℝ), ¬ ((0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) < (1 : ℝ)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 0,
    0, ?_⟩
  rintro ⟨H, _⟩
  exact absurd H (lt_irrefl 0)

/-- The hypotheses of `AutoIp.iSup_abs_one_sub_mul_landweberFilter_eq_one` can hold together. -/
theorem AutoIp.iSup_abs_one_sub_mul_landweberFilter_eq_one_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (ω : ℝ), (K ≠ (0 : E →L[𝕜] F)) ∧ ((0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) < (1 : ℝ)) :=
  by
  have hω : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) * ‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ) < 1 := by
    rw [Witnesses.Identity.norm_one']; norm_num
  exact ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 1,
    1 / 2, one_ne_zero, hω⟩

/-- The hypotheses of `AutoIp.iSup_abs_one_sub_mul_landweberFilter_eq_one` can fail. -/
theorem AutoIp.iSup_abs_one_sub_mul_landweberFilter_eq_one_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (ω : ℝ), ¬ ((K ≠ (0 : E →L[𝕜] F)) ∧ ((0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) < (1 : ℝ))) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 0,
    0, ?_⟩
  rintro ⟨H, _⟩
  exact H rfl

/-- The hypotheses of `AutoIp.landweber_discrepancy_rate` can hold together. -/
theorem AutoIp.landweber_discrepancy_rate_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ω : ℝ), ∃ (τ : ℝ), (IsSingularSystem K σ v u) ∧ (K ≠ (0 : E →L[𝕜] F)) ∧ ((0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) < (1 : ℝ)) ∧ (Dense (↑(LinearMap.range (↑K : E →ₗ[𝕜] F)) : Set F)) ∧ ((1 : ℝ) < τ) :=
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
  have hω : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) * ‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ) < 1 := by
    rw [Witnesses.Identity.norm_one']; norm_num
  have hd : Dense (↑(LinearMap.range ((1 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ)) : Set ℝ) := by
    have hr : LinearMap.range ((1 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) = ⊤ := LinearMap.range_id
    rw [hr, Submodule.top_coe]
    exact dense_univ
  exact ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1, 1 / 2, 2, hone,
    one_ne_zero, hω, hd, by norm_num⟩

/-- The hypotheses of `AutoIp.landweber_discrepancy_rate` can fail. -/
theorem AutoIp.landweber_discrepancy_rate_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ω : ℝ), ∃ (τ : ℝ), ¬ ((IsSingularSystem K σ v u) ∧ (K ≠ (0 : E →L[𝕜] F)) ∧ ((0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) < (1 : ℝ)) ∧ (Dense (↑(LinearMap.range (↑K : E →ₗ[𝕜] F)) : Set F)) ∧ ((1 : ℝ) < τ)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, 0, 2, ?_⟩
  rintro ⟨H, _, _, _, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)
