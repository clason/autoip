module

import AutoIp._part_2_reg._ch_21_perturbed_operator._lem_tikhonov_operator_perturbation.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.opNorm_tikhonov_perturbed_sub_le` can hold together. -/
theorem AutoIp.opNorm_tikhonov_perturbed_sub_le_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (Kh : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ι' : Type), ∃ (σ' : ι' → ℝ), ∃ (v' : ι' → E), ∃ (u' : ι' → F), ∃ (h : ℝ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), (IsSingularSystem K σ v u) ∧ (IsSingularSystem Kh σ' v' u') ∧ (‖K - Kh‖ ≤ h) :=
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
  have hhalf : IsSingularSystem (ι := Unit) ((1 / 2 : ℝ) • (1 : ℝ →L[ℝ] ℝ))
      (fun _ => 1 / 2) (fun _ => 1) (fun _ => 1) :=
    { pos := fun _ => by norm_num
      orthonormal_left := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      orthonormal_right := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      span_left := by
        rw [ContinuousLinearMap.toLinearMap_smul, LinearMap.ker_smul _ _ (by norm_num)]
        exact Witnesses.Identity.span_left _ fun _ => rfl
      span_right := by
        rw [ContinuousLinearMap.toLinearMap_smul, LinearMap.range_smul _ _ (by norm_num)]
        exact Witnesses.Identity.span_right _ fun _ => rfl
      map_left := fun _ => by simp
      map_right := fun _ => by
        rw [map_smulₛₗ, smul_apply, Witnesses.Identity.adjoint_one_apply]
        simp }
  have hdist : ‖(1 : ℝ →L[ℝ] ℝ) - (1 / 2 : ℝ) • (1 : ℝ →L[ℝ] ℝ)‖ = 1 / 2 := by
    rw [show (1 : ℝ →L[ℝ] ℝ) - (1 / 2 : ℝ) • (1 : ℝ →L[ℝ] ℝ) = (1 / 2 : ℝ) • (1 : ℝ →L[ℝ] ℝ) by
      rw [sub_eq_iff_eq_add, ← add_smul]; norm_num, norm_smul, Witnesses.Identity.norm_one']
    norm_num
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, (1 / 2 : ℝ) • (1 : ℝ →L[ℝ] ℝ), Unit, fun _ => 1, fun _ => 1,
    fun _ => 1, Unit, fun _ => 1 / 2, fun _ => 1, fun _ => 1, 1 / 2, ⟨1, Set.mem_Ioi.2 one_pos⟩,
    ?_⟩
  exact ⟨hone, hhalf, hdist.le⟩

/-- The hypotheses of `AutoIp.opNorm_tikhonov_perturbed_sub_le` can fail. -/
theorem AutoIp.opNorm_tikhonov_perturbed_sub_le_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (Kh : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ι' : Type), ∃ (σ' : ι' → ℝ), ∃ (v' : ι' → E), ∃ (u' : ι' → F), ∃ (h : ℝ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ¬ ((IsSingularSystem K σ v u) ∧ (IsSingularSystem Kh σ' v' u') ∧ (‖K - Kh‖ ≤ h)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, Empty,
    fun _ => 0, fun _ => 0, fun _ => 0, 0, ⟨1, Set.mem_Ioi.2 one_pos⟩, ?_⟩
  rintro ⟨H, _, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)
