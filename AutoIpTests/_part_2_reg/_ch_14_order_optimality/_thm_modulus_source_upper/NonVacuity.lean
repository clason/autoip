module

import AutoIp._part_2_reg._ch_14_order_optimality._thm_modulus_source_upper.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity

open Filter Topology
open scoped ENNReal

/-- The hypotheses of `AutoIp.modulusOfContinuity_sourceSet_le` can hold together. -/
theorem AutoIp.modulusOfContinuity_sourceSet_le_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ν : ℝ), ∃ (ρ : ℝ), ∃ (δ : ℝ), (IsSingularSystem K σ v u) ∧ ((0 : ℝ) < ν) ∧ ((0 : ℝ) < ρ) ∧ ((0 : ℝ) < δ) :=
  by
  classical
  have hss : IsSingularSystem (ι := Unit) (1 : ℝ →L[ℝ] ℝ)
      (fun _ => 1) (fun _ => 1) (fun _ => 1) :=
    { pos := fun _ => one_pos
      orthonormal_left := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      orthonormal_right := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      span_left := Witnesses.Identity.span_left _ fun _ => rfl
      span_right := Witnesses.Identity.span_right _ fun _ => rfl
      map_left := fun _ => (one_mul (1 : ℝ)).symm
      map_right := fun _ =>
        (Witnesses.Identity.adjoint_one_apply 1).trans (one_mul (1 : ℝ)).symm }
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1, 1, 1, 1, ?_⟩
  exact ⟨hss, by norm_num, by norm_num, by norm_num⟩

/-- The hypotheses of `AutoIp.modulusOfContinuity_sourceSet_le` can fail. -/
theorem AutoIp.modulusOfContinuity_sourceSet_le_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ν : ℝ), ∃ (ρ : ℝ), ∃ (δ : ℝ), ¬ ((IsSingularSystem K σ v u) ∧ ((0 : ℝ) < ν) ∧ ((0 : ℝ) < ρ) ∧ ((0 : ℝ) < δ)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, 1, 1, 1, ?_⟩
  rintro ⟨H, _, _, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)
