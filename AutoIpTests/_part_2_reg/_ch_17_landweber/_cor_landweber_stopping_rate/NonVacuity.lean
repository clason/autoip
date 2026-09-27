module

import AutoIp._part_2_reg._ch_17_landweber._cor_landweber_stopping_rate.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.landweber_stopping_le_of_mem_sourceSet` can hold together. -/
theorem AutoIp.landweber_stopping_le_of_mem_sourceSet_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ω : ℝ), ∃ (ν : ℝ), ∃ (ρ : ℝ), ∃ (τ : ℝ), (IsSingularSystem K σ v u) ∧ ((0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) < (1 : ℝ)) ∧ (Dense (↑(LinearMap.range (↑K : E →ₗ[𝕜] F)) : Set F)) ∧ ((0 : ℝ) < ν) ∧ ((0 : ℝ) < ρ) ∧ ((1 : ℝ) < τ) :=
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
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1, 1 / 2, 1, 1, 2, hone, hω, hd, one_pos, one_pos,
    by norm_num⟩

/-- The hypotheses of `AutoIp.landweber_stopping_le_of_mem_sourceSet` can fail. -/
theorem AutoIp.landweber_stopping_le_of_mem_sourceSet_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ω : ℝ), ∃ (ν : ℝ), ∃ (ρ : ℝ), ∃ (τ : ℝ), ¬ ((IsSingularSystem K σ v u) ∧ ((0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) < (1 : ℝ)) ∧ (Dense (↑(LinearMap.range (↑K : E →ₗ[𝕜] F)) : Set F)) ∧ ((0 : ℝ) < ν) ∧ ((0 : ℝ) < ρ) ∧ ((1 : ℝ) < τ)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, 0, 1, 1, 2, ?_⟩
  rintro ⟨H, _, _, _, _, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)
