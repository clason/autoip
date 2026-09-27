module

import AutoIp._part_2_reg._ch_14_order_optimality._def_order_optimal.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity

open Filter Topology
open scoped ENNReal

/-- The hypotheses of `AutoIp.IsOrderOptimal` can hold together. -/
theorem AutoIp.IsOrderOptimal_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (K : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F → E), ∃ (b : AutoIp.ParameterChoice F), ∃ (ν : ℝ), ∃ (ρ : ℝ), ∃ (c : ℝ), IsSingularSystem K σ v u :=
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
    inferInstance, inferInstance, Unit, fun _ => 1, fun _ => 1, fun _ => 1, 1,
    fun α z => (1 + (α : ℝ))⁻¹ * z, ⟨fun δ _ => (δ : ℝ), fun δ _ => δ.2⟩, 1, 1, 1, ?_⟩
  exact hss

/-- The hypotheses of `AutoIp.IsOrderOptimal` can fail. -/
theorem AutoIp.IsOrderOptimal_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (K : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F → E), ∃ (b : AutoIp.ParameterChoice F), ∃ (ν : ℝ), ∃ (ρ : ℝ), ∃ (c : ℝ), ¬ (IsSingularSystem K σ v u) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, Unit, fun _ => 0, fun _ => 0, fun _ => 0, 0,
    fun _ => fun _ => 0, ⟨fun _ _ => 1, fun _ _ => one_pos⟩, 0, 0, 0, ?_⟩
  intro H
  exact absurd (H.pos ()) (lt_irrefl 0)

/-- The hypotheses of `AutoIp.IsOrderOptimalPointwise` can hold together. -/
theorem AutoIp.IsOrderOptimalPointwise_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (K : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F → E), ∃ (b : AutoIp.ParameterChoice F), ∃ (ν : ℝ), IsSingularSystem K σ v u :=
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
    inferInstance, inferInstance, Unit, fun _ => 1, fun _ => 1, fun _ => 1, 1,
    fun α z => (1 + (α : ℝ))⁻¹ * z, ⟨fun δ _ => (δ : ℝ), fun δ _ => δ.2⟩, 1, ?_⟩
  exact hss

/-- The hypotheses of `AutoIp.IsOrderOptimalPointwise` can fail. -/
theorem AutoIp.IsOrderOptimalPointwise_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (K : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F → E), ∃ (b : AutoIp.ParameterChoice F), ∃ (ν : ℝ), ¬ (IsSingularSystem K σ v u) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, Unit, fun _ => 0, fun _ => 0, fun _ => 0, 0,
    fun _ => fun _ => 0, ⟨fun _ _ => 1, fun _ _ => one_pos⟩, 0, ?_⟩
  intro H
  exact absurd (H.pos ()) (lt_irrefl 0)
