module

import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_hom.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity
import AutoIpTests.Witnesses.Zero

open scoped InnerProductSpace

/-- The hypotheses of `IsSingularSystem.funCalc_add` can hold together. -/
theorem IsSingularSystem.funCalc_add_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (φ : ℝ → ℝ), ∃ (ψ : ℝ → ℝ), (IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |φ t| ≤ C) ∧ (∃ (C : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |ψ t| ≤ C) :=
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
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Empty, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
    fun _ => 0, ?_⟩
  exact ⟨hss, ⟨0, fun _ _ => by simp⟩, ⟨0, fun _ _ => by simp⟩⟩

/-- The hypotheses of `IsSingularSystem.funCalc_add` can fail. -/
theorem IsSingularSystem.funCalc_add_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (φ : ℝ → ℝ), ∃ (ψ : ℝ → ℝ), ¬ ((IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |φ t| ≤ C) ∧ (∃ (C : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |ψ t| ≤ C)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
    fun _ => 0, ?_⟩
  rintro ⟨H, _, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)

/-- The hypotheses of `IsSingularSystem.funCalc_smul` can hold together. -/
theorem IsSingularSystem.funCalc_smul_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (c : ℝ), ∃ (φ : ℝ → ℝ), (IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |φ t| ≤ C) :=
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
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Empty, fun _ => 0, fun _ => 0, fun _ => 0, 0, fun _ => 0, ?_⟩
  exact ⟨hss, ⟨0, fun _ _ => by simp⟩⟩

/-- The hypotheses of `IsSingularSystem.funCalc_smul` can fail. -/
theorem IsSingularSystem.funCalc_smul_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (c : ℝ), ∃ (φ : ℝ → ℝ), ¬ ((IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |φ t| ≤ C)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, 0, fun _ => 0, ?_⟩
  rintro ⟨H, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)

/-- The hypotheses of `IsSingularSystem.funCalc_mul` can hold together. -/
theorem IsSingularSystem.funCalc_mul_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (φ : ℝ → ℝ), ∃ (ψ : ℝ → ℝ), (IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |φ t| ≤ C) ∧ (∃ (C : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |ψ t| ≤ C) :=
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
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Empty, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
    fun _ => 0, ?_⟩
  exact ⟨hss, ⟨0, fun _ _ => by simp⟩, ⟨0, fun _ _ => by simp⟩⟩

/-- The hypotheses of `IsSingularSystem.funCalc_mul` can fail. -/
theorem IsSingularSystem.funCalc_mul_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (φ : ℝ → ℝ), ∃ (ψ : ℝ → ℝ), ¬ ((IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |φ t| ≤ C) ∧ (∃ (C : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |ψ t| ≤ C)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
    fun _ => 0, ?_⟩
  rintro ⟨H, _, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)

/-- The hypotheses of `IsSingularSystem.funCalc_rpow_apply_v` can hold together. -/
theorem IsSingularSystem.funCalc_rpow_apply_v_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ν : ℝ), ∃ (i : ι), (IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ (i : ι), |(fun (t : ℝ) => t ^ (ν / (2 : ℝ))) (σ i ^ (2 : ℕ))| ≤ C) :=
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
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1, 2, (), ?_⟩
  exact ⟨hone, ⟨1, fun _ => by norm_num⟩⟩

/-- The hypotheses of `IsSingularSystem.funCalc_rpow_apply_v` can fail. -/
theorem IsSingularSystem.funCalc_rpow_apply_v_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ν : ℝ), ∃ (i : ι), ¬ ((IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ (i : ι), |(fun (t : ℝ) => t ^ (ν / (2 : ℝ))) (σ i ^ (2 : ℕ))| ≤ C)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, 2, (), ?_⟩
  intro H
  exact absurd (H.1.pos ()) (lt_irrefl 0)
