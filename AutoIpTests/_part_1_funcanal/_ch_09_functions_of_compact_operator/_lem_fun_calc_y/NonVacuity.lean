module

import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_y.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity
import AutoIpTests.Witnesses.Zero

/-- The hypotheses of `IsSingularSystem.norm_funCalcRight_le` can hold together. -/
theorem IsSingularSystem.norm_funCalcRight_le_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ψ : ℝ → ℝ), ∃ (a : ℝ), (IsSingularSystem K σ v u) ∧ (∀ (i : ι), |ψ (σ i ^ (2 : ℕ))| ≤ a) :=
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
    inferInstance, inferInstance, 0, Empty, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, 0, ?_⟩
  exact ⟨hss, fun i => i.elim⟩

/-- The hypotheses of `IsSingularSystem.norm_funCalcRight_le` can fail. -/
theorem IsSingularSystem.norm_funCalcRight_le_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ψ : ℝ → ℝ), ∃ (a : ℝ), ¬ ((IsSingularSystem K σ v u) ∧ (∀ (i : ι), |ψ (σ i ^ (2 : ℕ))| ≤ a)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, 0, ?_⟩
  intro H
  exact absurd (H.1.pos ()) (lt_irrefl 0)

/-- The hypotheses of `IsSingularSystem.funCalcRight_id` can hold together. -/
theorem IsSingularSystem.funCalcRight_id_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), (IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ (i : ι), |id (σ i ^ (2 : ℕ))| ≤ C) :=
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
    inferInstance, inferInstance, 0, Empty, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  exact ⟨hss, ⟨0, fun i => i.elim⟩⟩

/-- The hypotheses of `IsSingularSystem.funCalcRight_id` can fail. -/
theorem IsSingularSystem.funCalcRight_id_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ¬ ((IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ (i : ι), |id (σ i ^ (2 : ℕ))| ≤ C)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  intro H
  exact absurd (H.1.pos ()) (lt_irrefl 0)

/-- The hypotheses of `IsSingularSystem.funCalcRight_mul` can hold together. -/
theorem IsSingularSystem.funCalcRight_mul_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ψ : ℝ → ℝ), ∃ (χ : ℝ → ℝ), (IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |ψ t| ≤ C) ∧ (∃ (C : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |χ t| ≤ C) :=
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
    inferInstance, inferInstance, 0, Empty, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  exact ⟨hss, ⟨0, fun _ _ => by simp⟩, ⟨0, fun _ _ => by simp⟩⟩

/-- The hypotheses of `IsSingularSystem.funCalcRight_mul` can fail. -/
theorem IsSingularSystem.funCalcRight_mul_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ψ : ℝ → ℝ), ∃ (χ : ℝ → ℝ), ¬ ((IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |ψ t| ≤ C) ∧ (∃ (C : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |χ t| ≤ C)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  intro H
  exact absurd (H.1.pos ()) (lt_irrefl 0)

/-- The hypotheses of `IsSingularSystem.funCalcRight_one` can hold together. -/
theorem IsSingularSystem.funCalcRight_one_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), (IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ (i : ι), |(fun (x : ℝ) => (1 : ℝ)) (σ i ^ (2 : ℕ))| ≤ C) :=
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
    inferInstance, inferInstance, 0, Empty, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  exact ⟨hss, ⟨0, fun i => i.elim⟩⟩

/-- The hypotheses of `IsSingularSystem.funCalcRight_one` can fail. -/
theorem IsSingularSystem.funCalcRight_one_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ¬ ((IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ (i : ι), |(fun (x : ℝ) => (1 : ℝ)) (σ i ^ (2 : ℕ))| ≤ C)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  intro H
  exact absurd (H.1.pos ()) (lt_irrefl 0)

/-- The hypotheses of `IsSingularSystem.funCalcRight_sqrt_comp_funCalcRight_sqrt` can hold together. -/
theorem IsSingularSystem.funCalcRight_sqrt_comp_funCalcRight_sqrt_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), (IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ (i : ι), |√(σ i ^ (2 : ℕ))| ≤ C) :=
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
    inferInstance, inferInstance, 0, Empty, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  exact ⟨hss, ⟨0, fun i => i.elim⟩⟩

/-- The hypotheses of `IsSingularSystem.funCalcRight_sqrt_comp_funCalcRight_sqrt` can fail. -/
theorem IsSingularSystem.funCalcRight_sqrt_comp_funCalcRight_sqrt_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ¬ ((IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ (i : ι), |√(σ i ^ (2 : ℕ))| ≤ C)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  intro H
  exact absurd (H.1.pos ()) (lt_irrefl 0)

/-- The hypotheses of `IsSingularSystem.funCalcRight_add` can hold together. -/
theorem IsSingularSystem.funCalcRight_add_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ψ : ℝ → ℝ), ∃ (χ : ℝ → ℝ), (IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |ψ t| ≤ C) ∧ (∃ (C : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |χ t| ≤ C) :=
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
    inferInstance, inferInstance, 0, Empty, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  exact ⟨hss, ⟨0, fun _ _ => by simp⟩, ⟨0, fun _ _ => by simp⟩⟩

/-- The hypotheses of `IsSingularSystem.funCalcRight_add` can fail. -/
theorem IsSingularSystem.funCalcRight_add_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ψ : ℝ → ℝ), ∃ (χ : ℝ → ℝ), ¬ ((IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |ψ t| ≤ C) ∧ (∃ (C : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |χ t| ≤ C)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  intro H
  exact absurd (H.1.pos ()) (lt_irrefl 0)

/-- The hypotheses of `IsSingularSystem.funCalcRight_smul` can hold together. -/
theorem IsSingularSystem.funCalcRight_smul_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (c : ℝ), ∃ (ψ : ℝ → ℝ), (IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |ψ t| ≤ C) :=
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

/-- The hypotheses of `IsSingularSystem.funCalcRight_smul` can fail. -/
theorem IsSingularSystem.funCalcRight_smul_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (c : ℝ), ∃ (ψ : ℝ → ℝ), ¬ ((IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |ψ t| ≤ C)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, 0, fun _ => 0, ?_⟩
  intro H
  exact absurd (H.1.pos ()) (lt_irrefl 0)

/-- The hypotheses of `IsSingularSystem.funCalcRight_rpow_apply_u` can hold together. -/
theorem IsSingularSystem.funCalcRight_rpow_apply_u_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ν : ℝ), ∃ (i : ι), (IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ (i : ι), |(fun (t : ℝ) => t ^ (ν / (2 : ℝ))) (σ i ^ (2 : ℕ))| ≤ C) :=
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

/-- The hypotheses of `IsSingularSystem.funCalcRight_rpow_apply_u` can fail. -/
theorem IsSingularSystem.funCalcRight_rpow_apply_u_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ν : ℝ), ∃ (i : ι), ¬ ((IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ (i : ι), |(fun (t : ℝ) => t ^ (ν / (2 : ℝ))) (σ i ^ (2 : ℕ))| ≤ C)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, 2, (), ?_⟩
  intro H
  exact absurd (H.1.pos ()) (lt_irrefl 0)
