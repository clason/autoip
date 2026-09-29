module

import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_fun_calc.Spec -- shake: keep
import AutoIpTests.Witnesses.Zero

/-- The hypotheses of `IsSingularSystem.funCalc` can hold together. -/
theorem IsSingularSystem.funCalc_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (φ : ℝ → ℝ), (IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ (i : ι), |φ (σ i ^ (2 : ℕ))| ≤ C) :=
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
    inferInstance, inferInstance, 0, Empty, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  exact ⟨hss, ⟨0, fun i => i.elim⟩⟩

/-- The hypotheses of `IsSingularSystem.funCalc` can fail. -/
theorem IsSingularSystem.funCalc_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (φ : ℝ → ℝ), ¬ ((IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ (i : ι), |φ (σ i ^ (2 : ℕ))| ≤ C)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  rintro ⟨H, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)

/-- The hypotheses of `IsSingularSystem.hasSum_funCalc_sub_starProjection` can hold together. -/
theorem IsSingularSystem.hasSum_funCalc_sub_starProjection_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (φ : ℝ → ℝ), ∃ (x : E), (IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ (i : ι), |φ (σ i ^ (2 : ℕ))| ≤ C) :=
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
  exact ⟨hss, ⟨0, fun i => i.elim⟩⟩

/-- The hypotheses of `IsSingularSystem.hasSum_funCalc_sub_starProjection` can fail. -/
theorem IsSingularSystem.hasSum_funCalc_sub_starProjection_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (φ : ℝ → ℝ), ∃ (x : E), ¬ ((IsSingularSystem K σ v u) ∧ (∃ (C : ℝ), ∀ (i : ι), |φ (σ i ^ (2 : ℕ))| ≤ C)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, 0, ?_⟩
  rintro ⟨H, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)
