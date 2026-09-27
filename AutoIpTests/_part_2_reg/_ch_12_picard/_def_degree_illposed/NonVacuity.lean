module

import AutoIp._part_2_reg._ch_12_picard._def_degree_illposed.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity

open scoped InnerProductSpace

/-- The hypotheses of `AutoIp.IsModeratelyIllPosed` can hold together. -/
theorem AutoIp.IsModeratelyIllPosed_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (I : Set ℕ), ∃ (σ : (↑I : Type) → ℝ), ∃ (v : (↑I : Type) → E), ∃ (u : (↑I : Type) → F), IsOrderedSingularSystem K σ v u :=
  by
  classical
  have : Nonempty ↥({0} : Set ℕ) := ⟨⟨0, rfl⟩⟩
  have hss : IsSingularSystem (ι := ↥({0} : Set ℕ)) (1 : ℝ →L[ℝ] ℝ)
      (fun _ => 1) (fun _ => 1) (fun _ => 1) :=
    { pos := fun _ => one_pos
      orthonormal_left := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      orthonormal_right := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      span_left := Witnesses.Identity.span_left _ fun _ => rfl
      span_right := Witnesses.Identity.span_right _ fun _ => rfl
      map_left := fun _ => (one_mul (1 : ℝ)).symm
      map_right := fun _ =>
        (Witnesses.Identity.adjoint_one_apply 1).trans (one_mul (1 : ℝ)).symm }
  have hoss : IsOrderedSingularSystem (I := ({0} : Set ℕ))
      (1 : ℝ →L[ℝ] ℝ) (fun _ => 1) (fun _ => 1) (fun _ => 1) :=
    { hss with
      isLowerSet := fun m n hn hmn => by
        rw [Set.mem_singleton_iff] at hn ⊢
        omega
      antitone := fun _ _ _ => le_rfl
      tendsto_zero := fun h => ((Set.finite_singleton 0).not_infinite h).elim }
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, {0}, fun _ => 1, fun _ => 1, fun _ => 1, ?_⟩
  exact hoss

/-- The hypotheses of `AutoIp.IsModeratelyIllPosed` can fail. -/
theorem AutoIp.IsModeratelyIllPosed_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (I : Set ℕ), ∃ (σ : (↑I : Type) → ℝ), ∃ (v : (↑I : Type) → E), ∃ (u : (↑I : Type) → F), ¬ (IsOrderedSingularSystem K σ v u) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Set.univ, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  intro H
  exact absurd (H.pos ⟨0, Set.mem_univ 0⟩) (lt_irrefl 0)

/-- The hypotheses of `AutoIp.IsExponentiallyIllPosed` can hold together. -/
theorem AutoIp.IsExponentiallyIllPosed_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (I : Set ℕ), ∃ (σ : (↑I : Type) → ℝ), ∃ (v : (↑I : Type) → E), ∃ (u : (↑I : Type) → F), IsOrderedSingularSystem K σ v u :=
  by
  classical
  have : Nonempty ↥({0} : Set ℕ) := ⟨⟨0, rfl⟩⟩
  have hss : IsSingularSystem (ι := ↥({0} : Set ℕ)) (1 : ℝ →L[ℝ] ℝ)
      (fun _ => 1) (fun _ => 1) (fun _ => 1) :=
    { pos := fun _ => one_pos
      orthonormal_left := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      orthonormal_right := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      span_left := Witnesses.Identity.span_left _ fun _ => rfl
      span_right := Witnesses.Identity.span_right _ fun _ => rfl
      map_left := fun _ => (one_mul (1 : ℝ)).symm
      map_right := fun _ =>
        (Witnesses.Identity.adjoint_one_apply 1).trans (one_mul (1 : ℝ)).symm }
  have hoss : IsOrderedSingularSystem (I := ({0} : Set ℕ))
      (1 : ℝ →L[ℝ] ℝ) (fun _ => 1) (fun _ => 1) (fun _ => 1) :=
    { hss with
      isLowerSet := fun m n hn hmn => by
        rw [Set.mem_singleton_iff] at hn ⊢
        omega
      antitone := fun _ _ _ => le_rfl
      tendsto_zero := fun h => ((Set.finite_singleton 0).not_infinite h).elim }
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, {0}, fun _ => 1, fun _ => 1, fun _ => 1, ?_⟩
  exact hoss

/-- The hypotheses of `AutoIp.IsExponentiallyIllPosed` can fail. -/
theorem AutoIp.IsExponentiallyIllPosed_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (I : Set ℕ), ∃ (σ : (↑I : Type) → ℝ), ∃ (v : (↑I : Type) → E), ∃ (u : (↑I : Type) → F), ¬ (IsOrderedSingularSystem K σ v u) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Set.univ, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  intro H
  exact absurd (H.pos ⟨0, Set.mem_univ 0⟩) (lt_irrefl 0)
