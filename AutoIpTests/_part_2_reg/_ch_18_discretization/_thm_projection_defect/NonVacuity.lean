module

import AutoIp._part_2_reg._ch_18_discretization._thm_projection_defect.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.le_norm_id_sub_starProjection_comp_adjoint_and_eq_of_singularSpan` can hold together. -/
theorem AutoIp.le_norm_id_sub_starProjection_comp_adjoint_and_eq_of_singularSpan_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (I : Set ℕ), ∃ (σ : (↑I : Type) → ℝ), ∃ (v : (↑I : Type) → E), ∃ (u : (↑I : Type) → F), ∃ (Y : ℕ → Submodule 𝕜 F), ∃ (X : ℕ → Submodule 𝕜 E), ∃ (x17 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (X n)), ∃ (n : ℕ), ∃ (x19 : FiniteDimensional 𝕜 ↥(Y n)), (IsOrderedSingularSystem K σ v u) ∧ (X n = Submodule.map (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K) : F →ₗ[𝕜] E) (Y n)) ∧ (Module.finrank 𝕜 ↥(Y n) = n) ∧ (n ∈ I) :=
  by
  have hsub1 : ∀ {i j : (↑({0} : Set ℕ) : Type)}, i ≠ j → False := fun {i j} hij =>
    hij (Subtype.ext (i.2.trans j.2.symm))
  have hss : ∀ {K : ℝ →L[ℝ] ℝ}, K = 1 → IsOrderedSingularSystem (I := ({0} : Set ℕ)) K
      (fun _ => 1) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) := by
    rintro K rfl
    exact
    { pos := fun _ => one_pos
      orthonormal_left := ⟨fun _ => norm_one, fun _ _ hij => (hsub1 hij).elim⟩
      orthonormal_right := ⟨fun _ => norm_one, fun _ _ hij => (hsub1 hij).elim⟩
      span_left := Witnesses.Identity.span_left _ (fun _ => rfl)
      span_right := Witnesses.Identity.span_right _ (fun _ => rfl)
      map_left := fun _ => by simp
      map_right := fun _ => by rw [Witnesses.Identity.adjoint_one_apply]; simp
      isLowerSet := fun m n hn hmn => by
        have : n = 0 := hn
        show m = 0
        omega
      antitone := fun _ _ _ => le_rfl
      tendsto_zero := fun h => ((Set.finite_singleton 0).not_infinite h).elim }
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, {0}, fun _ => 1, fun _ => 1, fun _ => 1, fun _ => ⊥,
    fun _ => ⊥, fun _ => inferInstance, 0, inferInstance, ?_⟩
  exact ⟨hss rfl, (Submodule.map_bot _).symm, finrank_bot ℝ ℝ, rfl⟩

/-- The hypotheses of `AutoIp.le_norm_id_sub_starProjection_comp_adjoint_and_eq_of_singularSpan` can fail. -/
theorem AutoIp.le_norm_id_sub_starProjection_comp_adjoint_and_eq_of_singularSpan_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (I : Set ℕ), ∃ (σ : (↑I : Type) → ℝ), ∃ (v : (↑I : Type) → E), ∃ (u : (↑I : Type) → F), ∃ (Y : ℕ → Submodule 𝕜 F), ∃ (X : ℕ → Submodule 𝕜 E), ∃ (x17 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (X n)), ∃ (n : ℕ), ∃ (x19 : FiniteDimensional 𝕜 ↥(Y n)), ¬ ((IsOrderedSingularSystem K σ v u) ∧ (X n = Submodule.map (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K) : F →ₗ[𝕜] E) (Y n)) ∧ (Module.finrank 𝕜 ↥(Y n) = n) ∧ (n ∈ I)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Set.univ, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => ⊥,
    fun _ => ⊥, fun _ => inferInstance, 0, inferInstance, ?_⟩
  rintro ⟨H, _⟩
  exact absurd (H.pos ⟨0, Set.mem_univ 0⟩) (lt_irrefl 0)

/-- The hypotheses of `AutoIp.le_norm_id_sub_starProjection_comp_adjoint` can hold together. -/
theorem AutoIp.le_norm_id_sub_starProjection_comp_adjoint_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (I : Set ℕ), ∃ (σ : (↑I : Type) → ℝ), ∃ (v : (↑I : Type) → E), ∃ (u : (↑I : Type) → F), ∃ (Y : ℕ → Submodule 𝕜 F), ∃ (X : ℕ → Submodule 𝕜 E), ∃ (x17 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (X n)), ∃ (n : ℕ), ∃ (x19 : FiniteDimensional 𝕜 ↥(Y n)), (IsOrderedSingularSystem K σ v u) ∧ (X n = Submodule.map (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K) : F →ₗ[𝕜] E) (Y n)) ∧ (Module.finrank 𝕜 ↥(Y n) = n) ∧ (n ∈ I) :=
  by
  have hsub1 : ∀ {i j : (↑({0} : Set ℕ) : Type)}, i ≠ j → False := fun {i j} hij =>
    hij (Subtype.ext (i.2.trans j.2.symm))
  have hss : ∀ {K : ℝ →L[ℝ] ℝ}, K = 1 → IsOrderedSingularSystem (I := ({0} : Set ℕ)) K
      (fun _ => 1) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) := by
    rintro K rfl
    exact
    { pos := fun _ => one_pos
      orthonormal_left := ⟨fun _ => norm_one, fun _ _ hij => (hsub1 hij).elim⟩
      orthonormal_right := ⟨fun _ => norm_one, fun _ _ hij => (hsub1 hij).elim⟩
      span_left := Witnesses.Identity.span_left _ (fun _ => rfl)
      span_right := Witnesses.Identity.span_right _ (fun _ => rfl)
      map_left := fun _ => by simp
      map_right := fun _ => by rw [Witnesses.Identity.adjoint_one_apply]; simp
      isLowerSet := fun m n hn hmn => by
        have : n = 0 := hn
        show m = 0
        omega
      antitone := fun _ _ _ => le_rfl
      tendsto_zero := fun h => ((Set.finite_singleton 0).not_infinite h).elim }
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, {0}, fun _ => 1, fun _ => 1, fun _ => 1, fun _ => ⊥,
    fun _ => ⊥, fun _ => inferInstance, 0, inferInstance, ?_⟩
  exact ⟨hss rfl, (Submodule.map_bot _).symm, finrank_bot ℝ ℝ, rfl⟩

/-- The hypotheses of `AutoIp.le_norm_id_sub_starProjection_comp_adjoint` can fail. -/
theorem AutoIp.le_norm_id_sub_starProjection_comp_adjoint_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (I : Set ℕ), ∃ (σ : (↑I : Type) → ℝ), ∃ (v : (↑I : Type) → E), ∃ (u : (↑I : Type) → F), ∃ (Y : ℕ → Submodule 𝕜 F), ∃ (X : ℕ → Submodule 𝕜 E), ∃ (x17 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (X n)), ∃ (n : ℕ), ∃ (x19 : FiniteDimensional 𝕜 ↥(Y n)), ¬ ((IsOrderedSingularSystem K σ v u) ∧ (X n = Submodule.map (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K) : F →ₗ[𝕜] E) (Y n)) ∧ (Module.finrank 𝕜 ↥(Y n) = n) ∧ (n ∈ I)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Set.univ, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => ⊥,
    fun _ => ⊥, fun _ => inferInstance, 0, inferInstance, ?_⟩
  rintro ⟨H, _⟩
  exact absurd (H.pos ⟨0, Set.mem_univ 0⟩) (lt_irrefl 0)

/-- The hypotheses of `AutoIp.norm_id_sub_starProjection_comp_adjoint_eq_of_singularSpan` can hold together. -/
theorem AutoIp.norm_id_sub_starProjection_comp_adjoint_eq_of_singularSpan_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (I : Set ℕ), ∃ (σ : (↑I : Type) → ℝ), ∃ (v : (↑I : Type) → E), ∃ (u : (↑I : Type) → F), ∃ (Y : ℕ → Submodule 𝕜 F), ∃ (X : ℕ → Submodule 𝕜 E), ∃ (x17 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (X n)), ∃ (n : ℕ), ∃ (x19 : FiniteDimensional 𝕜 ↥(Y n)), (IsOrderedSingularSystem K σ v u) ∧ (X n = Submodule.map (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K) : F →ₗ[𝕜] E) (Y n)) ∧ (Module.finrank 𝕜 ↥(Y n) = n) ∧ (n ∈ I) ∧ (Y n = Submodule.span 𝕜 (u '' {i : (↑I : Type) | (↑i : ℕ) < n})) :=
  by
  have hsub1 : ∀ {i j : (↑({0} : Set ℕ) : Type)}, i ≠ j → False := fun {i j} hij =>
    hij (Subtype.ext (i.2.trans j.2.symm))
  have hss : ∀ {K : ℝ →L[ℝ] ℝ}, K = 1 → IsOrderedSingularSystem (I := ({0} : Set ℕ)) K
      (fun _ => 1) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) := by
    rintro K rfl
    exact
    { pos := fun _ => one_pos
      orthonormal_left := ⟨fun _ => norm_one, fun _ _ hij => (hsub1 hij).elim⟩
      orthonormal_right := ⟨fun _ => norm_one, fun _ _ hij => (hsub1 hij).elim⟩
      span_left := Witnesses.Identity.span_left _ (fun _ => rfl)
      span_right := Witnesses.Identity.span_right _ (fun _ => rfl)
      map_left := fun _ => by simp
      map_right := fun _ => by rw [Witnesses.Identity.adjoint_one_apply]; simp
      isLowerSet := fun m n hn hmn => by
        have : n = 0 := hn
        show m = 0
        omega
      antitone := fun _ _ _ => le_rfl
      tendsto_zero := fun h => ((Set.finite_singleton 0).not_infinite h).elim }
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, {0}, fun _ => 1, fun _ => 1, fun _ => 1, fun _ => ⊥,
    fun _ => ⊥, fun _ => inferInstance, 0, inferInstance, ?_⟩
  exact ⟨hss rfl, (Submodule.map_bot _).symm, finrank_bot ℝ ℝ, rfl, by simp⟩

/-- The hypotheses of `AutoIp.norm_id_sub_starProjection_comp_adjoint_eq_of_singularSpan` can fail. -/
theorem AutoIp.norm_id_sub_starProjection_comp_adjoint_eq_of_singularSpan_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (I : Set ℕ), ∃ (σ : (↑I : Type) → ℝ), ∃ (v : (↑I : Type) → E), ∃ (u : (↑I : Type) → F), ∃ (Y : ℕ → Submodule 𝕜 F), ∃ (X : ℕ → Submodule 𝕜 E), ∃ (x17 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (X n)), ∃ (n : ℕ), ∃ (x19 : FiniteDimensional 𝕜 ↥(Y n)), ¬ ((IsOrderedSingularSystem K σ v u) ∧ (X n = Submodule.map (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K) : F →ₗ[𝕜] E) (Y n)) ∧ (Module.finrank 𝕜 ↥(Y n) = n) ∧ (n ∈ I) ∧ (Y n = Submodule.span 𝕜 (u '' {i : (↑I : Type) | (↑i : ℕ) < n}))) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Set.univ, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => ⊥,
    fun _ => ⊥, fun _ => inferInstance, 0, inferInstance, ?_⟩
  rintro ⟨H, _⟩
  exact absurd (H.pos ⟨0, Set.mem_univ 0⟩) (lt_irrefl 0)
