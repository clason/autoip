module

import AutoIp._part_2_reg._ch_18_discretization._thm_mu_le_sigma.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.iInf_le_singularValue_and_eq_of_singularSpan` can hold together. -/
theorem AutoIp.iInf_le_singularValue_and_eq_of_singularSpan_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (I : Set ℕ), ∃ (σ : (↑I : Type) → ℝ), ∃ (v : (↑I : Type) → E), ∃ (u : (↑I : Type) → F), ∃ (Y : ℕ → Submodule 𝕜 F), ∃ (x16 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (Y n)), ∃ (n : ℕ), ∃ (J : Set ℕ), ∃ (μ : (↑J : Type) → ℝ), ∃ (a : (↑J : Type) → E), ∃ (b : (↑J : Type) → F), (IsOrderedSingularSystem K σ v u) ∧ (Y n ≤ (LinearMap.ker (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K) : F →ₗ[𝕜] E))ᗮ) ∧ ((0 : ℕ) < n) ∧ (Module.finrank 𝕜 ↥(Y n) = n) ∧ (n - (1 : ℕ) ∈ I) ∧ (IsOrderedSingularSystem (Submodule.starProjection (Y n) ∘SL K) μ a b) :=
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
  have hker : (⊤ : Submodule ℝ ℝ) ≤ (LinearMap.ker
      (ContinuousLinearMap.adjoint (1 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ))ᗮ := by
    rw [ContinuousLinearMap.one_def, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.coe_id,
      LinearMap.ker_id, Submodule.bot_orthogonal_eq_top]
  have hfin : Module.finrank ℝ (⊤ : Submodule ℝ ℝ) = 1 := by
    rw [finrank_top, Module.finrank_self]
  have hss' := hss (K := (⊤ : Submodule ℝ ℝ).starProjection ∘L (1 : ℝ →L[ℝ] ℝ))
    (by rw [Submodule.starProjection_top, ContinuousLinearMap.id_comp])
  have hspan : (⊤ : Submodule ℝ ℝ) = Submodule.span ℝ ((fun _ : (↑({0} : Set ℕ) : Type) =>
      (1 : ℝ)) '' {i | (i : ℕ) < 1}) :=
    (Submodule.eq_top_iff'.2 fun x => (mul_one x) ▸ Submodule.smul_mem _ x
      (Submodule.subset_span ⟨⟨0, rfl⟩, Nat.zero_lt_one, rfl⟩)).symm
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, {0}, fun _ => 1, fun _ => 1, fun _ => 1, fun _ => ⊤,
    fun _ => inferInstance, 1, {0}, fun _ => 1, fun _ => 1, fun _ => 1, ?_⟩
  exact ⟨hss rfl, hker, Nat.zero_lt_one, hfin, rfl, hss'⟩

/-- The hypotheses of `AutoIp.iInf_le_singularValue_and_eq_of_singularSpan` can fail. -/
theorem AutoIp.iInf_le_singularValue_and_eq_of_singularSpan_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (I : Set ℕ), ∃ (σ : (↑I : Type) → ℝ), ∃ (v : (↑I : Type) → E), ∃ (u : (↑I : Type) → F), ∃ (Y : ℕ → Submodule 𝕜 F), ∃ (x16 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (Y n)), ∃ (n : ℕ), ∃ (J : Set ℕ), ∃ (μ : (↑J : Type) → ℝ), ∃ (a : (↑J : Type) → E), ∃ (b : (↑J : Type) → F), ¬ ((IsOrderedSingularSystem K σ v u) ∧ (Y n ≤ (LinearMap.ker (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K) : F →ₗ[𝕜] E))ᗮ) ∧ ((0 : ℕ) < n) ∧ (Module.finrank 𝕜 ↥(Y n) = n) ∧ (n - (1 : ℕ) ∈ I) ∧ (IsOrderedSingularSystem (Submodule.starProjection (Y n) ∘SL K) μ a b)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Set.univ, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => ⊥,
    fun _ => inferInstance, 1, ∅, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  rintro ⟨H, _, _, _, _, _⟩
  exact absurd (H.pos ⟨0, Set.mem_univ 0⟩) (lt_irrefl 0)

/-- The hypotheses of `AutoIp.iInf_le_singularValue` can hold together. -/
theorem AutoIp.iInf_le_singularValue_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (I : Set ℕ), ∃ (σ : (↑I : Type) → ℝ), ∃ (v : (↑I : Type) → E), ∃ (u : (↑I : Type) → F), ∃ (Y : ℕ → Submodule 𝕜 F), ∃ (x16 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (Y n)), ∃ (n : ℕ), ∃ (J : Set ℕ), ∃ (μ : (↑J : Type) → ℝ), ∃ (a : (↑J : Type) → E), ∃ (b : (↑J : Type) → F), (IsOrderedSingularSystem K σ v u) ∧ (Y n ≤ (LinearMap.ker (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K) : F →ₗ[𝕜] E))ᗮ) ∧ ((0 : ℕ) < n) ∧ (Module.finrank 𝕜 ↥(Y n) = n) ∧ (n - (1 : ℕ) ∈ I) ∧ (IsOrderedSingularSystem (Submodule.starProjection (Y n) ∘SL K) μ a b) :=
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
  have hker : (⊤ : Submodule ℝ ℝ) ≤ (LinearMap.ker
      (ContinuousLinearMap.adjoint (1 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ))ᗮ := by
    rw [ContinuousLinearMap.one_def, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.coe_id,
      LinearMap.ker_id, Submodule.bot_orthogonal_eq_top]
  have hfin : Module.finrank ℝ (⊤ : Submodule ℝ ℝ) = 1 := by
    rw [finrank_top, Module.finrank_self]
  have hss' := hss (K := (⊤ : Submodule ℝ ℝ).starProjection ∘L (1 : ℝ →L[ℝ] ℝ))
    (by rw [Submodule.starProjection_top, ContinuousLinearMap.id_comp])
  have hspan : (⊤ : Submodule ℝ ℝ) = Submodule.span ℝ ((fun _ : (↑({0} : Set ℕ) : Type) =>
      (1 : ℝ)) '' {i | (i : ℕ) < 1}) :=
    (Submodule.eq_top_iff'.2 fun x => (mul_one x) ▸ Submodule.smul_mem _ x
      (Submodule.subset_span ⟨⟨0, rfl⟩, Nat.zero_lt_one, rfl⟩)).symm
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, {0}, fun _ => 1, fun _ => 1, fun _ => 1, fun _ => ⊤,
    fun _ => inferInstance, 1, {0}, fun _ => 1, fun _ => 1, fun _ => 1, ?_⟩
  exact ⟨hss rfl, hker, Nat.zero_lt_one, hfin, rfl, hss'⟩

/-- The hypotheses of `AutoIp.iInf_le_singularValue` can fail. -/
theorem AutoIp.iInf_le_singularValue_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (I : Set ℕ), ∃ (σ : (↑I : Type) → ℝ), ∃ (v : (↑I : Type) → E), ∃ (u : (↑I : Type) → F), ∃ (Y : ℕ → Submodule 𝕜 F), ∃ (x16 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (Y n)), ∃ (n : ℕ), ∃ (J : Set ℕ), ∃ (μ : (↑J : Type) → ℝ), ∃ (a : (↑J : Type) → E), ∃ (b : (↑J : Type) → F), ¬ ((IsOrderedSingularSystem K σ v u) ∧ (Y n ≤ (LinearMap.ker (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K) : F →ₗ[𝕜] E))ᗮ) ∧ ((0 : ℕ) < n) ∧ (Module.finrank 𝕜 ↥(Y n) = n) ∧ (n - (1 : ℕ) ∈ I) ∧ (IsOrderedSingularSystem (Submodule.starProjection (Y n) ∘SL K) μ a b)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Set.univ, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => ⊥,
    fun _ => inferInstance, 1, ∅, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  rintro ⟨H, _, _, _, _, _⟩
  exact absurd (H.pos ⟨0, Set.mem_univ 0⟩) (lt_irrefl 0)

/-- The hypotheses of `AutoIp.iInf_eq_singularValue_of_singularSpan` can hold together. -/
theorem AutoIp.iInf_eq_singularValue_of_singularSpan_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (I : Set ℕ), ∃ (σ : (↑I : Type) → ℝ), ∃ (v : (↑I : Type) → E), ∃ (u : (↑I : Type) → F), ∃ (Y : ℕ → Submodule 𝕜 F), ∃ (x16 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (Y n)), ∃ (n : ℕ), ∃ (J : Set ℕ), ∃ (μ : (↑J : Type) → ℝ), ∃ (a : (↑J : Type) → E), ∃ (b : (↑J : Type) → F), (IsOrderedSingularSystem K σ v u) ∧ (Y n ≤ (LinearMap.ker (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K) : F →ₗ[𝕜] E))ᗮ) ∧ ((0 : ℕ) < n) ∧ (Module.finrank 𝕜 ↥(Y n) = n) ∧ (n - (1 : ℕ) ∈ I) ∧ (IsOrderedSingularSystem (Submodule.starProjection (Y n) ∘SL K) μ a b) ∧ (Y n = Submodule.span 𝕜 (u '' {i : (↑I : Type) | (↑i : ℕ) < n})) :=
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
  have hker : (⊤ : Submodule ℝ ℝ) ≤ (LinearMap.ker
      (ContinuousLinearMap.adjoint (1 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ))ᗮ := by
    rw [ContinuousLinearMap.one_def, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.coe_id,
      LinearMap.ker_id, Submodule.bot_orthogonal_eq_top]
  have hfin : Module.finrank ℝ (⊤ : Submodule ℝ ℝ) = 1 := by
    rw [finrank_top, Module.finrank_self]
  have hss' := hss (K := (⊤ : Submodule ℝ ℝ).starProjection ∘L (1 : ℝ →L[ℝ] ℝ))
    (by rw [Submodule.starProjection_top, ContinuousLinearMap.id_comp])
  have hspan : (⊤ : Submodule ℝ ℝ) = Submodule.span ℝ ((fun _ : (↑({0} : Set ℕ) : Type) =>
      (1 : ℝ)) '' {i | (i : ℕ) < 1}) :=
    (Submodule.eq_top_iff'.2 fun x => (mul_one x) ▸ Submodule.smul_mem _ x
      (Submodule.subset_span ⟨⟨0, rfl⟩, Nat.zero_lt_one, rfl⟩)).symm
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, {0}, fun _ => 1, fun _ => 1, fun _ => 1, fun _ => ⊤,
    fun _ => inferInstance, 1, {0}, fun _ => 1, fun _ => 1, fun _ => 1, ?_⟩
  exact ⟨hss rfl, hker, Nat.zero_lt_one, hfin, rfl, hss', hspan⟩

/-- The hypotheses of `AutoIp.iInf_eq_singularValue_of_singularSpan` can fail. -/
theorem AutoIp.iInf_eq_singularValue_of_singularSpan_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (I : Set ℕ), ∃ (σ : (↑I : Type) → ℝ), ∃ (v : (↑I : Type) → E), ∃ (u : (↑I : Type) → F), ∃ (Y : ℕ → Submodule 𝕜 F), ∃ (x16 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (Y n)), ∃ (n : ℕ), ∃ (J : Set ℕ), ∃ (μ : (↑J : Type) → ℝ), ∃ (a : (↑J : Type) → E), ∃ (b : (↑J : Type) → F), ¬ ((IsOrderedSingularSystem K σ v u) ∧ (Y n ≤ (LinearMap.ker (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K) : F →ₗ[𝕜] E))ᗮ) ∧ ((0 : ℕ) < n) ∧ (Module.finrank 𝕜 ↥(Y n) = n) ∧ (n - (1 : ℕ) ∈ I) ∧ (IsOrderedSingularSystem (Submodule.starProjection (Y n) ∘SL K) μ a b) ∧ (Y n = Submodule.span 𝕜 (u '' {i : (↑I : Type) | (↑i : ℕ) < n}))) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Set.univ, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => ⊥,
    fun _ => inferInstance, 1, ∅, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  rintro ⟨H, _, _, _, _, _, _⟩
  exact absurd (H.pos ⟨0, Set.mem_univ 0⟩) (lt_irrefl 0)
