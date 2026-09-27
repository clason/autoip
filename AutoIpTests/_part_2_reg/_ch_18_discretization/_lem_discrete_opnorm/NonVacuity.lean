module

import AutoIp._part_2_reg._ch_18_discretization._lem_discrete_opnorm.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity

open scoped InnerProductSpace

/-- The hypotheses of `AutoIp.opNorm_moorePenroseL_eq_inv_iInf` can hold together. -/
theorem AutoIp.opNorm_moorePenroseL_eq_inv_iInf_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (S : E →L[𝕜] F), ∃ (J : Set ℕ), ∃ (μ : (↑J : Type) → ℝ), ∃ (a : (↑J : Type) → E), ∃ (b : (↑J : Type) → F), (IsClosed (↑(LinearMap.range (↑S : E →ₗ[𝕜] F)) : Set F)) ∧ (IsOrderedSingularSystem S μ a b) :=
  by
  have hsub1 : ∀ {i j : (↑({0} : Set ℕ) : Type)}, i ≠ j → False := fun {i j} hij =>
    hij (Subtype.ext (i.2.trans j.2.symm))
  have hoss : IsOrderedSingularSystem (I := ({0} : Set ℕ)) (1 : ℝ →L[ℝ] ℝ)
      (fun _ => 1) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) :=
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
  have hr : LinearMap.range ((1 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) = ⊤ := LinearMap.range_id
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, {0}, fun _ => 1, fun _ => 1, fun _ => 1, ?_, hoss⟩
  rw [hr, Submodule.top_coe]
  exact isClosed_univ

/-- The hypotheses of `AutoIp.opNorm_moorePenroseL_eq_inv_iInf` can fail. -/
theorem AutoIp.opNorm_moorePenroseL_eq_inv_iInf_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (S : E →L[𝕜] F), ∃ (J : Set ℕ), ∃ (μ : (↑J : Type) → ℝ), ∃ (a : (↑J : Type) → E), ∃ (b : (↑J : Type) → F), ¬ ((IsClosed (↑(LinearMap.range (↑S : E →ₗ[𝕜] F)) : Set F)) ∧ (IsOrderedSingularSystem S μ a b)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Set.univ, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  rintro ⟨_, H⟩
  exact absurd (H.pos ⟨0, Set.mem_univ 0⟩) (lt_irrefl 0)
