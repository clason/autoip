module

import AutoIp._part_2_reg._ch_18_discretization._cor_dual_lsq_best_rate.Spec -- shake: keep
import AutoIpTests.Witnesses.Filtration
import AutoIpTests.Witnesses.Identity

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.dualLsq_norm_sub_le_of_singularSpan` can hold together. -/
theorem AutoIp.dualLsq_norm_sub_le_of_singularSpan_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (I : Set ℕ), ∃ (σ : (↑I : Type) → ℝ), ∃ (v : (↑I : Type) → E), ∃ (u : (↑I : Type) → F), ∃ (Y : ℕ → Submodule 𝕜 F), ∃ (x16 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (Y n)), ∃ (X : ℕ → Submodule 𝕜 E), ∃ (x18 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (X n)), ∃ (hmono : Monotone Y), ∃ (hfin : ∀ (n : ℕ), Module.finrank 𝕜 ↥(Y n) = n), ∃ (μ : ℕ → ℝ), ∃ (y : F), ∃ (hy : y ∈ AutoIp.mpDomain K), ∃ (w : F), ∃ (δ : ℝ), ∃ (z : F), ∃ (n : ℕ), (IsOrderedSingularSystem K σ v u) ∧ (∀ (n : ℕ), (0 : ℕ) < n → ‖AutoIp.moorePenroseL (AutoIp.isClosed_range_dualLsq K Y hmono hfin n)‖ = (μ n)⁻¹) ∧ ((↑(AutoIp.moorePenrose K) : ↥(LinearPMap.domain (AutoIp.moorePenrose K)) → E) ⟨y, hy⟩ =
  ((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K : F → E) w) ∧ (‖y - z‖ ≤ δ) ∧ (X n = Submodule.map (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K) : F →ₗ[𝕜] E) (Y n)) ∧ (Y n ≤ (LinearMap.ker (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K) : F →ₗ[𝕜] E))ᗮ) ∧ ((0 : ℕ) < n) :=
  by
  classical
  have hb0 : Witnesses.Filtration.b 0 ≠ 0 := Witnesses.Filtration.b.orthonormal.ne_zero 0
  have hsub1 : ∀ {i j : (↑({0} : Set ℕ) : Type)}, i ≠ j → False := fun {i j} hij =>
    hij (Subtype.ext (i.2.trans j.2.symm))
  have hker : LinearMap.ker (Witnesses.Filtration.K : ℝ →ₗ[ℝ] Witnesses.Filtration.H) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun r hr => ?_
    rw [ContinuousLinearMap.coe_coe, Witnesses.Filtration.K_apply] at hr
    exact (smul_eq_zero.1 hr).resolve_right hb0
  have hrange : Submodule.span ℝ (Set.range fun _ : (↑({0} : Set ℕ) : Type) =>
      Witnesses.Filtration.b 0) =
      LinearMap.range (Witnesses.Filtration.K : ℝ →ₗ[ℝ] Witnesses.Filtration.H) := by
    refine le_antisymm (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨_, rfl⟩
      exact ⟨1, by rw [ContinuousLinearMap.coe_coe, Witnesses.Filtration.K_apply, one_smul]⟩
    · rintro _ ⟨r, rfl⟩
      rw [ContinuousLinearMap.coe_coe, Witnesses.Filtration.K_apply]
      exact Submodule.smul_mem _ r (Submodule.subset_span ⟨⟨0, rfl⟩, rfl⟩)
  have hss : IsOrderedSingularSystem (I := ({0} : Set ℕ)) Witnesses.Filtration.K
      (fun _ => 1) (fun _ => (1 : ℝ)) (fun _ => Witnesses.Filtration.b 0) :=
    { pos := fun _ => one_pos
      orthonormal_left := ⟨fun _ => norm_one, fun _ _ hij => (hsub1 hij).elim⟩
      orthonormal_right :=
        ⟨fun _ => Witnesses.Filtration.b.orthonormal.1 0, fun _ _ hij => (hsub1 hij).elim⟩
      span_left := by
        rw [Witnesses.Identity.span_range_eq_top (ι := (↑({0} : Set ℕ) : Type))
          (fun _ => (1 : ℝ)) (fun _ => rfl), hker, Submodule.bot_orthogonal_eq_top]
        exact le_antisymm le_top (Submodule.le_topologicalClosure _)
      span_right := by rw [hrange]
      map_left := fun _ => by
        rw [Witnesses.Filtration.K_apply]
        simp
      map_right := fun _ => by
        rw [Witnesses.Filtration.adjoint_K_apply, Witnesses.Filtration.inner_b_zero_self]
        simp
      isLowerSet := fun m n hn hmn => by
        have : n = 0 := hn
        show m = 0
        omega
      antitone := fun _ _ _ => le_rfl
      tendsto_zero := fun h => ((Set.finite_singleton 0).not_infinite h).elim }
  refine ⟨ℝ, inferInstance, ℝ, Witnesses.Filtration.H, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, Witnesses.Filtration.K, {0},
    fun _ => 1, fun _ => 1, fun _ => Witnesses.Filtration.b 0, Witnesses.Filtration.X,
    fun _ => inferInstance,
    fun m => Submodule.map (ContinuousLinearMap.adjoint Witnesses.Filtration.K :
      Witnesses.Filtration.H →ₗ[ℝ] ℝ) (Witnesses.Filtration.X m),
    fun _ => inferInstance, Witnesses.Filtration.mono, Witnesses.Filtration.finrank_X,
    fun n => ‖AutoIp.moorePenroseL (AutoIp.isClosed_range_dualLsq Witnesses.Filtration.K
      Witnesses.Filtration.X Witnesses.Filtration.mono Witnesses.Filtration.finrank_X n)‖⁻¹,
    0, Submodule.zero_mem _, 0, 0, 0, 1, hss, fun n _ => (inv_inv _).symm, ?_, by simp, rfl,
    ?_, one_pos⟩
  · rw [map_zero]
    exact (AutoIp.moorePenrose _).map_zero
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal]
    intro x hx
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      Witnesses.Filtration.adjoint_K_apply] at hx
    rw [Fin.fin_one_eq_zero i, real_inner_comm]
    exact hx

/-- The hypotheses of `AutoIp.dualLsq_norm_sub_le_of_singularSpan` can fail. -/
theorem AutoIp.dualLsq_norm_sub_le_of_singularSpan_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (I : Set ℕ), ∃ (σ : (↑I : Type) → ℝ), ∃ (v : (↑I : Type) → E), ∃ (u : (↑I : Type) → F), ∃ (Y : ℕ → Submodule 𝕜 F), ∃ (x16 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (Y n)), ∃ (X : ℕ → Submodule 𝕜 E), ∃ (x18 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (X n)), ∃ (hmono : Monotone Y), ∃ (hfin : ∀ (n : ℕ), Module.finrank 𝕜 ↥(Y n) = n), ∃ (μ : ℕ → ℝ), ∃ (y : F), ∃ (hy : y ∈ AutoIp.mpDomain K), ∃ (w : F), ∃ (δ : ℝ), ∃ (z : F), ∃ (n : ℕ), ¬ ((IsOrderedSingularSystem K σ v u) ∧ (∀ (n : ℕ), (0 : ℕ) < n → ‖AutoIp.moorePenroseL (AutoIp.isClosed_range_dualLsq K Y hmono hfin n)‖ = (μ n)⁻¹) ∧ ((↑(AutoIp.moorePenrose K) : ↥(LinearPMap.domain (AutoIp.moorePenrose K)) → E) ⟨y, hy⟩ =
  ((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K : F → E) w) ∧ (‖y - z‖ ≤ δ) ∧ (X n = Submodule.map (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K) : F →ₗ[𝕜] E) (Y n)) ∧ (Y n ≤ (LinearMap.ker (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K) : F →ₗ[𝕜] E))ᗮ) ∧ ((0 : ℕ) < n)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, Witnesses.Filtration.H, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, 0, ∅,
    fun _ => 1, fun _ => 1, fun _ => 0, Witnesses.Filtration.X,
    fun _ => inferInstance, fun _ => ⊥, fun _ => inferInstance, Witnesses.Filtration.mono,
    Witnesses.Filtration.finrank_X, fun _ => 1, 0, Submodule.zero_mem _, 0, 0, 0, 0, ?_⟩
  exact fun h => lt_irrefl 0 h.2.2.2.2.2.2

/-- The hypotheses of `AutoIp.dualLsq_mu_le_and_le_norm_id_sub_starProjection` can hold together. -/
theorem AutoIp.dualLsq_mu_le_and_le_norm_id_sub_starProjection_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (I : Set ℕ), ∃ (σ : (↑I : Type) → ℝ), ∃ (v : (↑I : Type) → E), ∃ (u : (↑I : Type) → F), ∃ (Y : ℕ → Submodule 𝕜 F), ∃ (x16 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (Y n)), ∃ (X : ℕ → Submodule 𝕜 E), ∃ (x18 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (X n)), ∃ (hmono : Monotone Y), ∃ (hfin : ∀ (n : ℕ), Module.finrank 𝕜 ↥(Y n) = n), ∃ (μ : ℕ → ℝ), ∃ (n : ℕ), (IsOrderedSingularSystem K σ v u) ∧ (∀ (n : ℕ), (0 : ℕ) < n → ‖AutoIp.moorePenroseL (AutoIp.isClosed_range_dualLsq K Y hmono hfin n)‖ = (μ n)⁻¹) ∧ (X n = Submodule.map (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K) : F →ₗ[𝕜] E) (Y n)) ∧ (Y n ≤ (LinearMap.ker (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K) : F →ₗ[𝕜] E))ᗮ) ∧ ((0 : ℕ) < n) :=
  by
  classical
  have hb0 : Witnesses.Filtration.b 0 ≠ 0 := Witnesses.Filtration.b.orthonormal.ne_zero 0
  have hsub1 : ∀ {i j : (↑({0} : Set ℕ) : Type)}, i ≠ j → False := fun {i j} hij =>
    hij (Subtype.ext (i.2.trans j.2.symm))
  have hker : LinearMap.ker (Witnesses.Filtration.K : ℝ →ₗ[ℝ] Witnesses.Filtration.H) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun r hr => ?_
    rw [ContinuousLinearMap.coe_coe, Witnesses.Filtration.K_apply] at hr
    exact (smul_eq_zero.1 hr).resolve_right hb0
  have hrange : Submodule.span ℝ (Set.range fun _ : (↑({0} : Set ℕ) : Type) =>
      Witnesses.Filtration.b 0) =
      LinearMap.range (Witnesses.Filtration.K : ℝ →ₗ[ℝ] Witnesses.Filtration.H) := by
    refine le_antisymm (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨_, rfl⟩
      exact ⟨1, by rw [ContinuousLinearMap.coe_coe, Witnesses.Filtration.K_apply, one_smul]⟩
    · rintro _ ⟨r, rfl⟩
      rw [ContinuousLinearMap.coe_coe, Witnesses.Filtration.K_apply]
      exact Submodule.smul_mem _ r (Submodule.subset_span ⟨⟨0, rfl⟩, rfl⟩)
  have hss : IsOrderedSingularSystem (I := ({0} : Set ℕ)) Witnesses.Filtration.K
      (fun _ => 1) (fun _ => (1 : ℝ)) (fun _ => Witnesses.Filtration.b 0) :=
    { pos := fun _ => one_pos
      orthonormal_left := ⟨fun _ => norm_one, fun _ _ hij => (hsub1 hij).elim⟩
      orthonormal_right :=
        ⟨fun _ => Witnesses.Filtration.b.orthonormal.1 0, fun _ _ hij => (hsub1 hij).elim⟩
      span_left := by
        rw [Witnesses.Identity.span_range_eq_top (ι := (↑({0} : Set ℕ) : Type))
          (fun _ => (1 : ℝ)) (fun _ => rfl), hker, Submodule.bot_orthogonal_eq_top]
        exact le_antisymm le_top (Submodule.le_topologicalClosure _)
      span_right := by rw [hrange]
      map_left := fun _ => by
        rw [Witnesses.Filtration.K_apply]
        simp
      map_right := fun _ => by
        rw [Witnesses.Filtration.adjoint_K_apply, Witnesses.Filtration.inner_b_zero_self]
        simp
      isLowerSet := fun m n hn hmn => by
        have : n = 0 := hn
        show m = 0
        omega
      antitone := fun _ _ _ => le_rfl
      tendsto_zero := fun h => ((Set.finite_singleton 0).not_infinite h).elim }
  refine ⟨ℝ, inferInstance, ℝ, Witnesses.Filtration.H, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, Witnesses.Filtration.K, {0},
    fun _ => 1, fun _ => 1, fun _ => Witnesses.Filtration.b 0, Witnesses.Filtration.X,
    fun _ => inferInstance,
    fun m => Submodule.map (ContinuousLinearMap.adjoint Witnesses.Filtration.K :
      Witnesses.Filtration.H →ₗ[ℝ] ℝ) (Witnesses.Filtration.X m),
    fun _ => inferInstance, Witnesses.Filtration.mono, Witnesses.Filtration.finrank_X,
    fun n => ‖AutoIp.moorePenroseL (AutoIp.isClosed_range_dualLsq Witnesses.Filtration.K
      Witnesses.Filtration.X Witnesses.Filtration.mono Witnesses.Filtration.finrank_X n)‖⁻¹,
    1, hss, fun n _ => (inv_inv _).symm, rfl, ?_, one_pos⟩
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_orthogonal]
  intro x hx
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    Witnesses.Filtration.adjoint_K_apply] at hx
  rw [Fin.fin_one_eq_zero i, real_inner_comm]
  exact hx

/-- The hypotheses of `AutoIp.dualLsq_mu_le_and_le_norm_id_sub_starProjection` can fail. -/
theorem AutoIp.dualLsq_mu_le_and_le_norm_id_sub_starProjection_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (I : Set ℕ), ∃ (σ : (↑I : Type) → ℝ), ∃ (v : (↑I : Type) → E), ∃ (u : (↑I : Type) → F), ∃ (Y : ℕ → Submodule 𝕜 F), ∃ (x16 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (Y n)), ∃ (X : ℕ → Submodule 𝕜 E), ∃ (x18 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (X n)), ∃ (hmono : Monotone Y), ∃ (hfin : ∀ (n : ℕ), Module.finrank 𝕜 ↥(Y n) = n), ∃ (μ : ℕ → ℝ), ∃ (n : ℕ), ¬ ((IsOrderedSingularSystem K σ v u) ∧ (∀ (n : ℕ), (0 : ℕ) < n → ‖AutoIp.moorePenroseL (AutoIp.isClosed_range_dualLsq K Y hmono hfin n)‖ = (μ n)⁻¹) ∧ (X n = Submodule.map (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K) : F →ₗ[𝕜] E) (Y n)) ∧ (Y n ≤ (LinearMap.ker (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K) : F →ₗ[𝕜] E))ᗮ) ∧ ((0 : ℕ) < n)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, Witnesses.Filtration.H, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, 0, ∅,
    fun _ => 1, fun _ => 1, fun _ => 0, Witnesses.Filtration.X,
    fun _ => inferInstance, fun _ => ⊥, fun _ => inferInstance, Witnesses.Filtration.mono,
    Witnesses.Filtration.finrank_X, fun _ => 1, 0, ?_⟩
  exact fun h => lt_irrefl 0 h.2.2.2.2
