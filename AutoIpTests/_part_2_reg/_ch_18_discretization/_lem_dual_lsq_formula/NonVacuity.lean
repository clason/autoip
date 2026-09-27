module

import AutoIp._part_2_reg._ch_18_discretization._lem_dual_lsq_formula.Spec -- shake: keep

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.dualLsqProjection_eq_starProjection` can hold together. -/
theorem AutoIp.dualLsqProjection_eq_starProjection_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (Y : ℕ → Submodule 𝕜 F), ∃ (x12 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (Y n)), ∃ (X : ℕ → Submodule 𝕜 E), ∃ (x14 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (X n)), ∃ (n : ℕ), ∃ (y : F), (X n = Submodule.map (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) T) : F →ₗ[𝕜] E) (Y n)) ∧ (Y n ≤ (LinearMap.ker (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) T) : F →ₗ[𝕜] E))ᗮ) ∧ (y ∈ AutoIp.mpDomain T) ∧ (∀ (m : ℕ), (Submodule.starProjection (Y m) : F → F) y ∈ AutoIp.mpDomain (Submodule.starProjection (Y m) ∘SL T)) :=
  by
  have hker : (⊤ : Submodule ℝ ℝ) ≤ (LinearMap.ker
      (ContinuousLinearMap.adjoint (1 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ))ᗮ := by
    rw [ContinuousLinearMap.one_def, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.coe_id,
      LinearMap.ker_id, Submodule.bot_orthogonal_eq_top]
  have hmap : (⊤ : Submodule ℝ ℝ) = Submodule.map
      (ContinuousLinearMap.adjoint (1 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) ⊤ := by
    rw [ContinuousLinearMap.one_def, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.coe_id,
      Submodule.map_id]
  exact ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, fun _ => ⊤, fun _ => inferInstance, fun _ => ⊤,
    fun _ => inferInstance, 0, 1, hmap, hker, Submodule.mem_sup_left ⟨1, rfl⟩,
    fun _ => Submodule.mem_sup_left ⟨1, by simp⟩⟩

/-- The hypotheses of `AutoIp.dualLsqProjection_eq_starProjection` can fail. -/
theorem AutoIp.dualLsqProjection_eq_starProjection_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (Y : ℕ → Submodule 𝕜 F), ∃ (x12 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (Y n)), ∃ (X : ℕ → Submodule 𝕜 E), ∃ (x14 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (X n)), ∃ (n : ℕ), ∃ (y : F), ¬ ((X n = Submodule.map (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) T) : F →ₗ[𝕜] E) (Y n)) ∧ (Y n ≤ (LinearMap.ker (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) T) : F →ₗ[𝕜] E))ᗮ) ∧ (y ∈ AutoIp.mpDomain T) ∧ (∀ (m : ℕ), (Submodule.starProjection (Y m) : F → F) y ∈ AutoIp.mpDomain (Submodule.starProjection (Y m) ∘SL T))) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, fun _ => ⊥, fun _ => inferInstance, fun _ => ⊤,
    fun _ => inferInstance, 0, 0, ?_⟩
  rintro ⟨h, _⟩
  rw [Submodule.map_bot] at h
  exact top_ne_bot h
