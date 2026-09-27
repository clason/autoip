module

import AutoIp._part_2_reg._ch_18_discretization._thm_dual_lsq_noisy.Spec -- shake: keep
import AutoIpTests.Witnesses.Filtration

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.dualLsq_noisy_convergence` can hold together. -/
theorem AutoIp.dualLsq_noisy_convergence_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (Y : ℕ → Submodule 𝕜 F), ∃ (x12 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (Y n)), ∃ (hmono : Monotone Y), ∃ (hfin : ∀ (n : ℕ), Module.finrank 𝕜 ↥(Y n) = n), ∃ (μ : ℕ → ℝ), ∃ (y : F), ∃ (nd : ℝ → ℕ), ∃ (ε : ℝ), (Submodule.topologicalClosure (⨆ (n : ℕ), Y n) =
  (LinearMap.ker (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) T) : F →ₗ[𝕜] E))ᗮ) ∧ (∀ (n : ℕ), (0 : ℕ) < n → (0 : ℝ) < μ n) ∧ (∀ (n : ℕ), (0 : ℕ) < n → ‖AutoIp.moorePenroseL (AutoIp.isClosed_range_dualLsq T Y hmono hfin n)‖ = (μ n)⁻¹) ∧ (y ∈ AutoIp.mpDomain T) ∧ (Filter.Tendsto (fun (δ : ℝ) => (↑(nd δ) : ℝ)) (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) Filter.atTop) ∧ (Filter.Tendsto (fun (δ : ℝ) => δ / μ (nd δ)) (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (0 : ℝ))) ∧ (ε > (0 : ℝ)) :=
  by
  have hQ : ∀ n, AutoIp.moorePenroseL (AutoIp.isClosed_range_dualLsq
      (ContinuousLinearMap.id ℝ Witnesses.Filtration.H) Witnesses.Filtration.X
      Witnesses.Filtration.mono Witnesses.Filtration.finrank_X n) =
      (Witnesses.Filtration.X n).starProjection := by
    intro n
    refine ContinuousLinearMap.ext fun z => ?_
    rw [AutoIp.moorePenroseL_apply]
    have hk : LinearMap.ker ((Witnesses.Filtration.X n).starProjection ∘L
        ContinuousLinearMap.id ℝ Witnesses.Filtration.H).toLinearMap =
        (Witnesses.Filtration.X n)ᗮ := by
      rw [ContinuousLinearMap.comp_id]
      exact Submodule.ker_starProjection _
    have hr : LinearMap.range ((Witnesses.Filtration.X n).starProjection ∘L
        ContinuousLinearMap.id ℝ Witnesses.Filtration.H).toLinearMap =
        Witnesses.Filtration.X n := by
      rw [ContinuousLinearMap.comp_id]
      exact Submodule.range_starProjection _
    refine (AutoIp.eq_moorePenrose_of_apply_eq_of_eq_zero
      (S := (Witnesses.Filtration.X n).starProjection) (fun a _ b _ => map_add _ a b)
      ?_ ?_ _).symm
    · intro x hx
      rw [hk, Submodule.orthogonal_orthogonal] at hx
      rw [ContinuousLinearMap.comp_id, Submodule.starProjection_eq_self_iff.2 hx,
        Submodule.starProjection_eq_self_iff.2 hx]
    · intro x hx
      rw [hr] at hx
      rw [Submodule.starProjection_apply,
        Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hx, Submodule.coe_zero]
  refine ⟨ℝ, inferInstance, Witnesses.Filtration.H, Witnesses.Filtration.H, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ContinuousLinearMap.id ℝ _, Witnesses.Filtration.X, fun _ => inferInstance,
    Witnesses.Filtration.mono, Witnesses.Filtration.finrank_X, fun _ => 1, 0,
    fun δ => ⌈δ⁻¹⌉₊, 1, ?_, fun _ _ => one_pos, fun n hn => ?_, Submodule.zero_mem _, ?_, ?_,
    one_pos⟩
  · rw [ContinuousLinearMap.adjoint_id, ContinuousLinearMap.coe_id, LinearMap.ker_id,
      Submodule.bot_orthogonal_eq_top]
    exact Witnesses.Filtration.dense
  · rw [hQ, Submodule.norm_starProjection _ (Witnesses.Filtration.X_ne_bot hn), inv_one]
  · exact tendsto_atTop_mono (fun δ => Nat.le_ceil _) tendsto_inv_nhdsGT_zero
  · simp only [div_one]
    exact (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds

/-- The hypotheses of `AutoIp.dualLsq_noisy_convergence` can fail. -/
theorem AutoIp.dualLsq_noisy_convergence_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (Y : ℕ → Submodule 𝕜 F), ∃ (x12 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (Y n)), ∃ (hmono : Monotone Y), ∃ (hfin : ∀ (n : ℕ), Module.finrank 𝕜 ↥(Y n) = n), ∃ (μ : ℕ → ℝ), ∃ (y : F), ∃ (nd : ℝ → ℕ), ∃ (ε : ℝ), ¬ ((Submodule.topologicalClosure (⨆ (n : ℕ), Y n) =
  (LinearMap.ker (↑((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) T) : F →ₗ[𝕜] E))ᗮ) ∧ (∀ (n : ℕ), (0 : ℕ) < n → (0 : ℝ) < μ n) ∧ (∀ (n : ℕ), (0 : ℕ) < n → ‖AutoIp.moorePenroseL (AutoIp.isClosed_range_dualLsq T Y hmono hfin n)‖ = (μ n)⁻¹) ∧ (y ∈ AutoIp.mpDomain T) ∧ (Filter.Tendsto (fun (δ : ℝ) => (↑(nd δ) : ℝ)) (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) Filter.atTop) ∧ (Filter.Tendsto (fun (δ : ℝ) => δ / μ (nd δ)) (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (0 : ℝ))) ∧ (ε > (0 : ℝ))) :=
  by
  refine ⟨ℝ, inferInstance, Witnesses.Filtration.H, Witnesses.Filtration.H, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ContinuousLinearMap.id ℝ _, Witnesses.Filtration.X, fun _ => inferInstance,
    Witnesses.Filtration.mono, Witnesses.Filtration.finrank_X, fun _ => 1, 0,
    fun _ => 0, 0, fun h => lt_irrefl _ h.2.2.2.2.2.2⟩
