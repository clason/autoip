module

import AutoIp._part_2_reg._ch_14_order_optimality._thm_no_uniform_rates.Spec -- shake: keep

open Filter Topology
open scoped ENNReal

/-- The hypotheses of `AutoIp.exists_norm_moorePenrose_le_of_uniform_rate` can hold together. -/
theorem AutoIp.exists_norm_moorePenrose_le_of_uniform_rate_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →ₗ[𝕜] E), ∃ (a : AutoIp.ParameterChoice F), ∃ (ψ : ℝ → ℝ), (∀ t > (0 : ℝ), (0 : ℝ) < ψ t) ∧ (Filter.Tendsto ψ (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (0 : ℝ))) ∧ (∃ δ₀ > (0 : ℝ),
  ∀ (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) δ₀) (y : F) (hy : y ∈ AutoIp.mpDomain T),
    ‖y‖ ≤ (1 : ℝ) →
      AutoIp.worstCaseError T (fun (α : (↑(Set.Ioi (0 : ℝ)) : Type)) (z : F) => (R α : F → E) z) a y hy δ
          (And.left hδ) ≤
        ENNReal.ofReal (ψ δ)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 1, fun α => (1 + (α : ℝ))⁻¹ • LinearMap.id,
    ⟨fun δ _ => (δ : ℝ), fun δ _ => δ.2⟩, fun t => 2 * t,
    fun t ht => by positivity,
    tendsto_nhdsWithin_of_tendsto_nhds (by simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul 2),
    1, one_pos, ?_⟩
  intro δ hδ y hy hy1
  have hmp : AutoIp.moorePenrose (1 : ℝ →L[ℝ] ℝ) ⟨y, hy⟩ = y := by
    have heq := (AutoIp.moorePenrose_isMinimumNorm ⟨y, hy⟩).isLeastSquares y
    simp only [one_apply_eq_self, sub_self, norm_zero] at heq
    exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm heq (norm_nonneg _)))
  unfold AutoIp.worstCaseError
  refine iSup₂_le fun z hz => ?_
  rw [hmp, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  change |(1 + δ)⁻¹ * z - y| ≤ 2 * δ
  have hδ0 : 0 < δ := hδ.1
  rw [Metric.mem_closedBall, Real.dist_eq] at hz
  rw [Real.norm_eq_abs] at hy1
  have key : (1 + δ)⁻¹ * z - y = (1 + δ)⁻¹ * ((z - y) - δ * y) := by
    field_simp
    ring
  calc |(1 + δ)⁻¹ * z - y| = (1 + δ)⁻¹ * |(z - y) - δ * y| := by
        rw [key, abs_mul, abs_of_pos (inv_pos.2 (by linarith))]
    _ ≤ 1 * |(z - y) - δ * y| :=
        mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ (by linarith)) (abs_nonneg _)
    _ ≤ |z - y| + |δ * y| := by rw [one_mul]; exact abs_sub _ _
    _ ≤ δ + δ * 1 := by
        rw [abs_mul, abs_of_pos hδ0]
        nlinarith
    _ = 2 * δ := by ring

/-- The hypotheses of `AutoIp.exists_norm_moorePenrose_le_of_uniform_rate` can fail. -/
theorem AutoIp.exists_norm_moorePenrose_le_of_uniform_rate_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →ₗ[𝕜] E), ∃ (a : AutoIp.ParameterChoice F), ∃ (ψ : ℝ → ℝ), ¬ ((∀ t > (0 : ℝ), (0 : ℝ) < ψ t) ∧ (Filter.Tendsto ψ (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (0 : ℝ))) ∧ (∃ δ₀ > (0 : ℝ),
  ∀ (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) δ₀) (y : F) (hy : y ∈ AutoIp.mpDomain T),
    ‖y‖ ≤ (1 : ℝ) →
      AutoIp.worstCaseError T (fun (α : (↑(Set.Ioi (0 : ℝ)) : Type)) (z : F) => (R α : F → E) z) a y hy δ
          (And.left hδ) ≤
        ENNReal.ofReal (ψ δ))) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 0, 0, ⟨fun _ _ => 1, fun _ _ => one_pos⟩, fun _ => 1, ?_⟩
  rintro ⟨H, _, _⟩
  exact absurd H (by simp_all)
