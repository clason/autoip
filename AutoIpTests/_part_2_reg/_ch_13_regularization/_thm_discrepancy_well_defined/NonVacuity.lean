module

import AutoIp._part_2_reg._ch_13_regularization._thm_discrepancy_well_defined.Spec -- shake: keep

open Filter Topology

/-- The hypotheses of `AutoIp.exists_discrepancy_index` can hold together. -/
theorem AutoIp.exists_discrepancy_index_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), ∃ (α : ℕ → (↑(Set.Ioi (0 : ℝ)) : Type)), ∃ (τ : ℝ), ∃ (δ : ℝ), ∃ (z : F), (AutoIp.IsRegularization T R) ∧ (Dense (↑(LinearMap.range (↑T : E →ₗ[𝕜] F)) : Set F)) ∧ (∃ (C : ℝ), ∀ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ‖T ∘SL R α‖ ≤ C) ∧ (Filter.Tendsto α Filter.atTop Filter.atBot) ∧ ((0 : ℝ) < τ) ∧ ((0 : ℝ) < δ) :=
  by
  let as : ℕ → Set.Ioi (0 : ℝ) := fun n => ⟨1 / ((n : ℝ) + 1), Set.mem_Ioi.2 (by positivity)⟩
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, fun α => (1 + (α : ℝ))⁻¹ • (1 : ℝ →L[ℝ] ℝ),
    as, 1, 1, 1, ?_, ?_, ⟨1, fun α => ?_⟩, ?_, one_pos, one_pos⟩
  · intro y hy
    have hmp : AutoIp.moorePenrose (1 : ℝ →L[ℝ] ℝ) ⟨y, hy⟩ = y := by
      have heq := (AutoIp.moorePenrose_isMinimumNorm ⟨y, hy⟩).isLeastSquares y
      simp only [one_apply_eq_self, sub_self, norm_zero] at heq
      exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm heq (norm_nonneg _)))
    have hc : Tendsto (fun α : Set.Ioi (0 : ℝ) => (α : ℝ)) atBot (𝓝 0) :=
      Metric.tendsto_nhds.2 fun ε hε => Filter.eventually_atBot.2
        ⟨⟨ε / 2, Set.mem_Ioi.2 (by positivity)⟩, fun b hb => by
          have h1 : (b : ℝ) ≤ ε / 2 := hb
          have h2 : (0 : ℝ) < b := b.2
          rw [Real.dist_eq, sub_zero, abs_of_pos h2]
          linarith⟩
    have ht : Tendsto (fun α : Set.Ioi (0 : ℝ) => (1 + (α : ℝ))⁻¹ * y) atBot
        (𝓝 ((1 + 0)⁻¹ * y)) :=
      ((tendsto_const_nhds.add hc).inv₀ (by norm_num)).mul tendsto_const_nhds
    rw [hmp]
    simpa using ht
  · intro x
    exact subset_closure ⟨x, rfl⟩
  · have h2 : (0 : ℝ) < α := α.2
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    have h3 : (1 + (α : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      one_apply_eq_self, smul_eq_mul, norm_mul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 (by linarith : (0 : ℝ) < 1 + α))]
    exact mul_le_mul_of_nonneg_right h3 (abs_nonneg x)
  · rw [Filter.tendsto_atTop_atBot]
    intro b
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (Set.mem_Ioi.1 b.2)
    refine ⟨N, fun n hn => ?_⟩
    change 1 / ((n : ℝ) + 1) ≤ (b : ℝ)
    refine le_trans ?_ hN.le
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- The hypotheses of `AutoIp.exists_discrepancy_index` can fail. -/
theorem AutoIp.exists_discrepancy_index_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), ∃ (α : ℕ → (↑(Set.Ioi (0 : ℝ)) : Type)), ∃ (τ : ℝ), ∃ (δ : ℝ), ∃ (z : F), ¬ ((AutoIp.IsRegularization T R) ∧ (Dense (↑(LinearMap.range (↑T : E →ₗ[𝕜] F)) : Set F)) ∧ (∃ (C : ℝ), ∀ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ‖T ∘SL R α‖ ≤ C) ∧ (Filter.Tendsto α Filter.atTop Filter.atBot) ∧ ((0 : ℝ) < τ) ∧ ((0 : ℝ) < δ)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, 0, fun _ => ⟨1, Set.mem_Ioi.2 one_pos⟩, 0, 1, 0, ?_⟩
  rintro ⟨_, _, _, _, H, _⟩
  exact absurd H (lt_irrefl 0)
