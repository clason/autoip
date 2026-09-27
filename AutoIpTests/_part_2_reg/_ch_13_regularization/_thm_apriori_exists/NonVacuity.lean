module

import AutoIp._part_2_reg._ch_13_regularization._thm_apriori_exists.Spec -- shake: keep

open Filter Topology

/-- The hypotheses of `AutoIp.exists_apriori_isRegularizationMethod` can hold together. -/
theorem AutoIp.exists_apriori_isRegularizationMethod_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), AutoIp.IsRegularization T R :=
  ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 1, fun α => (1 + (α : ℝ))⁻¹ • (1 : ℝ →L[ℝ] ℝ), by
      intro y hy
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
      simpa using ht⟩

/-- The hypotheses of `AutoIp.exists_apriori_isRegularizationMethod` can fail. -/
theorem AutoIp.exists_apriori_isRegularizationMethod_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), ¬ (AutoIp.IsRegularization T R) :=
  ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 1, 0, by
      intro h
      have hy : (1 : ℝ) ∈ AutoIp.mpDomain (1 : ℝ →L[ℝ] ℝ) := by
        exact (AutoIp.IsLeastSquares.mem_mpDomain (x := (1 : ℝ)) (fun _ => by simp))
      have h1 := h 1 hy
      have hmp : AutoIp.moorePenrose (1 : ℝ →L[ℝ] ℝ) ⟨1, hy⟩ = 1 := by
        have hls : AutoIp.IsLeastSquares (1 : ℝ →L[ℝ] ℝ) 1 1 := fun _ => by simp
        have := (AutoIp.moorePenrose_isMinimumNorm ⟨(1 : ℝ), hy⟩).isLeastSquares
        have heq := (AutoIp.moorePenrose_isMinimumNorm ⟨(1 : ℝ), hy⟩).isLeastSquares 1
        simp only [ContinuousLinearMap.one_apply, sub_self, norm_zero] at heq
        have hz : (1 : ℝ →L[ℝ] ℝ) (AutoIp.moorePenrose 1 ⟨1, hy⟩) - 1 = 0 :=
          norm_eq_zero.1 (le_antisymm heq (norm_nonneg _))
        simpa using sub_eq_zero.1 hz
      rw [hmp, show (fun α : Set.Ioi (0 : ℝ) => ((0 : Set.Ioi (0 : ℝ) → ℝ →L[ℝ] ℝ) α) 1)
               = fun _ => (0 : ℝ) from rfl] at h1
      exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h1).symm⟩
