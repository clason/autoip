module

import AutoIp._part_2_reg._ch_13_regularization._thm_apriori_characterisation.Spec -- shake: keep
import AutoIpTests.Witnesses.Diagonal

open Filter Topology

/-- The hypotheses of `AutoIp.isRegularizationMethod_of_apriori` can hold together. -/
theorem AutoIp.isRegularizationMethod_of_apriori_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), ∃ (a : AutoIp.ParameterChoice F), (AutoIp.IsRegularization T R) ∧ (AutoIp.ParameterChoice.IsAPriori a) ∧ (∀ (y : F),
  Filter.Tendsto (fun (δ : (↑(Set.Ioi (0 : ℝ)) : Type)) => (a : (↑(Set.Ioi (0 : ℝ)) : Type) → F → ℝ) δ y) Filter.atBot
    (nhds (0 : ℝ))) ∧ (∀ (y : F),
  Filter.Tendsto (fun (δ : (↑(Set.Ioi (0 : ℝ)) : Type)) => (↑δ : ℝ) * ‖R (AutoIp.ParameterChoice.param a δ y)‖)
    Filter.atBot (nhds (0 : ℝ))) :=
  by
  have hmp : ∀ (y : ℝ) (hy : y ∈ AutoIp.mpDomain (1 : ℝ →L[ℝ] ℝ)),
      AutoIp.moorePenrose (1 : ℝ →L[ℝ] ℝ) ⟨y, hy⟩ = y := by
    intro y hy
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
  let a : AutoIp.ParameterChoice ℝ := ⟨fun δ _ => (δ : ℝ), fun δ _ => δ.2⟩
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, 1,
    fun α => (1 + (α : ℝ))⁻¹ • (1 : ℝ →L[ℝ] ℝ), a, ?_, fun _ _ _ => rfl, fun _ => hc, ?_⟩
  · intro y hy
    have ht : Tendsto (fun α : Set.Ioi (0 : ℝ) => (1 + (α : ℝ))⁻¹ * y) atBot
        (𝓝 ((1 + 0)⁻¹ * y)) :=
      ((tendsto_const_nhds.add hc).inv₀ (by norm_num)).mul tendsto_const_nhds
    rw [hmp]
    simpa using ht
  · intro y
    have ht : Tendsto (fun δ : Set.Ioi (0 : ℝ) => (δ : ℝ) * |(1 + (δ : ℝ))⁻¹|) atBot
        (𝓝 (0 * |(1 + 0)⁻¹|)) :=
      hc.mul ((tendsto_const_nhds.add hc).inv₀ (by norm_num)).abs
    rw [zero_mul] at ht
    refine ht.congr fun δ => ?_
    change (δ : ℝ) * |(1 + (δ : ℝ))⁻¹| = (δ : ℝ) * ‖(1 + (δ : ℝ))⁻¹ • (1 : ℝ →L[ℝ] ℝ)‖
    rw [norm_smul, norm_one, mul_one, Real.norm_eq_abs]

/-- The hypotheses of `AutoIp.isRegularizationMethod_of_apriori` can fail. -/
theorem AutoIp.isRegularizationMethod_of_apriori_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), ∃ (a : AutoIp.ParameterChoice F), ¬ ((AutoIp.IsRegularization T R) ∧ (AutoIp.ParameterChoice.IsAPriori a) ∧ (∀ (y : F),
  Filter.Tendsto (fun (δ : (↑(Set.Ioi (0 : ℝ)) : Type)) => (a : (↑(Set.Ioi (0 : ℝ)) : Type) → F → ℝ) δ y) Filter.atBot
    (nhds (0 : ℝ))) ∧ (∀ (y : F),
  Filter.Tendsto (fun (δ : (↑(Set.Ioi (0 : ℝ)) : Type)) => (↑δ : ℝ) * ‖R (AutoIp.ParameterChoice.param a δ y)‖)
    Filter.atBot (nhds (0 : ℝ)))) :=
  by
  let a : AutoIp.ParameterChoice ℝ := ⟨fun _ _ => 1, fun _ _ => one_pos⟩
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 0, fun _ => 0, a, ?_⟩
  rintro ⟨-, -, h, -⟩
  have h1 := h 0
  change Tendsto (fun _ : Set.Ioi (0 : ℝ) => (1 : ℝ)) atBot (𝓝 0) at h1
  haveI : Nonempty (Set.Ioi (0 : ℝ)) := ⟨⟨1, Set.mem_Ioi.2 one_pos⟩⟩
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h1)

/-- The hypotheses of `AutoIp.tendsto_norm_sub_moorePenrose_of_isRegularizationMethod` can hold together. -/
theorem AutoIp.tendsto_norm_sub_moorePenrose_of_isRegularizationMethod_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), ∃ (a : AutoIp.ParameterChoice F), ∃ (y : F), (AutoIp.IsRegularizationMethod T (fun (α : (↑(Set.Ioi (0 : ℝ)) : Type)) (w : F) => (R α : F → E) w) a) ∧ (y ∈ AutoIp.mpDomain T) :=
  by
  have hmp : ∀ (y : ℝ) (hy : y ∈ AutoIp.mpDomain (1 : ℝ →L[ℝ] ℝ)),
      AutoIp.moorePenrose (1 : ℝ →L[ℝ] ℝ) ⟨y, hy⟩ = y := by
    intro y hy
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
  let a : AutoIp.ParameterChoice ℝ := ⟨fun δ _ => (δ : ℝ), fun δ _ => δ.2⟩
  have hmeth : AutoIp.IsRegularizationMethod (1 : ℝ →L[ℝ] ℝ)
      (fun α w => ((1 + (α : ℝ))⁻¹ • (1 : ℝ →L[ℝ] ℝ) : ℝ → ℝ) w) a := by
    intro y hy ε hε
    refine ⟨ε / (1 + |y|), by positivity, fun δ hδ z hz => ?_⟩
    rw [hmp y hy]
    change |(1 + δ)⁻¹ * z - y| < ε
    have hδ0 : 0 < δ := hδ.1
    have hδ1 : δ < ε / (1 + |y|) := hδ.2
    rw [Real.norm_eq_abs] at hz
    have key : (1 + δ)⁻¹ * z - y = (1 + δ)⁻¹ * ((z - y) - δ * y) := by
      field_simp
      ring
    calc |(1 + δ)⁻¹ * z - y| = (1 + δ)⁻¹ * |(z - y) - δ * y| := by
          rw [key, abs_mul, abs_of_pos (inv_pos.2 (by linarith))]
      _ ≤ 1 * |(z - y) - δ * y| :=
          mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ (by linarith)) (abs_nonneg _)
      _ ≤ |z - y| + |δ * y| := by rw [one_mul]; exact abs_sub _ _
      _ ≤ δ + δ * |y| := by rw [abs_sub_comm, abs_mul, abs_of_pos hδ0]; linarith
      _ = δ * (1 + |y|) := by ring
      _ < ε := by rwa [lt_div_iff₀ (by positivity)] at hδ1
  exact ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 1, fun α => (1 + (α : ℝ))⁻¹ • (1 : ℝ →L[ℝ] ℝ), a, 1, hmeth,
    Submodule.mem_sup_left ⟨1, rfl⟩⟩

/-- The hypotheses of `AutoIp.tendsto_norm_sub_moorePenrose_of_isRegularizationMethod` can fail. -/
theorem AutoIp.tendsto_norm_sub_moorePenrose_of_isRegularizationMethod_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), ∃ (a : AutoIp.ParameterChoice F), ∃ (y : F), ¬ ((AutoIp.IsRegularizationMethod T (fun (α : (↑(Set.Ioi (0 : ℝ)) : Type)) (w : F) => (R α : F → E) w) a) ∧ (y ∈ AutoIp.mpDomain T)) :=
  by
  let a : AutoIp.ParameterChoice Witnesses.Diagonal.H := ⟨fun _ _ => 1, fun _ _ => one_pos⟩
  refine ⟨ℝ, inferInstance, Witnesses.Diagonal.H, Witnesses.Diagonal.H, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, Witnesses.Diagonal.T, fun _ => 0,
    a, Witnesses.Diagonal.y, ?_⟩
  rintro ⟨-, h⟩
  exact Witnesses.Diagonal.notMem_sup_orthogonal_range h

/-- The hypotheses of `AutoIp.tendsto_of_isAPriori_of_isRegularizationMethod` can hold together. -/
theorem AutoIp.tendsto_of_isAPriori_of_isRegularizationMethod_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), ∃ (a : AutoIp.ParameterChoice F), (AutoIp.ParameterChoice.IsAPriori a) ∧ (AutoIp.IsRegularizationMethod T (fun (α : (↑(Set.Ioi (0 : ℝ)) : Type)) (w : F) => (R α : F → E) w) a) :=
  by
  have hmp : ∀ (y : ℝ) (hy : y ∈ AutoIp.mpDomain (1 : ℝ →L[ℝ] ℝ)),
      AutoIp.moorePenrose (1 : ℝ →L[ℝ] ℝ) ⟨y, hy⟩ = y := by
    intro y hy
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
  let a : AutoIp.ParameterChoice ℝ := ⟨fun δ _ => (δ : ℝ), fun δ _ => δ.2⟩
  have hmeth : AutoIp.IsRegularizationMethod (1 : ℝ →L[ℝ] ℝ)
      (fun α w => ((1 + (α : ℝ))⁻¹ • (1 : ℝ →L[ℝ] ℝ) : ℝ → ℝ) w) a := by
    intro y hy ε hε
    refine ⟨ε / (1 + |y|), by positivity, fun δ hδ z hz => ?_⟩
    rw [hmp y hy]
    change |(1 + δ)⁻¹ * z - y| < ε
    have hδ0 : 0 < δ := hδ.1
    have hδ1 : δ < ε / (1 + |y|) := hδ.2
    rw [Real.norm_eq_abs] at hz
    have key : (1 + δ)⁻¹ * z - y = (1 + δ)⁻¹ * ((z - y) - δ * y) := by
      field_simp
      ring
    calc |(1 + δ)⁻¹ * z - y| = (1 + δ)⁻¹ * |(z - y) - δ * y| := by
          rw [key, abs_mul, abs_of_pos (inv_pos.2 (by linarith))]
      _ ≤ 1 * |(z - y) - δ * y| :=
          mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ (by linarith)) (abs_nonneg _)
      _ ≤ |z - y| + |δ * y| := by rw [one_mul]; exact abs_sub _ _
      _ ≤ δ + δ * |y| := by rw [abs_sub_comm, abs_mul, abs_of_pos hδ0]; linarith
      _ = δ * (1 + |y|) := by ring
      _ < ε := by rwa [lt_div_iff₀ (by positivity)] at hδ1
  exact ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 1, fun α => (1 + (α : ℝ))⁻¹ • (1 : ℝ →L[ℝ] ℝ), a, fun _ _ _ => rfl, hmeth⟩

/-- The hypotheses of `AutoIp.tendsto_of_isAPriori_of_isRegularizationMethod` can fail. -/
theorem AutoIp.tendsto_of_isAPriori_of_isRegularizationMethod_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), ∃ (a : AutoIp.ParameterChoice F), ¬ ((AutoIp.ParameterChoice.IsAPriori a) ∧ (AutoIp.IsRegularizationMethod T (fun (α : (↑(Set.Ioi (0 : ℝ)) : Type)) (w : F) => (R α : F → E) w) a)) :=
  by
  let a : AutoIp.ParameterChoice ℝ := ⟨fun _ y => ‖y‖ + 1, fun _ _ => by positivity⟩
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 0, fun _ => 0, a, ?_⟩
  rintro ⟨h, -⟩
  have h1 := h ⟨1, Set.mem_Ioi.2 one_pos⟩ 0 1
  change ‖(0 : ℝ)‖ + 1 = ‖(1 : ℝ)‖ + 1 at h1
  norm_num at h1
