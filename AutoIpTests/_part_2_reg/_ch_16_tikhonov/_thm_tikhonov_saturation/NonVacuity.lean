module

import AutoIp._part_2_reg._ch_16_tikhonov._thm_tikhonov_saturation.Spec -- shake: keep
import AutoIpTests.Witnesses.Diagonal
import AutoIpTests.Witnesses.Zero

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.tikhonov_saturation` can hold together. -/
theorem AutoIp.tikhonov_saturation_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (y : F), ∃ (hy : y ∈ LinearMap.range (↑K : E →ₗ[𝕜] F)), ∃ (a : AutoIp.ParameterChoice F), (IsCompactOperator (⇑K : E → F)) ∧ (¬FiniteDimensional 𝕜 ↥(LinearMap.range (↑K : E →ₗ[𝕜] F))) ∧ (AutoIp.ParameterChoice.IsAPriori a) ∧ (∀ (z : F),
  Filter.Tendsto (fun (δ : (↑(Set.Ioi (0 : ℝ)) : Type)) => (a : (↑(Set.Ioi (0 : ℝ)) : Type) → F → ℝ) δ z) Filter.atBot
    (nhds (0 : ℝ))) ∧ (Filter.Tendsto
  (fun (δ : (↑(Set.Ioi (0 : ℝ)) : Type)) =>
    AutoIp.worstCaseError K
        (fun (α : (↑(Set.Ioi (0 : ℝ)) : Type)) (w : F) =>
          (AutoIp.spectralReg hs AutoIp.tikhonovFilter (AutoIp.tikhonovFilter_exists_bound_on_spectrum hs) α : F → E) w)
        a y (Submodule.mem_sup_left hy) (↑δ : ℝ) (Subtype.property δ) *
      ENNReal.ofReal ((↑δ : ℝ) ^ (-2 / 3 : ℝ)))
  Filter.atBot (nhds (0 : ENNReal))) :=
  by
  classical
  have hsv : IsSingularSystem Witnesses.Diagonal.T Witnesses.Diagonal.w
      Witnesses.Diagonal.e Witnesses.Diagonal.e :=
    { pos := Witnesses.Diagonal.w_pos
      orthonormal_left := Witnesses.Diagonal.orthonormal_e
      orthonormal_right := Witnesses.Diagonal.orthonormal_e
      span_left := by
        rw [Witnesses.Diagonal.span_e_dense, Witnesses.Diagonal.ker_T,
          Submodule.bot_orthogonal_eq_top]
      span_right := by
        rw [Witnesses.Diagonal.span_e_dense, Witnesses.Diagonal.topologicalClosure_range_T]
      map_left := fun n => by rw [Witnesses.Diagonal.T_e]; rfl
      map_right := fun n => by rw [Witnesses.Diagonal.adjoint_T_e]; rfl }
  let a : AutoIp.ParameterChoice Witnesses.Diagonal.H :=
    ⟨fun δ _ => (δ : ℝ) ^ (1 / 6 : ℝ), fun δ _ => Real.rpow_pos_of_pos δ.2 _⟩
  have ha : ∀ δ z, a δ z = (δ : ℝ) ^ (1 / 6 : ℝ) := fun _ _ => rfl
  have hR : ∀ (α : (↑(Set.Ioi (0 : ℝ)) : Type)) (z : Witnesses.Diagonal.H),
      ‖AutoIp.spectralReg hsv AutoIp.tikhonovFilter
          (AutoIp.tikhonovFilter_exists_bound_on_spectrum hsv) α z‖ ≤ (α : ℝ)⁻¹ * ‖z‖ := by
    intro α z
    have hα : (0 : ℝ) < α := α.2
    have hsum := AutoIp.hasSum_spectralReg hsv AutoIp.tikhonovFilter
      (AutoIp.tikhonovFilter_exists_bound_on_spectrum hsv) α z
    refine Witnesses.Diagonal.norm_le_of_abs_le (inv_nonneg.2 hα.le) fun n => ?_
    rw [Witnesses.Diagonal.apply_of_hasSum hsum n, Witnesses.Diagonal.inner_e_left,
      AutoIp.tikhonovFilter_apply]
    have hw := Witnesses.Diagonal.w_pos n
    have hw1 := Witnesses.Diagonal.w_le_one n
    have hq : (Witnesses.Diagonal.w n ^ 2 + (α : ℝ))⁻¹ * Witnesses.Diagonal.w n ≤ (α : ℝ)⁻¹ := by
      rw [inv_mul_le_iff₀ (by positivity), le_mul_inv_iff₀ hα]
      nlinarith
    simp only [RCLike.ofReal_real_eq_id, id, abs_mul]
    rw [abs_of_pos (by positivity : (0 : ℝ) < (Witnesses.Diagonal.w n ^ 2 + (α : ℝ))⁻¹),
      abs_of_pos hw]
    exact mul_le_mul_of_nonneg_right hq (abs_nonneg _)
  have hmp : ∀ p : (AutoIp.moorePenrose Witnesses.Diagonal.T).domain,
      (p : Witnesses.Diagonal.H) = 0 →
      AutoIp.moorePenrose Witnesses.Diagonal.T p = 0 := fun p hp => by
    rw [show p = 0 from Subtype.ext hp]
    exact LinearPMap.map_zero _
  refine ⟨ℝ, inferInstance, Witnesses.Diagonal.H, Witnesses.Diagonal.H, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Witnesses.Diagonal.T, ℕ, Witnesses.Diagonal.w, Witnesses.Diagonal.e,
    Witnesses.Diagonal.e, hsv, 0, Submodule.zero_mem _, a,
    Witnesses.Diagonal.isCompactOperator_T, Witnesses.Diagonal.not_finiteDimensional_range,
    fun _ _ _ => rfl, fun z => ?_, ?_⟩
  · simp only [ha]
    exact Witnesses.Diagonal.tendsto_rpow_atBot (by norm_num)
  have hbound : ∀ δ : (↑(Set.Ioi (0 : ℝ)) : Type),
      AutoIp.worstCaseError Witnesses.Diagonal.T
          (fun (α : (↑(Set.Ioi (0 : ℝ)) : Type)) (w : Witnesses.Diagonal.H) =>
            (AutoIp.spectralReg hsv AutoIp.tikhonovFilter
              (AutoIp.tikhonovFilter_exists_bound_on_spectrum hsv) α :
                Witnesses.Diagonal.H → Witnesses.Diagonal.H) w)
          a 0 (Submodule.mem_sup_left (Submodule.zero_mem _)) (↑δ : ℝ) (Subtype.property δ) *
        ENNReal.ofReal ((↑δ : ℝ) ^ (-2 / 3 : ℝ)) ≤ ENNReal.ofReal ((δ : ℝ) ^ (1 / 6 : ℝ)) := by
    intro δ
    have hδ : (0 : ℝ) < δ := δ.2
    have hW : AutoIp.worstCaseError Witnesses.Diagonal.T
          (fun (α : (↑(Set.Ioi (0 : ℝ)) : Type)) (w : Witnesses.Diagonal.H) =>
            (AutoIp.spectralReg hsv AutoIp.tikhonovFilter
              (AutoIp.tikhonovFilter_exists_bound_on_spectrum hsv) α :
                Witnesses.Diagonal.H → Witnesses.Diagonal.H) w)
          a 0 (Submodule.mem_sup_left (Submodule.zero_mem _)) (↑δ : ℝ) (Subtype.property δ)
        ≤ ENNReal.ofReal (((δ : ℝ) ^ (1 / 6 : ℝ))⁻¹ * δ) := by
      refine (AutoIp.worstCaseError_le_iff _ _ _ _ _ _ _ _).2 fun z hz => ?_
      rw [hmp _ rfl, sub_zero, ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ((hR _ z).trans ?_)
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      exact mul_le_mul_of_nonneg_left hz (inv_nonneg.2 (Real.rpow_pos_of_pos hδ _).le)
    calc _ ≤ ENNReal.ofReal (((δ : ℝ) ^ (1 / 6 : ℝ))⁻¹ * δ) *
          ENNReal.ofReal ((↑δ : ℝ) ^ (-2 / 3 : ℝ)) := mul_le_mul_left hW _
      _ = ENNReal.ofReal (((δ : ℝ) ^ (1 / 6 : ℝ))⁻¹ * δ * (↑δ : ℝ) ^ (-2 / 3 : ℝ)) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ = ENNReal.ofReal ((δ : ℝ) ^ (1 / 6 : ℝ)) := by
          congr 1
          calc ((δ : ℝ) ^ (1 / 6 : ℝ))⁻¹ * δ * (↑δ : ℝ) ^ (-2 / 3 : ℝ)
              = (δ : ℝ) ^ (-(1 / 6) : ℝ) * (δ : ℝ) ^ (1 : ℝ) * (↑δ : ℝ) ^ (-2 / 3 : ℝ) := by
                rw [Real.rpow_neg hδ.le, Real.rpow_one]
            _ = (δ : ℝ) ^ (-(1 / 6) + 1 + -2 / 3 : ℝ) := by
                rw [Real.rpow_add hδ, Real.rpow_add hδ]
            _ = (δ : ℝ) ^ (1 / 6 : ℝ) := by norm_num
  have hup : Filter.Tendsto (fun δ : (↑(Set.Ioi (0 : ℝ)) : Type) =>
      ENNReal.ofReal ((δ : ℝ) ^ (1 / 6 : ℝ))) Filter.atBot (nhds 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (Witnesses.Diagonal.tendsto_rpow_atBot (by norm_num))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun _ => zero_le) hbound

/-- The hypotheses of `AutoIp.tikhonov_saturation` can fail. -/
theorem AutoIp.tikhonov_saturation_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (y : F), ∃ (hy : y ∈ LinearMap.range (↑K : E →ₗ[𝕜] F)), ∃ (a : AutoIp.ParameterChoice F), ¬ ((IsCompactOperator (⇑K : E → F)) ∧ (¬FiniteDimensional 𝕜 ↥(LinearMap.range (↑K : E →ₗ[𝕜] F))) ∧ (AutoIp.ParameterChoice.IsAPriori a) ∧ (∀ (z : F),
  Filter.Tendsto (fun (δ : (↑(Set.Ioi (0 : ℝ)) : Type)) => (a : (↑(Set.Ioi (0 : ℝ)) : Type) → F → ℝ) δ z) Filter.atBot
    (nhds (0 : ℝ))) ∧ (Filter.Tendsto
  (fun (δ : (↑(Set.Ioi (0 : ℝ)) : Type)) =>
    AutoIp.worstCaseError K
        (fun (α : (↑(Set.Ioi (0 : ℝ)) : Type)) (w : F) =>
          (AutoIp.spectralReg hs AutoIp.tikhonovFilter (AutoIp.tikhonovFilter_exists_bound_on_spectrum hs) α : F → E) w)
        a y (Submodule.mem_sup_left hy) (↑δ : ℝ) (Subtype.property δ) *
      ENNReal.ofReal ((↑δ : ℝ) ^ (-2 / 3 : ℝ)))
  Filter.atBot (nhds (0 : ENNReal)))) :=
  by
  classical
  have hss : IsSingularSystem (ι := Empty) (0 : ℝ →L[ℝ] ℝ)
      (fun _ => 0) (fun _ => 0) (fun _ => 0) :=
    { pos := fun i => i.elim
      orthonormal_left := ⟨fun i => i.elim, fun {i _} _ => i.elim⟩
      orthonormal_right := ⟨fun i => i.elim, fun {i _} _ => i.elim⟩
      span_left := Witnesses.Zero.span_left _
      span_right := Witnesses.Zero.span_right _
      map_left := fun i => i.elim
      map_right := fun i => i.elim }
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Empty, fun _ => 0, fun _ => 0, fun _ => 0, hss, 0,
    Submodule.zero_mem _, ⟨fun _ _ => 1, fun _ _ => one_pos⟩, ?_⟩
  rintro ⟨_, H, -⟩
  exact H inferInstance
