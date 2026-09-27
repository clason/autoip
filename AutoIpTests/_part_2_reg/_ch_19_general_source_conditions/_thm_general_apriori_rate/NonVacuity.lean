module

import AutoIp._part_2_reg._ch_19_general_source_conditions._thm_general_apriori_rate.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity
import AutoIpTests.Witnesses.Zero

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.norm_spectralReg_sub_moorePenrose_le_apriori_index` can hold together. -/
theorem AutoIp.norm_spectralReg_sub_moorePenrose_le_apriori_index_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (flt : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (Cflt : ℝ), ∃ (φ : ℝ → ℝ), ∃ (ρ : ℝ), ∃ (CF : ℝ), ∃ (Cq : ℝ), ∃ (hφ : AutoIp.IsIndexFunction (‖K‖ ^ (2 : ℕ)) φ), ∃ (hρ : (0 : ℝ) < ρ), ∃ (y : F), ∃ (hy : y ∈ AutoIp.mpDomain K), ∃ (δ : ℝ), ∃ (z : F), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), (AutoIp.IsRegularizingFilter K flt Cflt) ∧ (AutoIp.HasFilterBound K flt CF) ∧ (AutoIp.HasQualification K flt φ Cq) ∧ ((↑(AutoIp.moorePenrose K) : ↥(LinearPMap.domain (AutoIp.moorePenrose K)) → E) ⟨y, hy⟩ ∈
  AutoIp.sourceSetIndex hs φ (AutoIp.IsIndexFunction.exists_bound_on_spectrum hs hφ) ρ hρ) ∧ (‖y - z‖ ≤ δ) ∧ ((↑α : ℝ) ≤ ‖K‖ ^ (2 : ℕ)) ∧ (AutoIp.thetaIndex φ (↑α : ℝ) = δ / ρ) :=
  by
  classical
  have hone : IsSingularSystem (ι := Unit) (1 : ℝ →L[ℝ] ℝ)
      (fun _ => 1) (fun _ => 1) (fun _ => 1) :=
    { pos := fun _ => one_pos
      orthonormal_left := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      orthonormal_right := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      span_left := Witnesses.Identity.span_left _ fun _ => rfl
      span_right := Witnesses.Identity.span_right _ fun _ => rfl
      map_left := fun _ => (one_mul (1 : ℝ)).symm
      map_right := fun _ =>
        (Witnesses.Identity.adjoint_one_apply 1).trans (one_mul (1 : ℝ)).symm }
  have hK : ‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ) = 1 := by
    rw [Witnesses.Identity.norm_one']
    norm_num
  let flt : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ := fun α t => if (α : ℝ) ≤ t then t⁻¹ else 0
  have hflt_le : ∀ (α : (↑(Set.Ioi (0 : ℝ)) : Type)) (t : ℝ), 0 ≤ t →
      |flt α t| ≤ (α : ℝ)⁻¹ := by
    intro α t ht
    have hα : (0 : ℝ) < α := α.2
    simp only [flt]
    split_ifs with h
    · rw [abs_of_pos (inv_pos.2 (hα.trans_le h))]
      exact inv_anti₀ hα h
    · simp only [abs_zero]
      exact (inv_pos.2 hα).le
  have hreg : AutoIp.IsRegularizingFilter (1 : ℝ →L[ℝ] ℝ) flt 1 := by
    refine ⟨one_pos, fun α => ⟨(α : ℝ)⁻¹, fun t ht => hflt_le α t ht.1⟩, fun lam hlam => ?_,
      fun α lam hlam => ?_⟩
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_atBot.2 ⟨⟨lam, hlam.1⟩, fun b hb => hb⟩] with b hb
      have hb' : (b : ℝ) ≤ lam := hb
      simp only [flt]
      rw [if_pos hb']
    · simp only [flt]
      split_ifs with h
      · rw [abs_of_pos (inv_pos.2 hlam.1), mul_inv_cancel₀ hlam.1.ne']
      · simp
  have hFB : AutoIp.HasFilterBound (1 : ℝ →L[ℝ] ℝ) flt 1 := by
    refine ⟨⟨1, hreg⟩, one_pos, fun α => ?_⟩
    have hα : (0 : ℝ) < α := α.2
    rw [one_mul]
    exact Real.iSup_le (fun lam => Real.iSup_le (fun hlam => hflt_le α lam hlam.1.le)
      (inv_pos.2 hα).le) (inv_pos.2 hα).le
  have hmp : ∀ (y : ℝ) (hy : y ∈ AutoIp.mpDomain (1 : ℝ →L[ℝ] ℝ)),
      AutoIp.moorePenrose (1 : ℝ →L[ℝ] ℝ) ⟨y, hy⟩ = y := by
    intro y hy
    have h := AutoIp.sub_apply_moorePenrose_mem_orthogonal (T := (1 : ℝ →L[ℝ] ℝ)) ⟨y, hy⟩
    have hr : LinearMap.range ((1 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) = ⊤ := LinearMap.range_id
    simp only [hr, Submodule.top_orthogonal_eq_bot, Submodule.mem_bot, sub_eq_zero] at h
    simpa using h.symm
  have hfc : ∀ (φ : ℝ → ℝ) (hφ : ∃ C, ∀ i : Unit, |φ ((fun _ => (1 : ℝ)) i ^ 2)| ≤ C),
      φ 0 = 0 → ∀ x : ℝ, hone.funCalc φ hφ x = φ 1 * x := by
    intro φ hφ h0 x
    have h := hone.hasSum_funCalc_sub_starProjection hφ x
    rw [h0] at h
    simp only [RCLike.ofReal_real_eq_id, id, zero_smul, sub_zero] at h
    have h2 := h.unique (hasSum_fintype _)
    simpa using h2
  have hy1 : (1 : ℝ) ∈ AutoIp.mpDomain (1 : ℝ →L[ℝ] ℝ) :=
    Submodule.mem_sup_left ⟨1, rfl⟩
  have hφ : AutoIp.IsIndexFunction (‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ)) (fun t => t) :=
    ⟨rfl, continuousOn_id, fun _ _ _ _ h => h⟩
  have hQ : AutoIp.HasQualification (1 : ℝ →L[ℝ] ℝ) flt (fun t => t) 1 := by
    refine ⟨⟨1, hreg⟩, hφ, zero_le_one, fun α _ => ?_⟩
    have hα : (0 : ℝ) < α := α.2
    rw [one_mul]
    refine Real.iSup_le (fun lam => Real.iSup_le (fun hlam => ?_) hα.le) hα.le
    simp only [flt]
    split_ifs with h
    · rw [mul_inv_cancel₀ hlam.1.ne', sub_self, abs_zero, mul_zero]
      exact hα.le
    · rw [mul_zero, sub_zero, abs_one, mul_one]
      exact (not_le.1 h).le
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1, hone,
    flt, 1, fun t => t, 1, 1, 1, hφ, one_pos, 1, hy1, 1, 0, ⟨1, Set.mem_Ioi.2 one_pos⟩, ?_⟩
  refine ⟨hreg, hFB, hQ, ?_, by simp, by rw [hK], ?_⟩
  · refine (AutoIp.mem_sourceSetIndex_iff _ _ _ _ _).2 ⟨1, by simp, ?_⟩
    rw [hfc _ _ rfl, hmp]
    norm_num
  · rw [AutoIp.thetaIndex_apply]
    simp

/-- The hypotheses of `AutoIp.norm_spectralReg_sub_moorePenrose_le_apriori_index` can fail. -/
theorem AutoIp.norm_spectralReg_sub_moorePenrose_le_apriori_index_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (flt : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (Cflt : ℝ), ∃ (φ : ℝ → ℝ), ∃ (ρ : ℝ), ∃ (CF : ℝ), ∃ (Cq : ℝ), ∃ (hφ : AutoIp.IsIndexFunction (‖K‖ ^ (2 : ℕ)) φ), ∃ (hρ : (0 : ℝ) < ρ), ∃ (y : F), ∃ (hy : y ∈ AutoIp.mpDomain K), ∃ (δ : ℝ), ∃ (z : F), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ¬ ((AutoIp.IsRegularizingFilter K flt Cflt) ∧ (AutoIp.HasFilterBound K flt CF) ∧ (AutoIp.HasQualification K flt φ Cq) ∧ ((↑(AutoIp.moorePenrose K) : ↥(LinearPMap.domain (AutoIp.moorePenrose K)) → E) ⟨y, hy⟩ ∈
  AutoIp.sourceSetIndex hs φ (AutoIp.IsIndexFunction.exists_bound_on_spectrum hs hφ) ρ hρ) ∧ (‖y - z‖ ≤ δ) ∧ ((↑α : ℝ) ≤ ‖K‖ ^ (2 : ℕ)) ∧ (AutoIp.thetaIndex φ (↑α : ℝ) = δ / ρ)) :=
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
  have hφ : AutoIp.IsIndexFunction (‖(0 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ)) (fun t => t) :=
    ⟨rfl, continuousOn_id, fun _ _ _ _ h => h⟩
  have hy : (0 : ℝ) ∈ AutoIp.mpDomain (0 : ℝ →L[ℝ] ℝ) := Submodule.zero_mem _
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Empty, fun _ => 0, fun _ => 0, fun _ => 0, hss,
    fun _ _ => 0, 0, fun t => t, 1, 1, 1, hφ, one_pos, 0, hy, 1, 0, ⟨1, Set.mem_Ioi.2 one_pos⟩, ?_⟩
  rintro ⟨H, _⟩
  exact absurd H.const_pos (lt_irrefl 0)
