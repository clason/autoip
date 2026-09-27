module

import AutoIp._part_2_reg._ch_19_general_source_conditions._cor_general_holder_rate.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity
import AutoIpTests.Witnesses.Zero

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.norm_spectralReg_sub_moorePenrose_le_apriori_index_rpow` can hold together. -/
theorem AutoIp.norm_spectralReg_sub_moorePenrose_le_apriori_index_rpow_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (flt : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (Cflt : ℝ), ∃ (ν : ℝ), ∃ (ρ : ℝ), ∃ (CF : ℝ), ∃ (Cν : ℝ), ∃ (hν : (0 : ℝ) < ν), ∃ (hρ : (0 : ℝ) < ρ), ∃ (y : F), ∃ (hy : y ∈ AutoIp.mpDomain K), ∃ (δ : ℝ), ∃ (z : F), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), (AutoIp.IsRegularizingFilter K flt Cflt) ∧ (AutoIp.HasFilterBound K flt CF) ∧ (AutoIp.HasQualification K flt (fun (t : ℝ) => t ^ (ν / (2 : ℝ))) Cν) ∧ ((↑(AutoIp.moorePenrose K) : ↥(LinearPMap.domain (AutoIp.moorePenrose K)) → E) ⟨y, hy⟩ ∈ AutoIp.sourceSet hs ν hν ρ hρ) ∧ ((0 : ℝ) < δ) ∧ (δ / ρ ≤ (‖K‖ ^ (2 : ℕ)) ^ ((ν + (1 : ℝ)) / (2 : ℝ))) ∧ (‖y - z‖ ≤ δ) ∧ ((↑α : ℝ) = (δ / ρ) ^ ((2 : ℝ) / (ν + (1 : ℝ)))) :=
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
  have hy : (0 : ℝ) ∈ AutoIp.mpDomain (1 : ℝ →L[ℝ] ℝ) := Submodule.zero_mem _
  have hfun : (fun t : ℝ => t ^ ((2 : ℝ) / (2 : ℝ))) = fun t => t := by
    funext t
    norm_num
  have hQ : AutoIp.HasQualification (1 : ℝ →L[ℝ] ℝ) flt
      (fun (t : ℝ) => t ^ ((2 : ℝ) / (2 : ℝ))) 1 := by
    rw [hfun]
    refine ⟨⟨1, hreg⟩, ⟨rfl, continuousOn_id, fun _ _ _ _ h => h⟩, zero_le_one, fun α _ => ?_⟩
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
    flt, 1, 2, 1, 1, 1, two_pos, one_pos, 0, hy, 1, 0, ⟨1, Set.mem_Ioi.2 one_pos⟩, ?_⟩
  refine ⟨hreg, hFB, hQ, ?_, one_pos, by rw [hK]; simp, by simp, by simp⟩
  refine (AutoIp.mem_sourceSet_iff _ _ _ _ _).2 ⟨0, by simp, ?_⟩
  rw [map_zero]
  exact (LinearPMap.map_zero _).symm

/-- The hypotheses of `AutoIp.norm_spectralReg_sub_moorePenrose_le_apriori_index_rpow` can fail. -/
theorem AutoIp.norm_spectralReg_sub_moorePenrose_le_apriori_index_rpow_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (flt : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (Cflt : ℝ), ∃ (ν : ℝ), ∃ (ρ : ℝ), ∃ (CF : ℝ), ∃ (Cν : ℝ), ∃ (hν : (0 : ℝ) < ν), ∃ (hρ : (0 : ℝ) < ρ), ∃ (y : F), ∃ (hy : y ∈ AutoIp.mpDomain K), ∃ (δ : ℝ), ∃ (z : F), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ¬ ((AutoIp.IsRegularizingFilter K flt Cflt) ∧ (AutoIp.HasFilterBound K flt CF) ∧ (AutoIp.HasQualification K flt (fun (t : ℝ) => t ^ (ν / (2 : ℝ))) Cν) ∧ ((↑(AutoIp.moorePenrose K) : ↥(LinearPMap.domain (AutoIp.moorePenrose K)) → E) ⟨y, hy⟩ ∈ AutoIp.sourceSet hs ν hν ρ hρ) ∧ ((0 : ℝ) < δ) ∧ (δ / ρ ≤ (‖K‖ ^ (2 : ℕ)) ^ ((ν + (1 : ℝ)) / (2 : ℝ))) ∧ (‖y - z‖ ≤ δ) ∧ ((↑α : ℝ) = (δ / ρ) ^ ((2 : ℝ) / (ν + (1 : ℝ))))) :=
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
  have hy : (0 : ℝ) ∈ AutoIp.mpDomain (0 : ℝ →L[ℝ] ℝ) := Submodule.zero_mem _
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Empty, fun _ => 0, fun _ => 0, fun _ => 0, hss,
    fun _ _ => 0, 0, 2, 1, 1, 1, two_pos, one_pos, 0, hy, 1, 0, ⟨1, Set.mem_Ioi.2 one_pos⟩, ?_⟩
  rintro ⟨H, _⟩
  exact absurd H.const_pos (lt_irrefl 0)

/-- The hypotheses of `AutoIp.apriori_index_rpow_bracket_one_and_const_eq` can hold together. -/
theorem AutoIp.apriori_index_rpow_bracket_one_and_const_eq_satisfiable : ∃ (ν : ℝ), ∃ (δ : ℝ), ∃ (ρ : ℝ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ∃ (Cflt : ℝ), ∃ (CF : ℝ), ∃ (Cν : ℝ), (↑α : ℝ) = (δ / ρ) ^ ((2 : ℝ) / (ν + (1 : ℝ))) :=
  by
  refine ⟨1, 1, 1, ⟨1, Set.mem_Ioi.2 one_pos⟩, 0, 0, 0, ?_⟩
  simp

/-- The hypotheses of `AutoIp.apriori_index_rpow_bracket_one_and_const_eq` can fail. -/
theorem AutoIp.apriori_index_rpow_bracket_one_and_const_eq_nontrivial : ∃ (ν : ℝ), ∃ (δ : ℝ), ∃ (ρ : ℝ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ∃ (Cflt : ℝ), ∃ (CF : ℝ), ∃ (Cν : ℝ), ¬ ((↑α : ℝ) = (δ / ρ) ^ ((2 : ℝ) / (ν + (1 : ℝ)))) :=
  by
  refine ⟨1, 1, 1, ⟨2, Set.mem_Ioi.2 two_pos⟩, 0, 0, 0, ?_⟩
  norm_num
