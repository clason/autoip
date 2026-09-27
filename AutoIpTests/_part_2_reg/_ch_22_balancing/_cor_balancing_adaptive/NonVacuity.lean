module

import AutoIp._part_2_reg._ch_22_balancing._cor_balancing_adaptive.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity
import AutoIpTests.Witnesses.Zero

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.balancing_orderOptimal` can hold together. -/
theorem AutoIp.balancing_orderOptimal_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (flt : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (Cflt : ℝ), ∃ (CF : ℝ), ∃ (Cν : ℝ), ∃ (ν : ℝ), ∃ (ρ : ℝ), ∃ (hν : (0 : ℝ) < ν), ∃ (hρ : (0 : ℝ) < ρ), ∃ (y : F), ∃ (hy : y ∈ AutoIp.mpDomain K), ∃ (δ : ℝ), ∃ (z : F), ∃ (N : ℕ), ∃ (grid : ℕ → (↑(Set.Ioi (0 : ℝ)) : Type)), ∃ (q : ℝ), ∃ (cl : ℝ), ∃ (cu : ℝ), (AutoIp.IsRegularizingFilter K flt Cflt) ∧ (AutoIp.HasFilterBound K flt CF) ∧ (AutoIp.HasQualification K flt (fun (t : ℝ) => t ^ (ν / (2 : ℝ))) Cν) ∧ ((↑(AutoIp.moorePenrose K) : ↥(LinearPMap.domain (AutoIp.moorePenrose K)) → E) ⟨y, hy⟩ ∈ AutoIp.sourceSet hs ν hν ρ hρ) ∧ ((0 : ℝ) < δ) ∧ (‖y - z‖ ≤ δ) ∧ ((1 : ℝ) < q) ∧ (∀ i ≤ N, (↑(grid i) : ℝ) ≤ ‖K‖ ^ (2 : ℕ)) ∧ (∀ (i : ℕ), i + (1 : ℕ) ≤ N → (↑(grid i) : ℝ) = q * (↑(grid (i + (1 : ℕ))) : ℝ)) ∧ ((0 : ℝ) < cl) ∧ ((0 : ℝ) < cu) ∧ (∃ i ≤ N,
  cl * (δ / ρ) ^ ((2 : ℝ) / (ν + (1 : ℝ))) ≤ (↑(grid i) : ℝ) ∧
    (↑(grid i) : ℝ) ≤ cu * (δ / ρ) ^ ((2 : ℝ) / (ν + (1 : ℝ)))) :=
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
  have hK : ‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ) = 1 := by rw [Witnesses.Identity.norm_one']; norm_num
  let flt : Set.Ioi (0 : ℝ) → ℝ → ℝ := fun α lam => if (α : ℝ) ≤ lam then lam⁻¹ else 0
  have hbd : ∀ (α : Set.Ioi (0 : ℝ)) (t : ℝ), 0 ≤ t → |flt α t| ≤ (α : ℝ)⁻¹ := by
    intro α t ht
    have hα : (0 : ℝ) < α := α.2
    simp only [flt]
    split_ifs with h
    · rw [abs_of_nonneg (inv_nonneg.2 ht)]
      exact inv_anti₀ hα h
    · simp [hα.le]
  have hreg : AutoIp.IsRegularizingFilter (1 : ℝ →L[ℝ] ℝ) flt 1 := by
    refine ⟨one_pos, fun α => ⟨(α : ℝ)⁻¹, fun t ht => hbd α t ht.1⟩, fun lam hlam => ?_,
      fun α lam hlam => ?_⟩
    · have hl : lam ∈ Set.Ioi (0 : ℝ) := hlam.1
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_le_atBot (⟨lam, hl⟩ : Set.Ioi (0 : ℝ))] with α hα
      have hα' : (α : ℝ) ≤ lam := hα
      simp [flt, hα']
    · have hl : 0 < lam := hlam.1
      simp only [flt]
      split_ifs with h
      · rw [abs_of_pos (inv_pos.2 hl), mul_inv_cancel₀ hl.ne']
      · simp
  have hF : AutoIp.HasFilterBound (1 : ℝ →L[ℝ] ℝ) flt 1 := by
    refine ⟨⟨1, hreg⟩, one_pos, fun α => ?_⟩
    have hα : (0 : ℝ) < α := α.2
    rw [one_mul]
    exact Real.iSup_le (fun lam => Real.iSup_le (fun hlam => hbd α lam hlam.1.le)
      (inv_nonneg.2 hα.le)) (inv_nonneg.2 hα.le)
  have hw : (fun t : ℝ => t ^ ((2 : ℝ) / (2 : ℝ))) = fun t => t := by
    funext t
    norm_num
  have hidx : AutoIp.IsIndexFunction (‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ))
      (fun t : ℝ => t ^ ((2 : ℝ) / (2 : ℝ))) := by
    rw [hw]
    exact ⟨rfl, continuousOn_id, fun _ _ _ _ h => h⟩
  have hQ : AutoIp.HasQualification (1 : ℝ →L[ℝ] ℝ) flt
      (fun t : ℝ => t ^ ((2 : ℝ) / (2 : ℝ))) 1 := by
    refine ⟨⟨1, hreg⟩, hidx, zero_le_one, fun α _ => ?_⟩
    have hα : (0 : ℝ) < α := α.2
    have hw' : ∀ t : ℝ, t ^ ((2 : ℝ) / (2 : ℝ)) = t := fun t => by norm_num
    simp only [hw']
    have hr : (0 : ℝ) ≤ 1 * (α : ℝ) := by linarith
    refine Real.iSup_le (fun lam => Real.iSup_le (fun hlam => ?_) hr) hr
    have hl : 0 < lam := hlam.1
    simp only [flt]
    split_ifs with h
    · rw [mul_inv_cancel₀ hl.ne', sub_self, abs_zero, mul_zero]
      exact hr
    · push Not at h
      rw [mul_zero, sub_zero, abs_one, mul_one, one_mul]
      exact h.le
  have hy : (0 : ℝ) ∈ AutoIp.mpDomain (1 : ℝ →L[ℝ] ℝ) := Submodule.zero_mem _
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1, hone,
    flt, 1, 1, 1, 2, 1, two_pos, one_pos, 0, hy, 1, 0, 0,
    fun _ => ⟨1, Set.mem_Ioi.2 one_pos⟩, 2, 1, 1, ?_⟩
  refine ⟨hreg, hF, hQ, ?_, one_pos, by simp, by norm_num, fun i _ => by rw [hK],
    fun i hi => absurd hi (by omega), one_pos, one_pos, ⟨0, le_rfl, by simp, by simp⟩⟩
  refine (AutoIp.mem_sourceSet_iff _ _ _ _ _).2 ⟨0, by simp, ?_⟩
  rw [map_zero]
  exact (LinearPMap.map_zero _).symm

/-- The hypotheses of `AutoIp.balancing_orderOptimal` can fail. -/
theorem AutoIp.balancing_orderOptimal_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (flt : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (Cflt : ℝ), ∃ (CF : ℝ), ∃ (Cν : ℝ), ∃ (ν : ℝ), ∃ (ρ : ℝ), ∃ (hν : (0 : ℝ) < ν), ∃ (hρ : (0 : ℝ) < ρ), ∃ (y : F), ∃ (hy : y ∈ AutoIp.mpDomain K), ∃ (δ : ℝ), ∃ (z : F), ∃ (N : ℕ), ∃ (grid : ℕ → (↑(Set.Ioi (0 : ℝ)) : Type)), ∃ (q : ℝ), ∃ (cl : ℝ), ∃ (cu : ℝ), ¬ ((AutoIp.IsRegularizingFilter K flt Cflt) ∧ (AutoIp.HasFilterBound K flt CF) ∧ (AutoIp.HasQualification K flt (fun (t : ℝ) => t ^ (ν / (2 : ℝ))) Cν) ∧ ((↑(AutoIp.moorePenrose K) : ↥(LinearPMap.domain (AutoIp.moorePenrose K)) → E) ⟨y, hy⟩ ∈ AutoIp.sourceSet hs ν hν ρ hρ) ∧ ((0 : ℝ) < δ) ∧ (‖y - z‖ ≤ δ) ∧ ((1 : ℝ) < q) ∧ (∀ i ≤ N, (↑(grid i) : ℝ) ≤ ‖K‖ ^ (2 : ℕ)) ∧ (∀ (i : ℕ), i + (1 : ℕ) ≤ N → (↑(grid i) : ℝ) = q * (↑(grid (i + (1 : ℕ))) : ℝ)) ∧ ((0 : ℝ) < cl) ∧ ((0 : ℝ) < cu) ∧ (∃ i ≤ N,
  cl * (δ / ρ) ^ ((2 : ℝ) / (ν + (1 : ℝ))) ≤ (↑(grid i) : ℝ) ∧
    (↑(grid i) : ℝ) ≤ cu * (δ / ρ) ^ ((2 : ℝ) / (ν + (1 : ℝ))))) :=
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
    fun _ _ => 0, 1, 1, 1, 1, 1, one_pos, one_pos, 0, hy, 0, 0, 0,
    fun _ => ⟨1, Set.mem_Ioi.2 one_pos⟩, 2, 1, 1, ?_⟩
  rintro ⟨_, _, _, _, hδ, _⟩
  exact absurd hδ (lt_irrefl 0)
