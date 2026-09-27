module

import AutoIp._part_2_reg._ch_21_perturbed_operator._thm_perturbed_total_error.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity
import AutoIpTests.Witnesses.Zero

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.norm_spectralReg_sub_moorePenrose_le_perturbed` can hold together. -/
theorem AutoIp.norm_spectralReg_sub_moorePenrose_le_perturbed_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (Kh : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ι' : Type), ∃ (σ' : ι' → ℝ), ∃ (v' : ι' → E), ∃ (u' : ι' → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (y : F), ∃ (z : F), ∃ (h : ℝ), ∃ (δ : ℝ), ∃ (ν : ℝ), ∃ (ρ : ℝ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ∃ (hy : y ∈ AutoIp.mpDomain K), ∃ (hν : (0 : ℝ) < ν), ∃ (hρ : (0 : ℝ) < ρ), (IsSingularSystem Kh σ' v' u') ∧ (AutoIp.IsAdmissibleData K Kh y z h δ) ∧ (ν ≤ (2 : ℝ)) ∧ ((↑(AutoIp.moorePenrose K) : ↥(LinearPMap.domain (AutoIp.moorePenrose K)) → E) ⟨y, hy⟩ ∈ AutoIp.sourceSet hs ν hν ρ hρ) ∧ ((↑α : ℝ) ≤ (1 : ℝ)) :=
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
  have hhalf : IsSingularSystem (ι := Unit) ((1 / 2 : ℝ) • (1 : ℝ →L[ℝ] ℝ))
      (fun _ => 1 / 2) (fun _ => 1) (fun _ => 1) :=
    { pos := fun _ => by norm_num
      orthonormal_left := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      orthonormal_right := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      span_left := by
        rw [ContinuousLinearMap.toLinearMap_smul, LinearMap.ker_smul _ _ (by norm_num)]
        exact Witnesses.Identity.span_left _ fun _ => rfl
      span_right := by
        rw [ContinuousLinearMap.toLinearMap_smul, LinearMap.range_smul _ _ (by norm_num)]
        exact Witnesses.Identity.span_right _ fun _ => rfl
      map_left := fun _ => by simp
      map_right := fun _ => by
        rw [map_smulₛₗ, smul_apply, Witnesses.Identity.adjoint_one_apply]
        simp }
  have hdist : ‖(1 : ℝ →L[ℝ] ℝ) - (1 / 2 : ℝ) • (1 : ℝ →L[ℝ] ℝ)‖ = 1 / 2 := by
    rw [show (1 : ℝ →L[ℝ] ℝ) - (1 / 2 : ℝ) • (1 : ℝ →L[ℝ] ℝ) = (1 / 2 : ℝ) • (1 : ℝ →L[ℝ] ℝ) by
      rw [sub_eq_iff_eq_add, ← add_smul]; norm_num, norm_smul, Witnesses.Identity.norm_one']
    norm_num
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
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, (1 / 2 : ℝ) • (1 : ℝ →L[ℝ] ℝ), Unit, fun _ => 1, fun _ => 1,
    fun _ => 1, Unit, fun _ => 1 / 2, fun _ => 1, fun _ => 1, hone, 1, 0, 1 / 2, 1, 1, 1,
    ⟨1, Set.mem_Ioi.2 one_pos⟩, hy1, one_pos, one_pos, ?_⟩
  refine ⟨hhalf, ⟨hdist.le, by norm_num⟩, by norm_num, ?_, le_rfl⟩
  refine (AutoIp.mem_sourceSet_iff _ _ _ _ _).2 ⟨1, by simp, ?_⟩
  rw [hone.absRpow_def 1 zero_le_one ⟨1, fun _ => by norm_num⟩,
    hfc (fun t : ℝ => t ^ ((1 : ℝ) / 2)) _ (Real.zero_rpow (by norm_num)), hmp]
  norm_num

/-- The hypotheses of `AutoIp.norm_spectralReg_sub_moorePenrose_le_perturbed` can fail. -/
theorem AutoIp.norm_spectralReg_sub_moorePenrose_le_perturbed_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (Kh : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ι' : Type), ∃ (σ' : ι' → ℝ), ∃ (v' : ι' → E), ∃ (u' : ι' → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (y : F), ∃ (z : F), ∃ (h : ℝ), ∃ (δ : ℝ), ∃ (ν : ℝ), ∃ (ρ : ℝ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ∃ (hy : y ∈ AutoIp.mpDomain K), ∃ (hν : (0 : ℝ) < ν), ∃ (hρ : (0 : ℝ) < ρ), ¬ ((IsSingularSystem Kh σ' v' u') ∧ (AutoIp.IsAdmissibleData K Kh y z h δ) ∧ (ν ≤ (2 : ℝ)) ∧ ((↑(AutoIp.moorePenrose K) : ↥(LinearPMap.domain (AutoIp.moorePenrose K)) → E) ⟨y, hy⟩ ∈ AutoIp.sourceSet hs ν hν ρ hρ) ∧ ((↑α : ℝ) ≤ (1 : ℝ))) :=
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
    inferInstance, inferInstance, 0, 0, Empty, fun _ => 0, fun _ => 0, fun _ => 0,
    Unit, fun _ => 0, fun _ => 0, fun _ => 0, hss, 0, 0, 0, 0, 1, 1,
    ⟨1, Set.mem_Ioi.2 one_pos⟩, hy, one_pos, one_pos, ?_⟩
  rintro ⟨H, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)
