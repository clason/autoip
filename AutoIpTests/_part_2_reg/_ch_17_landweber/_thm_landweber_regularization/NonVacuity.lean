module

import AutoIp._part_2_reg._ch_17_landweber._thm_landweber_regularization.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.landweber_eq_spectralReg_and_tendsto_moorePenrose` can hold together. -/
theorem AutoIp.landweber_eq_spectralReg_and_tendsto_moorePenrose_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ω : ℝ), (IsSingularSystem K σ v u) ∧ ((0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) ≤ (1 : ℝ)) :=
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
  have hω : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) * ‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ) ≤ 1 := by
    rw [Witnesses.Identity.norm_one']; norm_num
  exact ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1, 1 / 2, hone, hω⟩

/-- The hypotheses of `AutoIp.landweber_eq_spectralReg_and_tendsto_moorePenrose` can fail. -/
theorem AutoIp.landweber_eq_spectralReg_and_tendsto_moorePenrose_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ω : ℝ), ¬ ((IsSingularSystem K σ v u) ∧ ((0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) ≤ (1 : ℝ))) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, 0, ?_⟩
  rintro ⟨H, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)

/-- The hypotheses of `AutoIp.landweber_eq_spectralReg` can hold together. -/
theorem AutoIp.landweber_eq_spectralReg_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ω : ℝ), ∃ (y : F), ∃ (m : ℕ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), (IsSingularSystem K σ v u) ∧ ((0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) ≤ (1 : ℝ)) ∧ ((0 : ℕ) < m) ∧ ((↑α : ℝ) = (1 : ℝ) / (↑m : ℝ)) :=
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
  have hω : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) * ‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ) ≤ 1 := by
    rw [Witnesses.Identity.norm_one']; norm_num
  exact ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1, 1 / 2, 0, 1, ⟨1, Set.mem_Ioi.2 one_pos⟩,
    hone, hω, one_pos, by norm_num⟩

/-- The hypotheses of `AutoIp.landweber_eq_spectralReg` can fail. -/
theorem AutoIp.landweber_eq_spectralReg_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ω : ℝ), ∃ (y : F), ∃ (m : ℕ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ¬ ((IsSingularSystem K σ v u) ∧ ((0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) ≤ (1 : ℝ)) ∧ ((0 : ℕ) < m) ∧ ((↑α : ℝ) = (1 : ℝ) / (↑m : ℝ))) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, 0, 0, 1,
    ⟨1, Set.mem_Ioi.2 one_pos⟩, ?_⟩
  rintro ⟨H, _, _, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)

/-- The hypotheses of `AutoIp.tendsto_landweber_moorePenrose` can hold together. -/
theorem AutoIp.tendsto_landweber_moorePenrose_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ω : ℝ), ∃ (y : F), ∃ (α : ℕ → (↑(Set.Ioi (0 : ℝ)) : Type)), (IsSingularSystem K σ v u) ∧ ((0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) ≤ (1 : ℝ)) ∧ (y ∈ AutoIp.mpDomain K) ∧ (∀ (m : ℕ), (0 : ℕ) < m → (↑(α m) : ℝ) = (1 : ℝ) / (↑m : ℝ)) :=
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
  have hω : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) * ‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ) ≤ 1 := by
    rw [Witnesses.Identity.norm_one']; norm_num
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1, 1 / 2, 0,
    fun m => if hm : 0 < m then ⟨1 / (m : ℝ), Set.mem_Ioi.2 (by positivity)⟩
      else ⟨1, Set.mem_Ioi.2 one_pos⟩, hone, hω, Submodule.zero_mem _, ?_⟩
  intro m hm
  simp [hm]

/-- The hypotheses of `AutoIp.tendsto_landweber_moorePenrose` can fail. -/
theorem AutoIp.tendsto_landweber_moorePenrose_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ω : ℝ), ∃ (y : F), ∃ (α : ℕ → (↑(Set.Ioi (0 : ℝ)) : Type)), ¬ ((IsSingularSystem K σ v u) ∧ ((0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) ≤ (1 : ℝ)) ∧ (y ∈ AutoIp.mpDomain K) ∧ (∀ (m : ℕ), (0 : ℕ) < m → (↑(α m) : ℝ) = (1 : ℝ) / (↑m : ℝ))) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, 0, 0,
    fun _ => ⟨1, Set.mem_Ioi.2 one_pos⟩, ?_⟩
  rintro ⟨H, _, _, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)
