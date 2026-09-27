module

import AutoIp._part_2_reg._ch_16_tikhonov._cor_tikhonov_apriori.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.tikhonov_orderOptimal_apriori` can hold together. -/
theorem AutoIp.tikhonov_orderOptimal_apriori_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ν : ℝ), ∃ (ρ : ℝ), ∃ (cl : ℝ), ∃ (cu : ℝ), ∃ (a : AutoIp.ParameterChoice F), (IsSingularSystem K σ v u) ∧ (ν ∈ Set.Ioc (0 : ℝ) (2 : ℝ)) ∧ ((0 : ℝ) < ρ) ∧ ((0 : ℝ) < cl) ∧ ((0 : ℝ) < cu) ∧ (AutoIp.ParameterChoice.IsAPriori a) ∧ (∀ (δ : (↑(Set.Ioi (0 : ℝ)) : Type)) (z : F),
  cl * ((↑δ : ℝ) / ρ) ^ ((2 : ℝ) / (ν + (1 : ℝ))) ≤ (a : (↑(Set.Ioi (0 : ℝ)) : Type) → F → ℝ) δ z ∧
    (a : (↑(Set.Ioi (0 : ℝ)) : Type) → F → ℝ) δ z ≤ cu * ((↑δ : ℝ) / ρ) ^ ((2 : ℝ) / (ν + (1 : ℝ)))) :=
  by
  classical
  have hss : IsSingularSystem (ι := Unit) (1 : ℝ →L[ℝ] ℝ)
      (fun _ => 1) (fun _ => 1) (fun _ => 1) :=
    { pos := fun _ => one_pos
      orthonormal_left := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      orthonormal_right := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      span_left := Witnesses.Identity.span_left _ fun _ => rfl
      span_right := Witnesses.Identity.span_right _ fun _ => rfl
      map_left := fun _ => (one_mul (1 : ℝ)).symm
      map_right := fun _ =>
        (Witnesses.Identity.adjoint_one_apply 1).trans (one_mul (1 : ℝ)).symm }
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1, 1, 1, 1, 1,
    ⟨fun δ _ => ((δ : ℝ) / 1) ^ ((2 : ℝ) / (1 + 1)),
      fun δ _ => Real.rpow_pos_of_pos (div_pos δ.2 one_pos) _⟩,
    hss, ⟨one_pos, by norm_num⟩, one_pos, one_pos, one_pos, fun _ _ _ => rfl, ?_⟩
  intro δ z
  exact ⟨(one_mul _).le, (one_mul _).ge⟩

/-- The hypotheses of `AutoIp.tikhonov_orderOptimal_apriori` can fail. -/
theorem AutoIp.tikhonov_orderOptimal_apriori_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ν : ℝ), ∃ (ρ : ℝ), ∃ (cl : ℝ), ∃ (cu : ℝ), ∃ (a : AutoIp.ParameterChoice F), ¬ ((IsSingularSystem K σ v u) ∧ (ν ∈ Set.Ioc (0 : ℝ) (2 : ℝ)) ∧ ((0 : ℝ) < ρ) ∧ ((0 : ℝ) < cl) ∧ ((0 : ℝ) < cu) ∧ (AutoIp.ParameterChoice.IsAPriori a) ∧ (∀ (δ : (↑(Set.Ioi (0 : ℝ)) : Type)) (z : F),
  cl * ((↑δ : ℝ) / ρ) ^ ((2 : ℝ) / (ν + (1 : ℝ))) ≤ (a : (↑(Set.Ioi (0 : ℝ)) : Type) → F → ℝ) δ z ∧
    (a : (↑(Set.Ioi (0 : ℝ)) : Type) → F → ℝ) δ z ≤ cu * ((↑δ : ℝ) / ρ) ^ ((2 : ℝ) / (ν + (1 : ℝ))))) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, 0, 1, 1, 1,
    ⟨fun _ _ => 1, fun _ _ => one_pos⟩, ?_⟩
  rintro ⟨H, _, _, _, _, _, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)

/-- The hypotheses of `AutoIp.norm_spectralReg_tikhonov_sub_le_rpow_two_thirds` can hold together. -/
theorem AutoIp.norm_spectralReg_tikhonov_sub_le_rpow_two_thirds_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ρ : ℝ), ∃ (cl : ℝ), ∃ (cu : ℝ), ∃ (a : AutoIp.ParameterChoice F), (IsSingularSystem K σ v u) ∧ ((0 : ℝ) < ρ) ∧ ((0 : ℝ) < cl) ∧ ((0 : ℝ) < cu) ∧ (∀ (δ : (↑(Set.Ioi (0 : ℝ)) : Type)) (z : F),
  cl * (↑δ : ℝ) ^ (2 / 3 : ℝ) ≤ (a : (↑(Set.Ioi (0 : ℝ)) : Type) → F → ℝ) δ z ∧
    (a : (↑(Set.Ioi (0 : ℝ)) : Type) → F → ℝ) δ z ≤ cu * (↑δ : ℝ) ^ (2 / 3 : ℝ)) :=
  by
  classical
  have hss : IsSingularSystem (ι := Unit) (1 : ℝ →L[ℝ] ℝ)
      (fun _ => 1) (fun _ => 1) (fun _ => 1) :=
    { pos := fun _ => one_pos
      orthonormal_left := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      orthonormal_right := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      span_left := Witnesses.Identity.span_left _ fun _ => rfl
      span_right := Witnesses.Identity.span_right _ fun _ => rfl
      map_left := fun _ => (one_mul (1 : ℝ)).symm
      map_right := fun _ =>
        (Witnesses.Identity.adjoint_one_apply 1).trans (one_mul (1 : ℝ)).symm }
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1, 1, 1, 1,
    ⟨fun δ _ => (δ : ℝ) ^ (2 / 3 : ℝ), fun δ _ => Real.rpow_pos_of_pos δ.2 _⟩,
    hss, one_pos, one_pos, one_pos, ?_⟩
  intro δ z
  exact ⟨(one_mul _).le, (one_mul _).ge⟩

/-- The hypotheses of `AutoIp.norm_spectralReg_tikhonov_sub_le_rpow_two_thirds` can fail. -/
theorem AutoIp.norm_spectralReg_tikhonov_sub_le_rpow_two_thirds_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ρ : ℝ), ∃ (cl : ℝ), ∃ (cu : ℝ), ∃ (a : AutoIp.ParameterChoice F), ¬ ((IsSingularSystem K σ v u) ∧ ((0 : ℝ) < ρ) ∧ ((0 : ℝ) < cl) ∧ ((0 : ℝ) < cu) ∧ (∀ (δ : (↑(Set.Ioi (0 : ℝ)) : Type)) (z : F),
  cl * (↑δ : ℝ) ^ (2 / 3 : ℝ) ≤ (a : (↑(Set.Ioi (0 : ℝ)) : Type) → F → ℝ) δ z ∧
    (a : (↑(Set.Ioi (0 : ℝ)) : Type) → F → ℝ) δ z ≤ cu * (↑δ : ℝ) ^ (2 / 3 : ℝ))) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, 1, 1, 1,
    ⟨fun _ _ => 1, fun _ _ => one_pos⟩, ?_⟩
  rintro ⟨H, _, _, _, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)

/-- The hypotheses of `AutoIp.sourceSet_two_subset_range_adjoint_comp_self` can hold together. -/
theorem AutoIp.sourceSet_two_subset_range_adjoint_comp_self_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ρ : ℝ), (IsSingularSystem K σ v u) ∧ ((0 : ℝ) < ρ) :=
  by
  classical
  have hss : IsSingularSystem (ι := Unit) (1 : ℝ →L[ℝ] ℝ)
      (fun _ => 1) (fun _ => 1) (fun _ => 1) :=
    { pos := fun _ => one_pos
      orthonormal_left := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      orthonormal_right := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      span_left := Witnesses.Identity.span_left _ fun _ => rfl
      span_right := Witnesses.Identity.span_right _ fun _ => rfl
      map_left := fun _ => (one_mul (1 : ℝ)).symm
      map_right := fun _ =>
        (Witnesses.Identity.adjoint_one_apply 1).trans (one_mul (1 : ℝ)).symm }
  exact ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1, 1, hss, one_pos⟩

/-- The hypotheses of `AutoIp.sourceSet_two_subset_range_adjoint_comp_self` can fail. -/
theorem AutoIp.sourceSet_two_subset_range_adjoint_comp_self_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (ρ : ℝ), ¬ ((IsSingularSystem K σ v u) ∧ ((0 : ℝ) < ρ)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, 1, ?_⟩
  rintro ⟨H, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)
