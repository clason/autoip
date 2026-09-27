module

import AutoIp._part_1_funcanal._ch_08_svd._cor_sigma_null.Spec -- shake: keep
import AutoIpTests.Witnesses.Diagonal

open scoped InnerProductSpace

/-- The hypotheses of `IsSingularSystem.infinite_of_not_finiteDimensional_range` can hold together. -/
theorem IsSingularSystem.infinite_of_not_finiteDimensional_range_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), (IsSingularSystem K σ v u) ∧ (¬FiniteDimensional 𝕜 ↥(LinearMap.range (↑K : E →ₗ[𝕜] F))) :=
  by
  have hker : (LinearMap.ker (Witnesses.Diagonal.T :
      Witnesses.Diagonal.H →ₗ[ℝ] Witnesses.Diagonal.H))ᗮ = ⊤ := by
    rw [Witnesses.Diagonal.ker_T, Submodule.bot_orthogonal_eq_top]
  have hss : IsSingularSystem Witnesses.Diagonal.T Witnesses.Diagonal.w
      Witnesses.Diagonal.e Witnesses.Diagonal.e :=
    { pos := Witnesses.Diagonal.w_pos
      orthonormal_left := Witnesses.Diagonal.orthonormal_e
      orthonormal_right := Witnesses.Diagonal.orthonormal_e
      span_left := Witnesses.Diagonal.span_e_dense.trans hker.symm
      span_right := Witnesses.Diagonal.span_e_dense.trans
        Witnesses.Diagonal.topologicalClosure_range_T.symm
      map_left := fun i => by simpa using Witnesses.Diagonal.T_e i
      map_right := fun i => by simpa using Witnesses.Diagonal.adjoint_T_e i }
  exact ⟨ℝ, inferInstance, Witnesses.Diagonal.H, Witnesses.Diagonal.H, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Witnesses.Diagonal.T, ℕ, _, _, _, hss,
    Witnesses.Diagonal.not_finiteDimensional_range⟩

/-- The hypotheses of `IsSingularSystem.infinite_of_not_finiteDimensional_range` can fail. -/
theorem IsSingularSystem.infinite_of_not_finiteDimensional_range_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ¬ ((IsSingularSystem K σ v u) ∧ (¬FiniteDimensional 𝕜 ↥(LinearMap.range (↑K : E →ₗ[𝕜] F)))) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  rintro ⟨H, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)

/-- The hypotheses of `IsOrderedSingularSystem.infinite_and_tendsto_zero_of_not_finiteDimensional_range` can hold together. -/
theorem IsOrderedSingularSystem.infinite_and_tendsto_zero_of_not_finiteDimensional_range_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (I : Set ℕ), ∃ (σ : (↑I : Type) → ℝ), ∃ (v : (↑I : Type) → E), ∃ (u : (↑I : Type) → F), (IsOrderedSingularSystem K σ v u) ∧ (¬FiniteDimensional 𝕜 ↥(LinearMap.range (↑K : E →ₗ[𝕜] F))) :=
  by
  have hker : (LinearMap.ker (Witnesses.Diagonal.T :
      Witnesses.Diagonal.H →ₗ[ℝ] Witnesses.Diagonal.H))ᗮ = ⊤ := by
    rw [Witnesses.Diagonal.ker_T, Submodule.bot_orthogonal_eq_top]
  have hss : IsSingularSystem Witnesses.Diagonal.T Witnesses.Diagonal.w
      Witnesses.Diagonal.e Witnesses.Diagonal.e :=
    { pos := Witnesses.Diagonal.w_pos
      orthonormal_left := Witnesses.Diagonal.orthonormal_e
      orthonormal_right := Witnesses.Diagonal.orthonormal_e
      span_left := Witnesses.Diagonal.span_e_dense.trans hker.symm
      span_right := Witnesses.Diagonal.span_e_dense.trans
        Witnesses.Diagonal.topologicalClosure_range_T.symm
      map_left := fun i => by simpa using Witnesses.Diagonal.T_e i
      map_right := fun i => by simpa using Witnesses.Diagonal.adjoint_T_e i }
  have hr : Set.range (fun i : (Set.univ : Set ℕ) => Witnesses.Diagonal.e i.1) =
      Set.range Witnesses.Diagonal.e := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨⟨n, Set.mem_univ n⟩, rfl⟩
  have hon : Orthonormal ℝ (fun i : (Set.univ : Set ℕ) => Witnesses.Diagonal.e i.1) :=
    Witnesses.Diagonal.orthonormal_e.comp _ Subtype.val_injective
  have hval : Filter.Tendsto (fun i : (Set.univ : Set ℕ) => i.1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop_of_monotone (fun _ _ h => h)
      (fun n => ⟨⟨n, Set.mem_univ n⟩, le_rfl⟩)
  have hoss : IsOrderedSingularSystem (I := Set.univ) Witnesses.Diagonal.T
      (fun i => Witnesses.Diagonal.w i.1) (fun i => Witnesses.Diagonal.e i.1)
      (fun i => Witnesses.Diagonal.e i.1) :=
    { pos := fun i => hss.pos i.1
      orthonormal_left := hon
      orthonormal_right := hon
      span_left := by rw [hr]; exact hss.span_left
      span_right := by rw [hr]; exact hss.span_right
      map_left := fun i => hss.map_left i.1
      map_right := fun i => hss.map_right i.1
      isLowerSet := fun _ _ _ _ => Set.mem_univ _
      antitone := fun _ _ h => Witnesses.Diagonal.w_antitone h
      tendsto_zero := fun _ => Witnesses.Diagonal.tendsto_w.comp hval }
  exact ⟨ℝ, inferInstance, Witnesses.Diagonal.H, Witnesses.Diagonal.H, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Witnesses.Diagonal.T, Set.univ, _, _, _, hoss,
    Witnesses.Diagonal.not_finiteDimensional_range⟩

/-- The hypotheses of `IsOrderedSingularSystem.infinite_and_tendsto_zero_of_not_finiteDimensional_range` can fail. -/
theorem IsOrderedSingularSystem.infinite_and_tendsto_zero_of_not_finiteDimensional_range_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (I : Set ℕ), ∃ (σ : (↑I : Type) → ℝ), ∃ (v : (↑I : Type) → E), ∃ (u : (↑I : Type) → F), ¬ ((IsOrderedSingularSystem K σ v u) ∧ (¬FiniteDimensional 𝕜 ↥(LinearMap.range (↑K : E →ₗ[𝕜] F)))) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Set.univ, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  rintro ⟨H, _⟩
  exact absurd (H.pos ⟨0, Set.mem_univ 0⟩) (lt_irrefl 0)
