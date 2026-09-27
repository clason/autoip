module

import AutoIp._part_2_reg._ch_14_order_optimality._thm_modulus_attained.Spec -- shake: keep
import AutoIpTests.Witnesses.Diagonal

open Filter Topology
open scoped ENNReal

/-- The hypotheses of `AutoIp.exists_seq_tendsto_zero_modulusOfContinuity_eq` can hold together. -/
theorem AutoIp.exists_seq_tendsto_zero_modulusOfContinuity_eq_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (I : Set ℕ), ∃ (σ : (↑I : Type) → ℝ), ∃ (v : (↑I : Type) → E), ∃ (u : (↑I : Type) → F), ∃ (ν : ℝ), ∃ (ρ : ℝ), (IsOrderedSingularSystem K σ v u) ∧ (¬FiniteDimensional 𝕜 ↥(LinearMap.range (↑K : E →ₗ[𝕜] F))) ∧ ((0 : ℝ) < ν) ∧ ((0 : ℝ) < ρ) :=
  by
  classical
  let e : ↥(Set.univ : Set ℕ) → Witnesses.Diagonal.H := fun i => Witnesses.Diagonal.e i
  let σ : ↥(Set.univ : Set ℕ) → ℝ := fun i => Witnesses.Diagonal.w i
  have hrange : Set.range e = Set.range Witnesses.Diagonal.e := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩
    · rintro ⟨n, rfl⟩; exact ⟨⟨n, Set.mem_univ n⟩, rfl⟩
  have hspan : (Submodule.span ℝ (Set.range e)).topologicalClosure = ⊤ := by
    rw [hrange]; exact Witnesses.Diagonal.span_e_dense
  have hss : IsOrderedSingularSystem Witnesses.Diagonal.T σ e e :=
    { pos := fun i => Witnesses.Diagonal.w_pos i
      orthonormal_left := Witnesses.Diagonal.orthonormal_e.comp _
        Subtype.val_injective
      orthonormal_right := Witnesses.Diagonal.orthonormal_e.comp _
        Subtype.val_injective
      span_left := by
        rw [hspan, Witnesses.Diagonal.ker_T, Submodule.bot_orthogonal_eq_top]
      span_right := by
        rw [hspan, Witnesses.Diagonal.topologicalClosure_range_T]
      map_left := fun i => Witnesses.Diagonal.T_e i
      map_right := fun i => Witnesses.Diagonal.adjoint_T_e i
      isLowerSet := fun _ _ _ _ => Set.mem_univ _
      antitone := fun i j hij => Witnesses.Diagonal.w_antitone hij
      tendsto_zero := fun _ => by
        have h : Filter.Tendsto (fun i : ↥(Set.univ : Set ℕ) => (i : ℕ)) atTop atTop :=
          tendsto_atTop_atTop.2 fun b => ⟨⟨b, Set.mem_univ b⟩, fun a ha => ha⟩
        exact Witnesses.Diagonal.tendsto_w.comp h }
  exact ⟨ℝ, inferInstance, Witnesses.Diagonal.H, Witnesses.Diagonal.H, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Witnesses.Diagonal.T, Set.univ, σ, e, e, 1, 1, hss,
    Witnesses.Diagonal.not_finiteDimensional_range, one_pos, one_pos⟩

/-- The hypotheses of `AutoIp.exists_seq_tendsto_zero_modulusOfContinuity_eq` can fail. -/
theorem AutoIp.exists_seq_tendsto_zero_modulusOfContinuity_eq_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (I : Set ℕ), ∃ (σ : (↑I : Type) → ℝ), ∃ (v : (↑I : Type) → E), ∃ (u : (↑I : Type) → F), ∃ (ν : ℝ), ∃ (ρ : ℝ), ¬ ((IsOrderedSingularSystem K σ v u) ∧ (¬FiniteDimensional 𝕜 ↥(LinearMap.range (↑K : E →ₗ[𝕜] F))) ∧ ((0 : ℝ) < ν) ∧ ((0 : ℝ) < ρ)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Set.univ, fun _ => 0, fun _ => 0, fun _ => 0, 1, 1, ?_⟩
  rintro ⟨H, _, _, _⟩
  exact absurd (H.pos ⟨0, Set.mem_univ 0⟩) (lt_irrefl 0)
