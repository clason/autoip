module

import AutoIp._part_2_reg._ch_14_order_optimality._thm_order_optimal_implies_convergence.Spec -- shake: keep

open Filter Topology
open scoped ENNReal

/-- The hypotheses of `AutoIp.isRegularizationMethod_of_orderOptimal` can hold together. -/
theorem AutoIp.isRegularizationMethod_of_orderOptimal_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), ∃ (a : AutoIp.ParameterChoice F), ∃ (ν : ℝ), ∃ (τ₀ : ℝ), ∃ (c : ℝ), ∃ (τ : ℝ), (Dense (↑(LinearMap.range (↑K : E →ₗ[𝕜] F)) : Set F)) ∧ ((1 : ℝ) ≤ τ₀) ∧ (∀ τ > τ₀,
  ∀ ρ > (0 : ℝ),
    ∀ (hτ : (0 : ℝ) < τ),
      AutoIp.IsOrderOptimal K (fun (α : (↑(Set.Ioi (0 : ℝ)) : Type)) (z : F) => (R α : F → E) z)
        (AutoIp.ParameterChoice.scale a τ hτ) hs ν ρ c) ∧ (τ₀ < τ) ∧ ((0 : ℝ) < τ) :=
  by
  classical
  have hsub : ∀ p q : Submodule ℝ Unit, p = q := fun p q => Subsingleton.elim p q
  have hss : IsSingularSystem (ι := Empty) (0 : Unit →L[ℝ] Unit)
      (fun _ => 0) (fun _ => ()) (fun _ => ()) :=
    { pos := fun i => i.elim
      orthonormal_left := ⟨fun i => i.elim, fun {i _} _ => i.elim⟩
      orthonormal_right := ⟨fun i => i.elim, fun {i _} _ => i.elim⟩
      span_left := hsub _ _
      span_right := hsub _ _
      map_left := fun i => i.elim
      map_right := fun i => i.elim }
  have hnorm : ∀ x : Unit, ‖x‖ = 0 := fun x => by
    rw [Subsingleton.elim x 0, norm_zero]
  refine ⟨ℝ, inferInstance, Unit, Unit, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, 0, Empty, fun _ => 0, fun _ => (),
    fun _ => (), hss, fun _ => 0, ⟨fun _ _ => 1, fun _ _ => one_pos⟩, 1, 1, 1, 2, ?_,
    le_rfl, ?_, by norm_num, by norm_num⟩
  · intro y
    rw [Subsingleton.elim y 0]
    exact subset_closure (Submodule.zero_mem _)
  · intro τ _ ρ hρ hτ
    refine ⟨one_pos, hρ, le_rfl, fun x _ δ hδ => ?_⟩
    unfold AutoIp.worstCaseError
    refine iSup₂_le fun z _ => ?_
    rw [← ofReal_norm, hnorm, ENNReal.ofReal_zero]
    exact bot_le

/-- The hypotheses of `AutoIp.isRegularizationMethod_of_orderOptimal` can fail. -/
theorem AutoIp.isRegularizationMethod_of_orderOptimal_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), ∃ (a : AutoIp.ParameterChoice F), ∃ (ν : ℝ), ∃ (τ₀ : ℝ), ∃ (c : ℝ), ∃ (τ : ℝ), ¬ ((Dense (↑(LinearMap.range (↑K : E →ₗ[𝕜] F)) : Set F)) ∧ ((1 : ℝ) ≤ τ₀) ∧ (∀ τ > τ₀,
  ∀ ρ > (0 : ℝ),
    ∀ (hτ : (0 : ℝ) < τ),
      AutoIp.IsOrderOptimal K (fun (α : (↑(Set.Ioi (0 : ℝ)) : Type)) (z : F) => (R α : F → E) z)
        (AutoIp.ParameterChoice.scale a τ hτ) hs ν ρ c) ∧ (τ₀ < τ) ∧ ((0 : ℝ) < τ)) :=
  by
  classical
  have hsub : ∀ p q : Submodule ℝ Unit, p = q := fun p q => Subsingleton.elim p q
  have hss : IsSingularSystem (ι := Empty) (0 : Unit →L[ℝ] Unit)
      (fun _ => 0) (fun _ => ()) (fun _ => ()) :=
    { pos := fun i => i.elim
      orthonormal_left := ⟨fun i => i.elim, fun {i _} _ => i.elim⟩
      orthonormal_right := ⟨fun i => i.elim, fun {i _} _ => i.elim⟩
      span_left := hsub _ _
      span_right := hsub _ _
      map_left := fun i => i.elim
      map_right := fun i => i.elim }
  refine ⟨ℝ, inferInstance, Unit, Unit, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, 0, Empty, fun _ => 0, fun _ => (),
    fun _ => (), hss, fun _ => 0, ⟨fun _ _ => 1, fun _ _ => one_pos⟩, 1, 0, 1, 2, ?_⟩
  rintro ⟨-, h, -⟩
  norm_num at h
