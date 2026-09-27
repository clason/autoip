module

import AutoIp._part_2_reg._ch_22_balancing._def_balancing.Spec -- shake: keep

/-- The hypotheses of `AutoIp.balancingIndex` can hold together. -/
theorem AutoIp.balancingIndex_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), ∃ (CR : ℝ), ∃ (δ : ℝ), ∃ (N : ℕ), ∃ (grid : ℕ → (↑(Set.Ioi (0 : ℝ)) : Type)), ∃ (z : F), (0 : ℝ) ≤ CR * δ :=
  by
  refine ⟨ℝ, inferInstance, PUnit, PUnit, inferInstance, inferInstance, inferInstance, inferInstance,
    fun _ => 0, 0, 0, 0, fun _ => ⟨1, Set.mem_Ioi.2 one_pos⟩, 0, ?_⟩
  norm_num

/-- The hypotheses of `AutoIp.balancingIndex` can fail. -/
theorem AutoIp.balancingIndex_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), ∃ (CR : ℝ), ∃ (δ : ℝ), ∃ (N : ℕ), ∃ (grid : ℕ → (↑(Set.Ioi (0 : ℝ)) : Type)), ∃ (z : F), ¬ ((0 : ℝ) ≤ CR * δ) :=
  by
  refine ⟨ℝ, inferInstance, PUnit, PUnit, inferInstance, inferInstance, inferInstance, inferInstance,
    fun _ => 0, -1, 1, 0, fun _ => ⟨1, Set.mem_Ioi.2 one_pos⟩, 0, ?_⟩
  norm_num

/-- The hypotheses of `AutoIp.IsBalancingChoiceOnGeometricGrid` can hold together. -/
theorem AutoIp.IsBalancingChoiceOnGeometricGrid_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), ∃ (CR : ℝ), ∃ (δ : ℝ), ∃ (N : ℕ), ∃ (grid : ℕ → (↑(Set.Ioi (0 : ℝ)) : Type)), ∃ (q : ℝ), ∃ (z : F), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), (0 : ℝ) ≤ CR * δ :=
  by
  refine ⟨ℝ, inferInstance, PUnit, PUnit, inferInstance, inferInstance, inferInstance, inferInstance,
    fun _ => 0, 0, 0, 0, fun _ => ⟨1, Set.mem_Ioi.2 one_pos⟩, 2, 0, ⟨1, Set.mem_Ioi.2 one_pos⟩,
    ?_⟩
  norm_num

/-- The hypotheses of `AutoIp.IsBalancingChoiceOnGeometricGrid` can fail. -/
theorem AutoIp.IsBalancingChoiceOnGeometricGrid_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), ∃ (CR : ℝ), ∃ (δ : ℝ), ∃ (N : ℕ), ∃ (grid : ℕ → (↑(Set.Ioi (0 : ℝ)) : Type)), ∃ (q : ℝ), ∃ (z : F), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ¬ ((0 : ℝ) ≤ CR * δ) :=
  by
  refine ⟨ℝ, inferInstance, PUnit, PUnit, inferInstance, inferInstance, inferInstance, inferInstance,
    fun _ => 0, -1, 1, 0, fun _ => ⟨1, Set.mem_Ioi.2 one_pos⟩, 2, 0, ⟨1, Set.mem_Ioi.2 one_pos⟩,
    ?_⟩
  norm_num
