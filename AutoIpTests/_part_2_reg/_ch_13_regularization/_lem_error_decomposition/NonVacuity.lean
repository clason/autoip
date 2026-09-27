module

import AutoIp._part_2_reg._ch_13_regularization._lem_error_decomposition.Spec -- shake: keep

open Filter Topology

/-- The hypotheses of `AutoIp.norm_sub_moorePenrose_le` can hold together. -/
theorem AutoIp.norm_sub_moorePenrose_le_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), ∃ (y : F), ∃ (z : F), ∃ (δ : ℝ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), (y ∈ AutoIp.mpDomain T) ∧ (‖y - z‖ ≤ δ) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 1, fun α => (1 + (α : ℝ))⁻¹ • (1 : ℝ →L[ℝ] ℝ), 1, 1 / 2, 1 / 2,
    ⟨1, Set.mem_Ioi.2 one_pos⟩, Submodule.mem_sup_left ⟨1, rfl⟩, ?_⟩
  norm_num

/-- The hypotheses of `AutoIp.norm_sub_moorePenrose_le` can fail. -/
theorem AutoIp.norm_sub_moorePenrose_le_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), ∃ (y : F), ∃ (z : F), ∃ (δ : ℝ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ¬ ((y ∈ AutoIp.mpDomain T) ∧ (‖y - z‖ ≤ δ)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 0, fun _ => 0, 0, 0, -1, ⟨1, Set.mem_Ioi.2 one_pos⟩, ?_⟩
  rintro ⟨-, h⟩
  norm_num at h
