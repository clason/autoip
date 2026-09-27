module

import AutoIp._part_2_reg._ch_22_balancing._lem_balancing_nonempty.Spec -- shake: keep
import Mathlib.Analysis.InnerProductSpace.Basic

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.balancingIndex_spec` can hold together. -/
theorem AutoIp.balancingIndex_spec_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), ∃ (CR : ℝ), ∃ (δ : ℝ), ∃ (N : ℕ), ∃ (grid : ℕ → (↑(Set.Ioi (0 : ℝ)) : Type)), ∃ (z : F), ((0 : ℝ) ≤ CR) ∧ ((0 : ℝ) ≤ δ) :=
  by
  classical
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 0, 0, 0, 0, fun _ => ⟨1, Set.mem_Ioi.2 one_pos⟩,
    0, ?_⟩
  exact ⟨by norm_num, by norm_num⟩

/-- The hypotheses of `AutoIp.balancingIndex_spec` can fail. -/
theorem AutoIp.balancingIndex_spec_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), ∃ (CR : ℝ), ∃ (δ : ℝ), ∃ (N : ℕ), ∃ (grid : ℕ → (↑(Set.Ioi (0 : ℝ)) : Type)), ∃ (z : F), ¬ (((0 : ℝ) ≤ CR) ∧ ((0 : ℝ) ≤ δ)) :=
  by
  classical
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 0, -1, 0, 0,
    fun _ => ⟨1, Set.mem_Ioi.2 one_pos⟩, 0, ?_⟩
  rintro ⟨H, _⟩
  exact absurd H (by norm_num)
