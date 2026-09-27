module

import AutoIp._part_2_reg._ch_15_spectral_regularization._def_standard_filters.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity

open Filter Topology

/-- The hypotheses of `AutoIp.landweberFilter_of_ne_zero` can hold together. -/
theorem AutoIp.landweberFilter_of_ne_zero_satisfiable : ∃ (lam : ℝ), ∃ (ω : ℝ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), lam ≠ (0 : ℝ) :=
  by
  refine ⟨1, 0, ⟨1, Set.mem_Ioi.2 one_pos⟩, ?_⟩
  exact by norm_num

/-- The hypotheses of `AutoIp.landweberFilter_of_ne_zero` can fail. -/
theorem AutoIp.landweberFilter_of_ne_zero_nontrivial : ∃ (lam : ℝ), ∃ (ω : ℝ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ¬ (lam ≠ (0 : ℝ)) :=
  by
  refine ⟨0, 0, ⟨1, Set.mem_Ioi.2 one_pos⟩, ?_⟩
  intro H
  exact H rfl

/-- The hypotheses of `AutoIp.landweberFilter_isRegularizingFilter` can hold together. -/
theorem AutoIp.landweberFilter_isRegularizingFilter_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (ω : ℝ), (0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) ≤ (1 : ℝ) :=
  by
  classical
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    1, 1, ?_⟩
  have h1 : ‖(1 : ℝ →L[ℝ] ℝ)‖ = 1 := Witnesses.Identity.norm_one'
  exact ⟨one_pos, by rw [h1]; norm_num⟩

/-- The hypotheses of `AutoIp.landweberFilter_isRegularizingFilter` can fail. -/
theorem AutoIp.landweberFilter_isRegularizingFilter_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (ω : ℝ), ¬ ((0 : ℝ) < ω ∧ ω * ‖K‖ ^ (2 : ℕ) ≤ (1 : ℝ)) :=
  by
  classical
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 0, 0, ?_⟩
  intro H
  exact absurd H (by simp)
