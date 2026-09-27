module

import AutoIp._part_1_funcanal._ch_07_spectral_theory._thm_max_eigenvalue.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity

open scoped InnerProductSpace

/-- The hypotheses of `IsSelfAdjoint.exists_eigenvalue_norm_eq_norm` can hold together. -/
theorem IsSelfAdjoint.exists_eigenvalue_norm_eq_norm_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (H : Type), ∃ (x3 : NormedAddCommGroup H), ∃ (x4 : InnerProductSpace 𝕜 H), ∃ (x5 : CompleteSpace H), ∃ (K : H →L[𝕜] H), (IsSelfAdjoint K) ∧ (IsCompactOperator (⇑K : H → H)) ∧ (K ≠ (0 : H →L[𝕜] H)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, inferInstance, 1, ?_⟩
  exact ⟨IsSelfAdjoint.one _, isCompactOperator_of_locallyCompactSpace_dom _,
    Witnesses.Identity.one_ne_zero'⟩

/-- The hypotheses of `IsSelfAdjoint.exists_eigenvalue_norm_eq_norm` can fail. -/
theorem IsSelfAdjoint.exists_eigenvalue_norm_eq_norm_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (H : Type), ∃ (x3 : NormedAddCommGroup H), ∃ (x4 : InnerProductSpace 𝕜 H), ∃ (x5 : CompleteSpace H), ∃ (K : H →L[𝕜] H), ¬ ((IsSelfAdjoint K) ∧ (IsCompactOperator (⇑K : H → H)) ∧ (K ≠ (0 : H →L[𝕜] H))) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, inferInstance, 0, ?_⟩
  rintro ⟨_, _, H⟩
  exact H rfl
