module

import AutoIp._part_1_funcanal._ch_06_compact_operators._thm_schauder.Spec -- shake: keep
import AutoIpTests.Witnesses.Diagonal

open Metric

/-- The hypotheses of `IsCompactOperator.dualMap` can hold together. -/
theorem IsCompactOperator.dualMap_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : NormedSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : NormedSpace 𝕜 F), ∃ (T : E →L[𝕜] F), IsCompactOperator (⇑T : E → F) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 0
    , ?_⟩
  exact isCompactOperator_zero

/-- The hypotheses of `IsCompactOperator.dualMap` can fail. -/
theorem IsCompactOperator.dualMap_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : NormedSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : NormedSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ¬ (IsCompactOperator (⇑T : E → F)) :=
  ⟨ℝ, inferInstance, Witnesses.Diagonal.H, Witnesses.Diagonal.H, inferInstance, inferInstance, inferInstance,
    inferInstance, 1, Witnesses.Diagonal.not_isCompactOperator_one⟩
