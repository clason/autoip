module

import AutoIp._part_2_reg._ch_11_moore_penrose._lem_minnorm_unique.Spec -- shake: keep
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Data.EReal.Inv
import Mathlib.Tactic.Bound

/-- The hypotheses of `AutoIp.IsMinimumNorm.unique` can hold together. -/
theorem AutoIp.IsMinimumNorm.unique_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (y : F), ∃ (x : E), ∃ (x' : E), (AutoIp.IsMinimumNorm T y x) ∧ (AutoIp.IsMinimumNorm T y x') :=
  ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    1, 0, 0, 0, ⟨⟨fun _ => by simp, fun z _ => by simp⟩, ⟨fun _ => by simp, fun z _ => by simp⟩⟩⟩

/-- The hypotheses of `AutoIp.IsMinimumNorm.unique` can fail. -/
theorem AutoIp.IsMinimumNorm.unique_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (y : F), ∃ (x : E), ∃ (x' : E), ¬ ((AutoIp.IsMinimumNorm T y x) ∧ (AutoIp.IsMinimumNorm T y x')) :=
  ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    1, 0, 1, 0, by
      rintro ⟨h, -⟩
      have := h.isLeastSquares 0
      simp only [ContinuousLinearMap.one_apply, sub_zero, norm_one, norm_zero] at this
      linarith⟩
