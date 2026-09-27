module

import AutoIp._part_2_reg._ch_20_iterated_tikhonov._lem_iterated_tikhonov_filter.Spec -- shake: keep
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.iteratedTikhonovFilter_isRegularizingFilter` can hold together. -/
theorem AutoIp.iteratedTikhonovFilter_isRegularizingFilter_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (m : ℕ), (0 : ℕ) < m :=
  by
  classical
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 0, 1, ?_⟩
  exact by norm_num

/-- The hypotheses of `AutoIp.iteratedTikhonovFilter_isRegularizingFilter` can fail. -/
theorem AutoIp.iteratedTikhonovFilter_isRegularizingFilter_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (m : ℕ), ¬ ((0 : ℕ) < m) :=
  by
  classical
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 0, 0, ?_⟩
  intro H
  exact absurd H (lt_irrefl 0)

/-- The hypotheses of `AutoIp.iSup_abs_iteratedTikhonovFilter_le` can hold together. -/
theorem AutoIp.iSup_abs_iteratedTikhonovFilter_le_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (m : ℕ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), (0 : ℕ) < m :=
  by
  classical
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 0, 1, ⟨1, Set.mem_Ioi.2 one_pos⟩, ?_⟩
  exact by norm_num

/-- The hypotheses of `AutoIp.iSup_abs_iteratedTikhonovFilter_le` can fail. -/
theorem AutoIp.iSup_abs_iteratedTikhonovFilter_le_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (m : ℕ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ¬ ((0 : ℕ) < m) :=
  by
  classical
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 0, 0, ⟨1, Set.mem_Ioi.2 one_pos⟩, ?_⟩
  intro H
  exact absurd H (lt_irrefl 0)
