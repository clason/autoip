module

import AutoIp._part_2_reg._ch_20_iterated_tikhonov._thm_iterated_tikhonov_qualification.Spec -- shake: keep
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.iSup_rpow_mul_abs_one_sub_mul_iteratedTikhonovFilter_le` can hold together. -/
theorem AutoIp.iSup_rpow_mul_abs_one_sub_mul_iteratedTikhonovFilter_le_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (m : ℕ), ∃ (ν : ℝ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ((0 : ℝ) < ν) ∧ (ν ≤ (2 : ℝ) * (↑m : ℝ)) :=
  by
  classical
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 0, 1, 1,
    ⟨1, Set.mem_Ioi.2 one_pos⟩, ?_⟩
  exact ⟨one_pos, by norm_num⟩

/-- The hypotheses of `AutoIp.iSup_rpow_mul_abs_one_sub_mul_iteratedTikhonovFilter_le` can fail. -/
theorem AutoIp.iSup_rpow_mul_abs_one_sub_mul_iteratedTikhonovFilter_le_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (m : ℕ), ∃ (ν : ℝ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ¬ (((0 : ℝ) < ν) ∧ (ν ≤ (2 : ℝ) * (↑m : ℝ))) :=
  by
  classical
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 0, 0, 0,
    ⟨1, Set.mem_Ioi.2 one_pos⟩, ?_⟩
  rintro ⟨H, _⟩
  exact absurd H (lt_irrefl 0)
