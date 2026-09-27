module

import AutoIp._part_2_reg._ch_20_iterated_tikhonov._lem_landweber_residual_polynomial.Spec -- shake: keep
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.semiIterativeFilter_landweberResidualPoly` can hold together. -/
theorem AutoIp.semiIterativeFilter_landweberResidualPoly_satisfiable : ∃ (ω : ℝ), ∃ (k : ℕ), ∃ (lam : ℝ), (0 : ℕ) < k :=
  by
  refine ⟨0, 1, 0, ?_⟩
  exact by norm_num

/-- The hypotheses of `AutoIp.semiIterativeFilter_landweberResidualPoly` can fail. -/
theorem AutoIp.semiIterativeFilter_landweberResidualPoly_nontrivial : ∃ (ω : ℝ), ∃ (k : ℕ), ∃ (lam : ℝ), ¬ ((0 : ℕ) < k) :=
  by
  refine ⟨0, 0, 0, ?_⟩
  intro H
  exact absurd H (lt_irrefl 0)
