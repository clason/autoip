module

import AutoIp._part_2_reg._ch_20_iterated_tikhonov._def_iterated_tikhonov.Spec -- shake: keep
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.iteratedTikhonovFilter_of_ne_zero` can hold together. -/
theorem AutoIp.iteratedTikhonovFilter_of_ne_zero_satisfiable : ∃ (lam : ℝ), ∃ (m : ℕ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), lam ≠ (0 : ℝ) :=
  by
  refine ⟨1, 0, ⟨1, Set.mem_Ioi.2 one_pos⟩, ?_⟩
  exact by norm_num

/-- The hypotheses of `AutoIp.iteratedTikhonovFilter_of_ne_zero` can fail. -/
theorem AutoIp.iteratedTikhonovFilter_of_ne_zero_nontrivial : ∃ (lam : ℝ), ∃ (m : ℕ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ¬ (lam ≠ (0 : ℝ)) :=
  by
  refine ⟨0, 0, ⟨1, Set.mem_Ioi.2 one_pos⟩, ?_⟩
  intro H
  exact H rfl

/-- The hypotheses of `AutoIp.iteratedTikhonovFilter_one` can hold together. -/
theorem AutoIp.iteratedTikhonovFilter_one_satisfiable : ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ∃ (lam : ℝ), (0 : ℝ) ≤ lam :=
  by
  refine ⟨⟨1, Set.mem_Ioi.2 one_pos⟩, 0, ?_⟩
  exact by norm_num

/-- The hypotheses of `AutoIp.iteratedTikhonovFilter_one` can fail. -/
theorem AutoIp.iteratedTikhonovFilter_one_nontrivial : ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ∃ (lam : ℝ), ¬ ((0 : ℝ) ≤ lam) :=
  by
  refine ⟨⟨1, Set.mem_Ioi.2 one_pos⟩, -1, ?_⟩
  intro H
  linarith

/-- The hypotheses of `AutoIp.one_sub_mul_iteratedTikhonovFilter` can hold together. -/
theorem AutoIp.one_sub_mul_iteratedTikhonovFilter_satisfiable : ∃ (m : ℕ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ∃ (lam : ℝ), (0 : ℝ) < lam :=
  by
  refine ⟨0, ⟨1, Set.mem_Ioi.2 one_pos⟩, 1, ?_⟩
  exact by norm_num

/-- The hypotheses of `AutoIp.one_sub_mul_iteratedTikhonovFilter` can fail. -/
theorem AutoIp.one_sub_mul_iteratedTikhonovFilter_nontrivial : ∃ (m : ℕ), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ∃ (lam : ℝ), ¬ ((0 : ℝ) < lam) :=
  by
  refine ⟨0, ⟨1, Set.mem_Ioi.2 one_pos⟩, 0, ?_⟩
  intro H
  exact absurd H (lt_irrefl 0)
