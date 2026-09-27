module

import AutoIp._part_2_reg._ch_20_iterated_tikhonov._lem_iterated_tikhonov_qualification_sharp.Spec -- shake: keep
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.iteratedTikhonov_qualification` can hold together. -/
theorem AutoIp.iteratedTikhonov_qualification_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (m : ℕ), (K ≠ (0 : E →L[𝕜] F)) ∧ ((0 : ℕ) < m) :=
  by
  classical
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 1, 1, ?_⟩
  refine ⟨fun h => one_ne_zero (DFunLike.congr_fun h (1 : ℝ)), Nat.one_pos⟩

/-- The hypotheses of `AutoIp.iteratedTikhonov_qualification` can fail. -/
theorem AutoIp.iteratedTikhonov_qualification_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (m : ℕ), ¬ ((K ≠ (0 : E →L[𝕜] F)) ∧ ((0 : ℕ) < m)) :=
  by
  classical
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 0, 1, ?_⟩
  rintro ⟨H, _⟩
  exact H rfl

/-- The hypotheses of `AutoIp.qualification_iteratedTikhonovFilter` can hold together. -/
theorem AutoIp.qualification_iteratedTikhonovFilter_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (m : ℕ), (K ≠ (0 : E →L[𝕜] F)) ∧ ((0 : ℕ) < m) :=
  by
  classical
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 1, 1, ?_⟩
  refine ⟨fun h => one_ne_zero (DFunLike.congr_fun h (1 : ℝ)), Nat.one_pos⟩

/-- The hypotheses of `AutoIp.qualification_iteratedTikhonovFilter` can fail. -/
theorem AutoIp.qualification_iteratedTikhonovFilter_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (m : ℕ), ¬ ((K ≠ (0 : E →L[𝕜] F)) ∧ ((0 : ℕ) < m)) :=
  by
  classical
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 0, 1, ?_⟩
  rintro ⟨H, _⟩
  exact H rfl

/-- The hypotheses of `AutoIp.not_exists_qualification_const_of_gt` can hold together. -/
theorem AutoIp.not_exists_qualification_const_of_gt_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (m : ℕ), ∃ (ν : ℝ), (K ≠ (0 : E →L[𝕜] F)) ∧ ((0 : ℕ) < m) ∧ ((2 : ℝ) * (↑m : ℝ) < ν) :=
  by
  classical
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 1, 1, 3, ?_⟩
  refine ⟨fun h => one_ne_zero (DFunLike.congr_fun h (1 : ℝ)), Nat.one_pos, by norm_num⟩

/-- The hypotheses of `AutoIp.not_exists_qualification_const_of_gt` can fail. -/
theorem AutoIp.not_exists_qualification_const_of_gt_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (m : ℕ), ∃ (ν : ℝ), ¬ ((K ≠ (0 : E →L[𝕜] F)) ∧ ((0 : ℕ) < m) ∧ ((2 : ℝ) * (↑m : ℝ) < ν)) :=
  by
  classical
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 0, 1, 0, ?_⟩
  rintro ⟨H, _, _⟩
  exact H rfl
