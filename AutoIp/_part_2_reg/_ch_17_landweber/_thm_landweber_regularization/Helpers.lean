/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_standard_filters
public import AutoIp._part_2_reg._ch_17_landweber._def_landweber
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_hom
import AutoIp._part_2_reg._ch_15_spectral_regularization._thm_spectral_is_regularization
import AutoIp._part_2_reg._ch_17_landweber._lem_landweber_closed_form
import Mathlib.Tactic.Polynomial.Basic
import AutoIp.Auxiliary.BoundedOnIcc
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- On `[0, κ]` the Landweber filter at `α = 1/m` is the polynomial
`ω ∑_{n<m} (1 - ωt)ⁿ`. -/
public theorem landweberFilter_eq_geom (K : E →L[𝕜] F) {ω : ℝ}
    (hω : 0 < ω ∧ ω * ‖K‖ ^ 2 ≤ 1) {m : ℕ} (hm : 0 < m)
    {α : Set.Ioi (0 : ℝ)} (hα : (α : ℝ) = 1 / m)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2)) :
    landweberFilter ω α t = ω * ∑ n ∈ Finset.range m, (1 - ω * t) ^ n := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hexp : (1 : ℝ) / (α : ℝ) = (m : ℝ) := by
    rw [hα, one_div_one_div]
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · rw [← h0, landweberFilter_zero, hα]
    simp
  · have hq : (1 : ℝ) - ω * t ≠ 1 := by
      have : ω * t ≠ 0 := ne_of_gt (mul_pos hω.1 hpos)
      intro h; apply this; linarith
    have ht0 : t ≠ 0 := ne_of_gt hpos
    have hw0 : ω ≠ 0 := ne_of_gt hω.1
    rw [landweberFilter_of_ne_zero ht0, hexp, Real.rpow_natCast, geom_sum_eq hq,
      show (1 - ω * t) - 1 = -(ω * t) from by ring]
    field_simp
    ring

end AutoIp
