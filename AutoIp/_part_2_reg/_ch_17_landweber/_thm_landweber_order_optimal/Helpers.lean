/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_12_picard._def_source_set
public import AutoIp._part_2_reg._ch_13_regularization._def_discrepancy_principle
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_qualification
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_standard_filters
import AutoIp._part_2_reg._ch_15_spectral_regularization._thm_discrepancy_order_optimal
import AutoIp.Auxiliary.ExpBound
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- Pointwise condition (F) for the Landweber filter: `|φ_α(λ)| ≤ ω(1-ωκ)⁻¹ α⁻¹` for
`λ ∈ (0,κ]`. -/
public theorem landweberFilter_abs_le {ω κ lam : ℝ} {α : Set.Ioi (0 : ℝ)} (hω : 0 < ω)
    (hωκ : ω * κ < 1) (hlam : lam ∈ Set.Ioc (0 : ℝ) κ) :
    |landweberFilter ω α lam| ≤ ω * (1 - ω * κ)⁻¹ * (α : ℝ)⁻¹ := by
  have hα : (0 : ℝ) < (α : ℝ) := α.2
  obtain ⟨hl0, hlk⟩ := hlam
  set t : ℝ := 1 / (α : ℝ) with ht
  have ht0 : 0 < t := by positivity
  set c : ℝ := 1 - ω * lam with hc
  have hωlam : ω * lam ≤ ω * κ := by nlinarith
  have hc1 : c < 1 := by simp only [hc, sub_lt_self_iff]; positivity
  have hc0 : 0 < c := by simp only [hc, sub_pos]; nlinarith
  have hlog : Real.log (1/c) ≤ (1 - c)/c := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1/c by positivity)
    calc Real.log (1/c) ≤ 1/c - 1 := this
      _ = (1 - c)/c := by field_simp
  have hcpow : c ^ t = Real.exp (-(t * Real.log (1/c))) := by
    rw [Real.rpow_def_of_pos hc0]
    congr 1
    rw [Real.log_div one_ne_zero (ne_of_gt hc0), Real.log_one]
    ring
  have hkey : 1 - c ^ t ≤ t * Real.log (1/c) := by
    rw [hcpow]
    have hu : 0 ≤ t * Real.log (1/c) := by
      have : 0 ≤ Real.log (1/c) := Real.log_nonneg (by rw [le_div_iff₀ hc0]; linarith)
      positivity
    nlinarith [Real.add_one_le_exp (-(t * Real.log (1/c)))]
  have hcpow_le : c ^ t ≤ 1 := Real.rpow_le_one hc0.le hc1.le ht0.le
  have hcpos : (0:ℝ) < 1 - ω * κ := by linarith
  have hcge : 1 - ω * κ ≤ c := by simp only [hc, sub_le_sub_iff_left]; linarith
  have hchain : 1 - c ^ t ≤ t * (ω * lam) / (1 - ω * κ) := by
    have h1 : t * Real.log (1/c) ≤ t * ((1 - c)/c) :=
      mul_le_mul_of_nonneg_left hlog ht0.le
    have h2 : (1 - c) / c ≤ (ω * lam) / (1 - ω * κ) := by
      have hnum : (1:ℝ) - c = ω * lam := by simp [hc]
      rw [hnum]
      gcongr
    have h3 : t * ((1 - c)/c) ≤ t * ((ω * lam) / (1 - ω * κ)) :=
      mul_le_mul_of_nonneg_left h2 ht0.le
    calc 1 - c ^ t ≤ t * Real.log (1/c) := hkey
      _ ≤ t * ((1 - c)/c) := h1
      _ ≤ t * ((ω * lam) / (1 - ω * κ)) := h3
      _ = t * (ω * lam) / (1 - ω * κ) := by ring
  rw [landweberFilter_of_ne_zero (ne_of_gt hl0), abs_of_nonneg (by
    have : (0:ℝ) ≤ 1 - c ^ t := by linarith
    positivity)]
  rw [← ht]
  have hfinal : lam⁻¹ * (1 - c ^ t) ≤ lam⁻¹ * (t * (ω * lam) / (1 - ω * κ)) :=
    mul_le_mul_of_nonneg_left hchain (by positivity)
  refine hfinal.trans (le_of_eq ?_)
  rw [ht]
  field_simp

/-- The Landweber residual is `1 - λφ_α(λ) = (1 - ωλ)^(1/α)` for `λ ≠ 0`. -/
public theorem landweberFilter_residual_eq {ω lam : ℝ} {α : Set.Ioi (0 : ℝ)}
    (hlam : lam ≠ 0) :
    1 - lam * landweberFilter ω α lam = (1 - ω * lam) ^ ((1:ℝ) / (α : ℝ)) := by
  rw [landweberFilter_of_ne_zero hlam]
  field_simp
  ring

/-- The Landweber residual satisfies `|1 - λφ_α(λ)| ≤ 1` for `λ > 0` with `ωλ ≤ 1`. -/
public theorem landweberFilter_residual_abs_le_one {ω lam : ℝ} {α : Set.Ioi (0 : ℝ)}
    (hl0 : 0 < lam) (hωlam : ω * lam ≤ 1) (hω : 0 < ω) :
    |1 - lam * landweberFilter ω α lam| ≤ 1 := by
  have hα : (0 : ℝ) < (α : ℝ) := α.2
  rw [landweberFilter_residual_eq (ne_of_gt hl0)]
  have hbase : (0:ℝ) ≤ 1 - ω * lam := by linarith
  have hb1 : (1:ℝ) - ω * lam ≤ 1 := by nlinarith
  rw [abs_of_nonneg (Real.rpow_nonneg hbase _)]
  exact Real.rpow_le_one hbase hb1 (by positivity)

end AutoIp
