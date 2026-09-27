/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_12_picard._def_source_set
public import AutoIp._part_2_reg._ch_14_order_optimality._def_worst_case_error
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_abs_norm
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._thm_interpolation

section _thm_modulus_source_upper

namespace AutoIp

open Filter Topology
open scoped ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- For `ν, ρ > 0`, `ε(X_{ν,ρ}, δ) ≤ δ^{ν/(ν+1)} ρ^{1/(ν+1)}` for all `δ > 0`. The source
set `X_{ν,ρ}` is formed from a singular system of `K`, and `K` is not assumed
compact. -/
public theorem modulusOfContinuity_sourceSet_le (hs : IsSingularSystem K σ v u) {ν ρ δ : ℝ}
    (hν : 0 < ν) (hρ : 0 < ρ) (hδ : 0 < δ) :
    modulusOfContinuity K (sourceSet hs ν hν ρ hρ) δ hδ ≤
      ENNReal.ofReal (δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1))) := by
  have hν1 : (0 : ℝ) < ν + 1 := by linarith
  have he1 : (0 : ℝ) ≤ ν / (ν + 1) := (div_pos hν hν1).le
  have he2 : (0 : ℝ) ≤ 1 / (ν + 1) := (div_pos one_pos hν1).le
  rw [modulusOfContinuity]
  refine iSup₂_le ?_
  rintro x ⟨hxM, hxδ⟩
  rw [← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mem_sourceSet_iff] at hxM
  obtain ⟨w, hw, rfl⟩ := hxM
  have hexp : 1 - ν / (ν + 1) = 1 / (ν + 1) := by field_simp; ring
  have hinterp := hs.norm_absRpow_le_rpow_mul_rpow hν.le (by linarith : ν < ν + 1) w
  rw [hexp] at hinterp
  have hν1' : (0 : ℝ) ≤ ν + 1 := hν1.le
  have hcomp : hs.absRpow (ν + 1) hν1' w
      = hs.absRpow 1 zero_le_one (hs.absRpow ν hν.le w) := by
    rw [hs.absRpow_congr (show ν + 1 = 1 + ν by ring) hν1' (by linarith),
      hs.absRpow_add one_pos hν, ContinuousLinearMap.comp_apply]
  have hnorm : ‖hs.absRpow (ν + 1) hν1' w‖ ≤ δ := by
    rw [hcomp, hs.norm_absRpow_one_apply_eq_norm_map]
    exact hxδ
  refine le_trans hinterp (mul_le_mul ?_ ?_ (Real.rpow_nonneg (norm_nonneg _) _)
    (Real.rpow_nonneg hδ.le _))
  · exact Real.rpow_le_rpow (norm_nonneg _) hnorm he1
  · exact Real.rpow_le_rpow (norm_nonneg _) hw he2

end AutoIp

end _thm_modulus_source_upper
