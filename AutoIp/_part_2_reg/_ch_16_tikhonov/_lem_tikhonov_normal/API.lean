/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_16_tikhonov._lem_tikhonov_normal.Spec
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_basic
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_hom

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- The bound `‖R_α y‖ ≤ ‖y‖ / (2√α)` for Tikhonov regularization. -/
public theorem norm_spectralReg_tikhonov_le (hs : IsSingularSystem K σ v u) {α : Set.Ioi (0 : ℝ)}
    (w : F) :
    ‖spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) α w‖
      ≤ ‖w‖ / (2 * Real.sqrt (α : ℝ)) := by
  have hα : (0 : ℝ) < (α : ℝ) := α.2
  have hsq0 : 0 < Real.sqrt (α : ℝ) := Real.sqrt_pos.mpr α.2
  have hsqsq : Real.sqrt (α : ℝ) * Real.sqrt (α : ℝ) = (α : ℝ) := Real.mul_self_sqrt α.2.le
  have hnorm : (ContinuousLinearMap.adjoint K ∘L K +
        (RCLike.ofReal (α : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E)
      (spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) α w)
      = ContinuousLinearMap.adjoint K w :=
    (tikhonov_iff_normal hs w _).mp rfl
  set x := spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) α w with hxdef
  have hik : (inner 𝕜 x ((ContinuousLinearMap.adjoint K ∘L K +
        (RCLike.ofReal (α : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E) x) : 𝕜)
      = (RCLike.ofReal (‖K x‖ ^ 2 + (α : ℝ) * ‖x‖ ^ 2) : 𝕜) := by
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      smul_apply, ContinuousLinearMap.id_apply, inner_add_right,
      inner_smul_right, ContinuousLinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K, RCLike.ofReal_add, RCLike.ofReal_mul, RCLike.ofReal_pow]
  have h2 : ‖K x‖ ^ 2 + (α : ℝ) * ‖x‖ ^ 2 ≤ ‖K x‖ * ‖w‖ := by
    have h3 : RCLike.re (inner 𝕜 x ((ContinuousLinearMap.adjoint K ∘L K +
        (RCLike.ofReal (α : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E) x) : 𝕜)
        = RCLike.re (inner 𝕜 (K x) w : 𝕜) := by
      rw [hnorm, ContinuousLinearMap.adjoint_inner_right]
    rw [hik, RCLike.ofReal_re] at h3
    rw [h3]
    exact re_inner_le_norm (𝕜 := 𝕜) _ _
  rw [le_div_iff₀ (by positivity)]
  rcases eq_or_lt_of_le (norm_nonneg (K x)) with ha | ha
  · have hx2 : ‖x‖ ^ 2 ≤ 0 := by nlinarith [norm_nonneg w]
    have hb : ‖x‖ = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm hx2 (sq_nonneg _))
    rw [hb]
    simp
  · nlinarith [sq_nonneg (‖K x‖ - Real.sqrt (α : ℝ) * ‖x‖), norm_nonneg x, hsqsq]

/-- The bound `‖R_α‖ ≤ 1 / (2√α)` for Tikhonov regularization. -/
public theorem opNorm_spectralReg_tikhonov_le (hs : IsSingularSystem K σ v u)
    {α : Set.Ioi (0 : ℝ)} :
    ‖spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) α‖
      ≤ 1 / (2 * Real.sqrt (α : ℝ)) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [show 1 / (2 * Real.sqrt (α : ℝ)) * ‖w‖ = ‖w‖ / (2 * Real.sqrt (α : ℝ)) by ring]
  exact norm_spectralReg_tikhonov_le hs w

end AutoIp
