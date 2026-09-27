/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_17_landweber._def_landweber
public import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F}

/-- The adjoint residual `r_m = K*(K x_m - y)` satisfies `r_{m+1} = (I - ωK*K) r_m`. -/
public theorem landweber_adjoint_residual_succ (K : E →L[𝕜] F) (ω : ℝ) (z : F) (m : ℕ) :
    K.adjoint (K (landweber K ω z (m + 1)) - z) =
      (ContinuousLinearMap.id 𝕜 E -
          (ω : 𝕜) • (K.adjoint ∘L K))
        (K.adjoint (K (landweber K ω z m) - z)) := by
  rw [landweber_succ]
  simp only [map_add, map_sub, map_smul, sub_apply,
    ContinuousLinearMap.id_apply, smul_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply]
  module

/-- `I - ωK*K` is injective for `0 < ω` and `ω‖K‖² < 1`. -/
public theorem injective_id_sub_smul_adjoint_comp_self (K : E →L[𝕜] F) {ω : ℝ}
    (hω : 0 < ω ∧ ω * ‖K‖ ^ 2 < 1) :
    Function.Injective (ContinuousLinearMap.id 𝕜 E -
      (ω : 𝕜) • (K.adjoint ∘L K)) := by
  obtain ⟨hω0, hprod⟩ := hω
  rw [injective_iff_map_eq_zero]
  intro x hx
  -- Pair the vanishing vector with `x`: the real part of the pairing is
  -- `‖x‖² - ω‖Kx‖²`, so the two are equal.
  have hval : (‖x‖ : ℝ) ^ 2 = ω * ‖K x‖ ^ 2 := by
    have h : (inner 𝕜 ((ContinuousLinearMap.id 𝕜 E -
        (RCLike.ofReal ω : 𝕜) • (ContinuousLinearMap.adjoint K ∘L K)) x) x : 𝕜) = 0 := by
      rw [hx, inner_zero_left]
    simp only [sub_apply, ContinuousLinearMap.id_apply, smul_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, inner_sub_left,
      inner_smul_left, RCLike.conj_ofReal,
      ContinuousLinearMap.adjoint_inner_left] at h
    have hre := congrArg RCLike.re h
    simp only [map_sub, map_zero, RCLike.re_ofReal_mul, inner_self_eq_norm_sq_to_K,
      sub_eq_zero, ← RCLike.ofReal_pow, RCLike.ofReal_re] at hre
    exact hre
  by_contra hne
  have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hne
  have hop : ‖K x‖ ^ 2 ≤ ‖K‖ ^ 2 * ‖x‖ ^ 2 := by
    have h := K.le_opNorm x
    nlinarith [norm_nonneg (K x), norm_nonneg K, hxpos.le]
  have hsq : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hop hω0.le,
    mul_lt_mul_of_pos_right hprod hsq]

end AutoIp
