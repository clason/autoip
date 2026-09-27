/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# StepSize

Elementary bounds on the Landweber step size.
-/

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- For `0 < ω` with `ω ‖K‖² ≤ 1`, `‖r - ω K K* r‖² ≤ ‖r‖² - ω ‖K* r‖²`. -/
public theorem sq_norm_sub_smul_apply_adjoint_le (K : E →L[𝕜] F) {ω : ℝ} (hω0 : 0 < ω)
    (hωK : ω * ‖K‖ ^ 2 ≤ 1) (r : F) :
    ‖r - (ω : 𝕜) • K (K.adjoint r)‖ ^ 2 ≤ ‖r‖ ^ 2 - ω * ‖K.adjoint r‖ ^ 2 := by
  have hre : RCLike.re
      (inner 𝕜 r ((RCLike.ofReal ω : 𝕜) • K (ContinuousLinearMap.adjoint K r))) =
      ω * ‖ContinuousLinearMap.adjoint K r‖ ^ 2 := by
    rw [inner_smul_right, RCLike.re_ofReal_mul, ← ContinuousLinearMap.adjoint_inner_left,
      inner_self_eq_norm_sq]
  have hop : ‖K (ContinuousLinearMap.adjoint K r)‖ ^ 2 ≤
      ‖K‖ ^ 2 * ‖ContinuousLinearMap.adjoint K r‖ ^ 2 := by
    have h := K.le_opNorm (ContinuousLinearMap.adjoint K r)
    nlinarith [norm_nonneg (K (ContinuousLinearMap.adjoint K r)), norm_nonneg K,
      norm_nonneg (ContinuousLinearMap.adjoint K r)]
  have hnorm : ‖(RCLike.ofReal ω : 𝕜) • K (ContinuousLinearMap.adjoint K r)‖ ^ 2 =
      ω ^ 2 * ‖K (ContinuousLinearMap.adjoint K r)‖ ^ 2 := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos hω0, mul_pow]
  rw [norm_sub_sq (𝕜 := 𝕜), hre, hnorm]
  nlinarith [mul_nonneg hω0.le (sq_nonneg ‖ContinuousLinearMap.adjoint K r‖),
    mul_le_mul_of_nonneg_left hop (sq_nonneg ω)]

end AutoIp
