/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_17_landweber._def_landweber.Spec
import all AutoIp._part_2_reg._ch_17_landweber._def_landweber.Spec
public import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The iteration starts at zero. -/
public theorem landweber_zero (K : E →L[𝕜] F) (ω : ℝ) (y : F) : landweber K ω y 0 = 0 := by
  unfold landweber
  rfl

/-- The Landweber step `x_{m+1} = x_m + ω K* (y - K x_m)`. -/
public theorem landweber_succ (K : E →L[𝕜] F) (ω : ℝ) (y : F) (m : ℕ) :
    landweber K ω y (m + 1) = landweber K ω y m +
      (ω : 𝕜) • K.adjoint (y - K (landweber K ω y m)) := by
  conv_lhs => unfold landweber

end AutoIp
