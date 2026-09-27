/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Defs

section _def_landweber

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Landweber iteration for `y ∈ Y`: `x₀ = 0` and `xₘ = xₘ₋₁ + ω K* (y - K xₘ₋₁)` for
`m ∈ ℕ`.

The relaxation `ω` is an argument and is not constrained here. -/
public noncomputable def landweber (K : E →L[𝕜] F) (ω : ℝ) (y : F) : ℕ → E
  | 0 => 0
  | m + 1 => landweber K ω y m +
      (ω : 𝕜) • K.adjoint (y - K (landweber K ω y m))

end AutoIp

end _def_landweber
