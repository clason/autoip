/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Data.EReal.Inv

section _def_lsq_minnorm

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- `x̂ ∈ X` is a least squares solution of `T x = y`: `‖T x̂ - y‖ ≤ ‖T z - y‖` for all
`z ∈ X`. -/
@[expose]
public def IsLeastSquares (T : E →L[𝕜] F) (y : F) (x : E) : Prop :=
  ∀ z : E, ‖T x - y‖ ≤ ‖T z - y‖

/-- `x̂ ∈ X` is a minimum norm solution of `T x = y`: a least squares solution with
`‖x̂‖ ≤ ‖z‖` for every least squares solution `z`. -/
public structure IsMinimumNorm (T : E →L[𝕜] F) (y : F) (x : E) : Prop where
  /-- `x̂` is a least squares solution of `T x = y`. -/
  isLeastSquares : IsLeastSquares T y x
  /-- `‖x̂‖ ≤ ‖z‖` for every least squares solution `z` of `T x = y`. -/
  norm_le : ∀ z : E, IsLeastSquares T y z → ‖x‖ ≤ ‖z‖

end AutoIp

end _def_lsq_minnorm
