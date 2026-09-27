/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Operator.Basic

section _def_perturbed_problem

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Perturbed problem: `(K_h, y^δ)` is `(h,δ)`-admissible data for `(K, y)` if `‖K - K_h‖ ≤ h`
and `‖y - y^δ‖ ≤ δ`. -/
public structure IsAdmissibleData (K Kh : E →L[𝕜] F) (y z : F) (h δ : ℝ) : Prop where
  /-- `‖K - K_h‖ ≤ h`. -/
  opNorm_sub_le : ‖K - Kh‖ ≤ h
  /-- `‖y - y^δ‖ ≤ δ`. -/
  norm_sub_le : ‖y - z‖ ≤ δ

end AutoIp

end _def_perturbed_problem
