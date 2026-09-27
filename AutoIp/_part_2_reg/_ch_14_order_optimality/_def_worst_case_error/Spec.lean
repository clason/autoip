/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_13_regularization._def_parameter_choice

section _def_worst_case_error

namespace AutoIp

open scoped ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The worst-case error `E(y, δ) := sup_{y^δ ∈ B_δ(y)} ‖R_{α(δ, y^δ)} y^δ - T† y‖` for
`y ∈ Dom(T†)` and `δ > 0`. Its value lies in `[0, ∞]`. The family `R` is any family of maps
`Y → X`. -/
@[expose]
public noncomputable def worstCaseError [CompleteSpace E] (T : E →L[𝕜] F)
    (R : Set.Ioi (0 : ℝ) → F → E) (a : ParameterChoice F)
    (y : F) (hy : y ∈ mpDomain T) (δ : ℝ) (hδ : 0 < δ) : ℝ≥0∞ :=
  ⨆ z ∈ Metric.closedBall y δ,
    ‖R (a.param ⟨δ, hδ⟩ z) z - moorePenrose T ⟨y, hy⟩‖ₑ

/-- The modulus of conditional continuity `ε(M, δ) := sup {‖x‖ : x ∈ M, ‖T x‖ ≤ δ}` for
`M ⊆ X` and `δ > 0`. Its value lies in `[0, ∞]`, and the supremum of the empty set is `0`.
The positivity of `δ` is an argument the body does not read. -/
@[expose]
public noncomputable def modulusOfContinuity (T : E →L[𝕜] F) (M : Set E) (δ : ℝ)
    -- The condition is an argument because the object is defined only under it, though the
    -- formula does not read it.
    (_hδ : 0 < δ) : ℝ≥0∞ :=
  ⨆ x ∈ {x ∈ M | ‖T x‖ ≤ δ}, ‖x‖ₑ

end AutoIp

end _def_worst_case_error
