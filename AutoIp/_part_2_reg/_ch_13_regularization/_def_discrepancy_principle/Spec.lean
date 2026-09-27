/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_13_regularization._def_parameter_choice

section _def_discrepancy_principle

namespace AutoIp

open Filter Topology
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The rule `α` satisfies the Morozov discrepancy principle with tolerance `τ` for the family
`{R_α}`. -/
public structure IsDiscrepancyPrinciple (T : E →L[𝕜] F) (R : Set.Ioi (0 : ℝ) → F →L[𝕜] E) (τ : ℝ)
    (a : ParameterChoice F) : Prop where
  /-- `τ > 1`. -/
  one_lt_tau : 1 < τ
  /-- For all `δ > 0` and all `y^δ ∈ Y` with `‖y^δ‖ > τδ`,
  `‖T R_{α(δ,y^δ)} y^δ − y^δ‖ ≤ τδ < ‖T R_α y^δ − y^δ‖` for all `α > α(δ, y^δ)`. -/
  residual : ∀ (δ : ℝ) (hδ : 0 < δ), ∀ z : F, τ * δ < ‖z‖ →
    ‖T (R (a.param ⟨δ, hδ⟩ z) z) - z‖ ≤ τ * δ ∧
      ∀ α : Set.Ioi (0 : ℝ), a ⟨δ, hδ⟩ z < (α : ℝ) → τ * δ < ‖T (R α z) - z‖

end AutoIp

end _def_discrepancy_principle
