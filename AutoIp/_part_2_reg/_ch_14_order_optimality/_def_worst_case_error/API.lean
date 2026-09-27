/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_14_order_optimality._def_worst_case_error.Spec

namespace AutoIp

open scoped ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- `E(y, δ) = E(y', δ)` for `y = y'`, whatever the proofs of `y, y' ∈ Dom(T†)`. -/
public theorem worstCaseError_congr (T : E →L[𝕜] F) (R : Set.Ioi (0 : ℝ) → F → E)
    (a : ParameterChoice F) {y y' : F} (h : y = y') (hy : y ∈ mpDomain T)
    (hy' : y' ∈ mpDomain T) (δ : ℝ) (hδ : 0 < δ) :
    worstCaseError T R a y hy δ hδ = worstCaseError T R a y' hy' δ hδ := by
  subst h
  rfl

/-- `‖R_{α(δ,y^δ)} y^δ - T† y‖ ≤ E(y, δ)` for every `y^δ ∈ B_δ(y)`. -/
public theorem le_worstCaseError (T : E →L[𝕜] F) (R : Set.Ioi (0 : ℝ) → F → E)
    (a : ParameterChoice F) (y : F) (hy : y ∈ mpDomain T) {δ : ℝ} (hδ : 0 < δ) {z : F}
    (hz : z ∈ Metric.closedBall y δ) :
    ‖R (a.param ⟨δ, hδ⟩ z) z - moorePenrose T ⟨y, hy⟩‖ₑ
      ≤ worstCaseError T R a y hy δ hδ :=
  le_iSup₂ (f := fun z (_ : z ∈ Metric.closedBall y δ) =>
    ‖R (a.param ⟨δ, hδ⟩ z) z - moorePenrose T ⟨y, hy⟩‖ₑ) z hz

/-- `E(y, δ) ≤ C` if and only if `‖R_{α(δ,y^δ)} y^δ - T† y‖ ≤ C` for every
`y^δ ∈ B_δ(y)`. -/
public theorem worstCaseError_le_iff (T : E →L[𝕜] F) (R : Set.Ioi (0 : ℝ) → F → E)
    (a : ParameterChoice F) (y : F) (hy : y ∈ mpDomain T) (δ : ℝ) (hδ : 0 < δ) (C : ℝ≥0∞) :
    worstCaseError T R a y hy δ hδ ≤ C ↔ ∀ z ∈ Metric.closedBall y δ,
      ‖R (a.param ⟨δ, hδ⟩ z) z - moorePenrose T ⟨y, hy⟩‖ₑ ≤ C :=
  iSup₂_le_iff

end AutoIp
