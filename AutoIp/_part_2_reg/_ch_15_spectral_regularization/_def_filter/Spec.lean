/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Operator.Basic

section _def_filter

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable {K : E →L[𝕜] F}

/-- `{φ_α}_{α>0}` is a regularizing filter with constant `C_φ`, where `κ = ‖K‖²`. Each
`φ_α` is a function on `ℝ` of which only the values on `[0, κ]` are constrained, and
piecewise continuity is not required. -/
public structure IsRegularizingFilter (K : E →L[𝕜] F) (φ : Set.Ioi (0 : ℝ) → ℝ → ℝ)
    (C : ℝ) : Prop where
  /-- `C_φ > 0`. -/
  const_pos : 0 < C
  /-- Each `φ_α` is bounded on `[0, κ]`. -/
  bddOn : ∀ α, ∃ B : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |φ α t| ≤ B
  /-- (i) `φ_α(λ) → λ⁻¹` as `α → 0`, for every `λ ∈ (0, κ]`. -/
  tendsto_inv : ∀ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
    Tendsto (fun α => φ α lam) atBot (𝓝 lam⁻¹)
  /-- (ii) `λ |φ_α(λ)| ≤ C_φ` for all `λ ∈ (0, κ]` and all `α > 0`. -/
  mul_abs_le : ∀ α, ∀ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), lam * |φ α lam| ≤ C

end AutoIp

end _def_filter
