/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_filter
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

section _def_qualification

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The regularizing filter `{φ_α}` satisfies condition (F) with constant `C`: `C > 0` and
`sup_{λ ∈ (0,κ]} |φ_α(λ)| ≤ C α⁻¹` for all `α > 0`. -/
public structure HasFilterBound (K : E →L[𝕜] F) (φ : Set.Ioi (0 : ℝ) → ℝ → ℝ)
    (C : ℝ) : Prop where
  /-- `{φ_α}` is a regularizing filter, with some constant `C_φ`. -/
  isRegularizingFilter : ∃ Cφ, IsRegularizingFilter K φ Cφ
  /-- `C > 0`. -/
  const_pos : 0 < C
  /-- `sup_{λ ∈ (0,κ]} |φ_α(λ)| ≤ C α⁻¹` for all `α > 0`. -/
  iSup_le : ∀ α : Set.Ioi (0 : ℝ),
    (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |φ α lam|) ≤ C * (α : ℝ)⁻¹

/-- The regularizing filter `{φ_α}` satisfies condition (Q_ν) with constant `C`: `C > 0` and
`ω_ν(α) ≤ C α^{ν/2}` for all `α ∈ (0, κ]`, where
`ω_ν(α) = sup_{λ ∈ (0,κ]} λ^{ν/2} |1 − λ φ_α(λ)|`. -/
public structure HasResidualBound (K : E →L[𝕜] F) (φ : Set.Ioi (0 : ℝ) → ℝ → ℝ)
    (ν C : ℝ) : Prop where
  /-- `{φ_α}` is a regularizing filter, with some constant `C_φ`. -/
  isRegularizingFilter : ∃ Cφ, IsRegularizingFilter K φ Cφ
  /-- `C > 0`. -/
  const_pos : 0 < C
  /-- `ω_ν(α) ≤ C α^{ν/2}` for all `α ∈ (0, κ]`. -/
  omega_le : ∀ α : Set.Ioi (0 : ℝ), (α : ℝ) ≤ ‖K‖ ^ 2 →
    (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), lam ^ (ν / 2) * |1 - lam * φ α lam|) ≤
      C * (α : ℝ) ^ (ν / 2)

/-- The qualification `ν₀ := sup {ν > 0 : (Q_ν) holds}`, taken in `[0, ∞]`. Where (Q_ν)
holds for no `ν > 0` the supremum of the empty set is `0`, outside the prose's `(0, ∞]`. -/
public noncomputable def qualification (K : E →L[𝕜] F) (φ : Set.Ioi (0 : ℝ) → ℝ → ℝ) : ℝ≥0∞ :=
  ⨆ ν ∈ {ν : ℝ | 0 < ν ∧ ∃ C, HasResidualBound K φ ν C}, ENNReal.ofReal ν

end AutoIp

end _def_qualification
