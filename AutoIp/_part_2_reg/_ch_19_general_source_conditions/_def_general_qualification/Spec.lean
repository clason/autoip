/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_filter
public import AutoIp._part_2_reg._ch_19_general_source_conditions._def_index_function

section _def_general_qualification

namespace AutoIp

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The regularizing filter `{φ_α}` has qualification `ψ` with constant `C`, written (Q_ψ):
`ω_ψ(α) := sup_{λ ∈ (0,κ]} ψ(λ) |r_α(λ)| ≤ C ψ(α)` for all `α ∈ (0, κ]`, where
`r_α(λ) := 1 - λ φ_α(λ)`, `ψ` is an index function and `κ = ‖K‖²`.

It also asks `C ≥ 0`, which the blueprint does not state. -/
public structure HasQualification (K : E →L[𝕜] F) (flt : Set.Ioi (0 : ℝ) → ℝ → ℝ)
    (ψ : ℝ → ℝ) (C : ℝ) : Prop where
  /-- `{φ_α}` is a regularizing filter, for some constant `C_φ`. -/
  isRegularizingFilter : ∃ Cflt, IsRegularizingFilter K flt Cflt
  /-- `ψ` is an index function on `[0, κ]`. -/
  isIndexFunction : IsIndexFunction (‖K‖ ^ 2) ψ
  /-- `C ≥ 0`, a condition the blueprint does not state. -/
  const_nonneg : 0 ≤ C
  /-- `ω_ψ(α) ≤ C ψ(α)` for all `α ∈ (0, κ]`. -/
  omega_le : ∀ α : Set.Ioi (0 : ℝ), (α : ℝ) ≤ ‖K‖ ^ 2 →
    (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), ψ lam * |1 - lam * flt α lam|) ≤ C * ψ (α : ℝ)

end AutoIp

end _def_general_qualification
