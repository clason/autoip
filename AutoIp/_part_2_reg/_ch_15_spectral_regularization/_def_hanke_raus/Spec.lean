/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg

section _def_hanke_raus

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Hanke–Raus rule: `α ∈ argmin_{α ∈ (0,κ]} Ψ(α)` for the datum `y^δ`, where
`Ψ(α) = α^{-1/2} ‖K x^δ_α − y^δ‖` and `x^δ_α = R_α y^δ` with `R_α` the spectral regularization of
`{φ_α}`. The family need not be a regularizing filter; the boundedness of each `φ_α` at the `σₙ²` is
there because the spectral regularization needs it as an argument. -/
public
structure IsHankeRausChoiceOnSpectrum (hs : IsSingularSystem K σ v u) (φ : Set.Ioi (0 : ℝ) → ℝ → ℝ)
    (hφ : ∀ α : Set.Ioi (0 : ℝ), ∃ C, ∀ i, |φ α (σ i ^ 2)| ≤ C) (z : F)
    (α : Set.Ioi (0 : ℝ)) : Prop where
  /-- `α ≤ κ`, so that `α ∈ (0, κ]`. -/
  le_normSq : (α : ℝ) ≤ ‖K‖ ^ 2
  /-- `Ψ(α) ≤ Ψ(β)` for all `β ∈ (0, κ]`. -/
  minimal : ∀ β : Set.Ioi (0 : ℝ), (β : ℝ) ≤ ‖K‖ ^ 2 →
    (α : ℝ) ^ (-(1 : ℝ) / 2) * ‖K (spectralReg hs φ hφ α z) - z‖ ≤
      (β : ℝ) ^ (-(1 : ℝ) / 2) * ‖K (spectralReg hs φ hφ β z) - z‖

end AutoIp

end _def_hanke_raus
