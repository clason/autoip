/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.RCLike.Lemmas

section _thm_riesz_ball

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Riesz: for a normed space `X` over `𝕂 ∈ {ℝ, ℂ}`, the closed unit ball of `X` is compact if and
only if `dim X < ∞`. -/
public theorem isCompact_unitClosedBall_iff_finiteDimensional :
    IsCompact (Metric.closedBall (0 : E) 1) ↔ FiniteDimensional 𝕜 E := by
  constructor
  · intro h
    exact FiniteDimensional.of_isCompact_closedBall 𝕜 one_pos h
  · intro _
    have : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
    exact ProperSpace.isCompact_closedBall 0 1

end _thm_riesz_ball
