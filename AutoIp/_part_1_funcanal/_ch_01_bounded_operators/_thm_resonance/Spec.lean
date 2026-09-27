/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

section _thm_resonance

/-- Banach–Steinhaus, resonance form: let `X` be a Banach space, `Y` a normed space, and `T i`
a family in `L(X,Y)` with `sup_i ‖T i‖ = ∞`. Then there is `x ∈ X` with `sup_i ‖T i x‖ = ∞`. Each
supremum being infinite is written as every real `C` being exceeded by some term. -/
public theorem banach_steinhaus_exists_unbounded {𝕜 : Type*} [RCLike 𝕜] {ι : Type*}
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {T : ι → E →L[𝕜] F} (h : ∀ C : ℝ, ∃ i, C < ‖T i‖) :
    ∃ x : E, ∀ C : ℝ, ∃ i, C < ‖T i x‖ := by
  by_contra! h_bound
  rcases banach_steinhaus h_bound with ⟨C', hC'⟩
  rcases h C' with ⟨i, hi⟩
  grind

end _thm_resonance
