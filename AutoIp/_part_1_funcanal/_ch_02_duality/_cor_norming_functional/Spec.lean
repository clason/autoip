/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Analysis.Normed.Module.HahnBanach
import Cite.Attribute

section _cor_norming_functional

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Norming functionals, the consequence `‖x‖ = sup_{‖f‖ ≤ 1} |⟨x, f⟩|`, the supremum being over
the closed unit ball of `X'`. -/
public theorem sSup_unitClosedBall_dual_eq_norm (x : E) :
    sSup ((fun f : StrongDual 𝕜 E => ‖f x‖) '' Metric.closedBall 0 1) = ‖x‖ := by
  have hiso : ‖NormedSpace.inclusionInDoubleDual 𝕜 E x‖ = ‖x‖ :=
    (NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map x
  rw [← hiso]
  exact ContinuousLinearMap.sSup_unitClosedBall_eq_norm
    (NormedSpace.inclusionInDoubleDual 𝕜 E x)


attribute [cite] SeparatingDual.eq_iff_forall_dual_eq
attribute [cite] exists_dual_vector
attribute [cite] exists_dual_vector''

end _cor_norming_functional

-- `X'` separates the points of `X`: the cited criterion holds for every normed space over `ℝ`
-- or `ℂ`, since Hahn–Banach supplies the separating functionals it presupposes.
example {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {x y : E} :
    x = y ↔ ∀ f : StrongDual 𝕜 E, f x = f y :=
  SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)
