/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.NormedSpace -- shake: keep
import Cite.Attribute
public import Mathlib.Analysis.Normed.Operator.Basic

section _lem_neumann

attribute [cite] NormedRing.inverse_one_sub
attribute [cite] Units.oneSub
attribute [cite] hasSum_geom_series_inverse
attribute [cite] tsum_geometric_le_of_norm_lt_one

attribute [cite] ContinuousLinearMap.norm_id_le

end _lem_neumann

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E]

/- The bound `‖(Id - T)⁻¹‖ ≤ 1 / (1 - ‖T‖)`, with `‖Id‖ ≤ 1` supplying what the cited bound
leaves as `‖1‖ - 1`. -/
example (T : E →L[𝕜] E) (hT : ‖T‖ < 1) :
    ‖Ring.inverse (1 - T)‖ ≤ (1 - ‖T‖)⁻¹ := by
  rw [← geom_series_eq_inverse T hT]
  have h1 : ‖(1 : E →L[𝕜] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  linarith [tsum_geometric_le_of_norm_lt_one T hT]
