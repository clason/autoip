/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_06_compact_operators._lem_compact_seq.Spec
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.RCLike.Basic

open scoped Topology
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- An operator into a Banach space is compact if the image of the closed unit ball is
totally bounded. -/
public
theorem isCompactOperator_of_totallyBounded_image_closedBall [CompleteSpace F] {T : E →L[𝕜] F}
    (h : TotallyBounded ((T : E →ₗ[𝕜] F) '' Metric.closedBall (0 : E) 1)) :
    IsCompactOperator T :=
  (isCompactOperator_iff_isCompact_closure_image_closedBall (T : E →ₗ[𝕜] F) one_pos).mpr
    (TotallyBounded.isCompact_of_isClosed h.closure isClosed_closure)
