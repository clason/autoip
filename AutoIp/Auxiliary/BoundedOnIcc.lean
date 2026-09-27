/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# BoundedOnIcc

A continuous function is bounded on a compact interval.
-/

namespace AutoIp

/-- A continuous function is bounded on `[0, b]`. -/
public theorem exists_bound_on_Icc_of_continuous (b : ℝ) {φ : ℝ → ℝ} (h : Continuous φ) :
    ∃ C, ∀ t ∈ Set.Icc (0 : ℝ) b, |φ t| ≤ C := by
  simpa only [Real.norm_eq_abs] using
    isCompact_Icc.exists_bound_of_continuousOn h.continuousOn

end AutoIp
