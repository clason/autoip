/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Normed.Group.Basic

section _def_index_function

namespace AutoIp

open Filter Topology

/-- `φ` is an index function on `[0, κ]`: continuous and strictly increasing there, with
`φ(0) = 0`.

`φ` is a function on `ℝ` and only its values on `[0, κ]` are constrained; that they lie in
`[0, ∞)` follows and is stated separately. -/
public structure IsIndexFunction (κ : ℝ) (φ : ℝ → ℝ) : Prop where
  /-- `φ(0) = 0`. -/
  map_zero : φ 0 = 0
  /-- `φ` is continuous on `[0, κ]`. -/
  continuousOn : ContinuousOn φ (Set.Icc (0 : ℝ) κ)
  /-- `φ` is strictly increasing on `[0, κ]`. -/
  strictMonoOn : StrictMonoOn φ (Set.Icc (0 : ℝ) κ)

/-- An index function takes values in `[0, ∞)` on `[0, κ]`. -/
public theorem IsIndexFunction.nonneg {κ : ℝ} {φ : ℝ → ℝ} (hφ : IsIndexFunction κ φ) :
    ∀ t ∈ Set.Icc (0 : ℝ) κ, 0 ≤ φ t := by
  intro t ht
  rcases ht.1.eq_or_lt with h | h
  · simp [← h, hφ.map_zero]
  · have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) κ := ⟨le_rfl, ht.1.trans ht.2⟩
    have hlt := hφ.strictMonoOn h0 ht h
    rw [hφ.map_zero] at hlt
    exact hlt.le

end AutoIp

end _def_index_function
