/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_19_general_source_conditions._def_index_function.Spec
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Ring.Basic

namespace AutoIp

/-- An index function is strictly positive on `(0, κ]`. -/
public theorem IsIndexFunction.pos {κ : ℝ} {φ : ℝ → ℝ} (hφ : IsIndexFunction κ φ) {t : ℝ}
    (ht : t ∈ Set.Ioc (0 : ℝ) κ) : 0 < φ t := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) κ := ⟨le_rfl, ht.1.le.trans ht.2⟩
  have h := hφ.strictMonoOn h0 ⟨ht.1.le, ht.2⟩ ht.1
  rwa [hφ.map_zero] at h

/-- An index function is at most `φ(κ)` on `[0, κ]`. -/
public theorem IsIndexFunction.le_right {κ : ℝ} {φ : ℝ → ℝ} (hφ : IsIndexFunction κ φ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) κ) : φ t ≤ φ κ :=
  hφ.strictMonoOn.monotoneOn ht ⟨ht.1.trans ht.2, le_rfl⟩ ht.2

/-- An index function is bounded on `[0, κ]`. -/
public theorem IsIndexFunction.exists_bound {κ : ℝ} {φ : ℝ → ℝ} (hφ : IsIndexFunction κ φ) :
    ∃ C, ∀ t ∈ Set.Icc (0 : ℝ) κ, |φ t| ≤ C := by
  simpa only [Real.norm_eq_abs] using
    isCompact_Icc.exists_bound_of_continuousOn hφ.continuousOn

end AutoIp
