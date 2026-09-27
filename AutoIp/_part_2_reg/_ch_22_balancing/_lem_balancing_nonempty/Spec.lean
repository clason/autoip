/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_22_balancing._def_balancing
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

section _lem_balancing_nonempty

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The rule is well defined: `i₊` exists, lies in the set that defines it, and satisfies
`i₊ ≤ N`.

That the set contains `i = N` is not stated on its own. The hypotheses `0 ≤ C_R` and `0 ≤ δ`
are the chapter's standing assumptions; the grid need not be geometric. -/
public theorem balancingIndex_spec (R : Set.Ioi (0 : ℝ) → F →L[𝕜] E) {CR δ : ℝ} (hCR : 0 ≤ CR)
    (hδ : 0 ≤ δ) (N : ℕ) {grid : ℕ → Set.Ioi (0 : ℝ)} (z : F) :
    balancingIndex R CR δ (mul_nonneg hCR hδ) N grid z ≤ N ∧
      ∀ j, balancingIndex R CR δ (mul_nonneg hCR hδ) N grid z ≤ j → j ≤ N →
        ‖R (grid (balancingIndex R CR δ (mul_nonneg hCR hδ) N grid z)) z - R (grid j) z‖ ≤
          4 * (CR * δ * (grid j : ℝ) ^ (-(1 : ℝ) / 2)) := by
  rw [balancingIndex_def]
  have hmem : N ∈ {i : ℕ | i ≤ N ∧ ∀ j, i ≤ j → j ≤ N →
      ‖R (grid i) z - R (grid j) z‖ ≤ 4 * (CR * δ * (grid j : ℝ) ^ (-(1 : ℝ) / 2))} := by
    refine ⟨le_rfl, fun j hj hjN => ?_⟩
    have hjeq : j = N := le_antisymm hjN hj
    rw [hjeq]
    have h0 : (0 : ℝ) ≤ CR * δ * (grid N : ℝ) ^ (-(1 : ℝ) / 2) :=
      mul_nonneg (mul_nonneg hCR hδ) (Real.rpow_nonneg (grid N).2.le _)
    simp only [sub_self, norm_zero]
    linarith
  exact Nat.sInf_mem ⟨N, hmem⟩

end AutoIp

end _lem_balancing_nonempty
