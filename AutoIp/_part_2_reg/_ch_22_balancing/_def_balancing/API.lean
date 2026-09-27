/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_22_balancing._def_balancing.Spec
import all AutoIp._part_2_reg._ch_22_balancing._def_balancing.Spec
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace AutoIp

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The balancing index is the infimum of the admissible indices in `{0,…,N}`. -/
public theorem balancingIndex_def (R : Set.Ioi (0 : ℝ) → F →L[𝕜] E) (CR δ : ℝ)
    (h : 0 ≤ CR * δ) (N : ℕ) (grid : ℕ → Set.Ioi (0 : ℝ)) (z : F) :
    balancingIndex R CR δ h N grid z
      = sInf {i : ℕ | i ≤ N ∧ ∀ j, i ≤ j → j ≤ N →
          ‖R (grid i) z - R (grid j) z‖ ≤ 4 * (CR * δ * (grid j : ℝ) ^ (-(1 : ℝ) / 2))} := by
  unfold balancingIndex
  rfl

/-- The balancing index is at most every admissible index `i ≤ N`. -/
public theorem balancingIndex_le (R : Set.Ioi (0 : ℝ) → F →L[𝕜] E) {CR δ : ℝ}
    {h : 0 ≤ CR * δ} {N : ℕ} {grid : ℕ → Set.Ioi (0 : ℝ)} {z : F} {i : ℕ} (hi : i ≤ N)
    (hj : ∀ j, i ≤ j → j ≤ N →
      ‖R (grid i) z - R (grid j) z‖ ≤ 4 * (CR * δ * (grid j : ℝ) ^ (-(1 : ℝ) / 2))) :
    balancingIndex R CR δ h N grid z ≤ i := by
  rw [balancingIndex_def]
  exact Nat.sInf_le ⟨hi, hj⟩

/-- Below the balancing index, the balancing condition fails against some later index `j ≤ N`. -/
public theorem exists_gt_of_lt_balancingIndex (R : Set.Ioi (0 : ℝ) → F →L[𝕜] E) {CR δ : ℝ}
    {h : 0 ≤ CR * δ} {N : ℕ}
    {grid : ℕ → Set.Ioi (0 : ℝ)} {z : F} {m : ℕ} (hmN : m ≤ N)
    (hlt : m < balancingIndex R CR δ h N grid z) :
    ∃ j, m ≤ j ∧ j ≤ N ∧
      4 * (CR * δ * (grid j : ℝ) ^ (-(1 : ℝ) / 2)) < ‖R (grid m) z - R (grid j) z‖ := by
  by_contra hcon
  push Not at hcon
  exact absurd (balancingIndex_le R hmN fun j hj hjN => hcon j hj hjN) (by omega)

end AutoIp
