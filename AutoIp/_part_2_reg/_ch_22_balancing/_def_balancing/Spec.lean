/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

section _def_balancing

namespace AutoIp

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The balancing index `i₊ = min {i ∈ {0,…,N} : ‖xᵢ - xⱼ‖ ≤ 4Δⱼ for all j ≥ i}`, where
`xᵢ = R_{αᵢ} y^δ` and `Δⱼ = C_R δ αⱼ^(-1/2)`.

The hypothesis `0 ≤ C_R δ` is not used by the definition; it is there so that the index is
formed only where the set is nonempty. `R_α` and `C_R` are arguments, and the grid need not be
geometric here. -/
public noncomputable def balancingIndex (R : Set.Ioi (0 : ℝ) → F →L[𝕜] E) (CR δ : ℝ)
    -- The condition is an argument because the index is defined only under it, though the
    -- formula does not read it.
    (_h : 0 ≤ CR * δ) (N : ℕ) (grid : ℕ → Set.Ioi (0 : ℝ)) (z : F) : ℕ :=
  sInf {i : ℕ | i ≤ N ∧ ∀ j, i ≤ j → j ≤ N →
    ‖R (grid i) z - R (grid j) z‖ ≤ 4 * (CR * δ * (grid j : ℝ) ^ (-(1 : ℝ) / 2))}

/-- The balancing principle on a geometric grid `α₀ > ⋯ > α_N > 0` with ratio `q`
selects the parameter `α = α_{i₊}`. -/
public
structure IsBalancingChoiceOnGeometricGrid (R : Set.Ioi (0 : ℝ) → F →L[𝕜] E) (CR δ : ℝ)
    (h : 0 ≤ CR * δ) (N : ℕ) (grid : ℕ → Set.Ioi (0 : ℝ)) (q : ℝ) (z : F)
    (α : Set.Ioi (0 : ℝ)) : Prop where
  /-- The ratio satisfies `q > 1`. -/
  one_lt_ratio : 1 < q
  /-- `α_{i-1} = q αᵢ` for `i = 1, …, N`. -/
  grid_geometric : ∀ i, i + 1 ≤ N → (grid i : ℝ) = q * (grid (i + 1) : ℝ)
  /-- The selected parameter is `α_{i₊}`. -/
  eq_grid : α = grid (balancingIndex R CR δ h N grid z)

end AutoIp

end _def_balancing
