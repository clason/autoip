/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

section _def_heuristic_rules

namespace AutoIp

open Filter Topology
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Heuristic rules, (i), the quasi-optimality rule: on a finite strictly decreasing grid
`{α_n}`, the index `n*` lies in `argmin_n ‖R_{α_{n+1}} y^δ − R_{α_n} y^δ‖`, and the rule
takes `α(y^δ) := α_{n*}`. The grid is `α_0, …, α_N` and the minimum runs over all `N`
consecutive pairs; the prose's range `1 ≤ n < N` is all consecutive pairs of a grid
`α_1, …, α_N`, so the Lean `N` is one less than the prose's. -/
public structure IsQuasiOptimalChoice (R : Set.Ioi (0 : ℝ) → F →L[𝕜] E) (N : ℕ)
    (α : Fin (N + 1) → Set.Ioi (0 : ℝ))
    (z : F) (n : Fin N) : Prop where
  /-- The grid `{α_n}` is strictly decreasing. -/
  grid_strictAnti : StrictAnti α
  /-- `n*` minimises `‖R_{α_{n+1}} y^δ − R_{α_n} y^δ‖` over all consecutive pairs of the
  grid. -/
  min_consecutive_diff : ∀ m : Fin N,
    ‖R (α n.succ) z - R (α n.castSucc) z‖ ≤ ‖R (α m.succ) z - R (α m.castSucc) z‖

/-- Heuristic rules, (ii), the Hanke–Raus rule:
`α(y^δ) ∈ argmin_{α>0} α^{-1/2} ‖T R_α y^δ − y^δ‖`. -/
public structure IsHankeRausChoice (T : E →L[𝕜] F) (R : Set.Ioi (0 : ℝ) → F →L[𝕜] E) (z : F)
    (α : Set.Ioi (0 : ℝ)) : Prop where
  /-- `α` minimises `α^{-1/2} ‖T R_α y^δ − y^δ‖` over `α > 0`. -/
  minimal : ∀ β : Set.Ioi (0 : ℝ),
    (α : ℝ) ^ (-(1 : ℝ) / 2) * ‖T (R α z) - z‖ ≤ (β : ℝ) ^ (-(1 : ℝ) / 2) * ‖T (R β z) - z‖

/-- Heuristic rules, (iii), the L-curve rule:
`α(y^δ) ∈ argmin_{α>0} ‖R_α y^δ‖ · ‖T R_α y^δ − y^δ‖`. -/
public structure IsLCurveChoice (T : E →L[𝕜] F) (R : Set.Ioi (0 : ℝ) → F →L[𝕜] E) (z : F)
    (α : Set.Ioi (0 : ℝ)) : Prop where
  /-- `α` minimises `‖R_α y^δ‖ · ‖T R_α y^δ − y^δ‖` over `α > 0`. -/
  minimal : ∀ β : Set.Ioi (0 : ℝ),
    ‖R α z‖ * ‖T (R α z) - z‖ ≤ ‖R β z‖ * ‖T (R β z) - z‖

end AutoIp

end _def_heuristic_rules
