/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.Defs -- shake: keep

/-!
# Geometric

Monotonicity along geometrically spaced parameter grids.
-/

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- A geometric grid with ratio `q > 1` decreases. -/
public theorem as_le_of_geometric {N : ℕ} {α : ℕ → Set.Ioi (0 : ℝ)} {q : ℝ} (hq : 1 < q)
    (hgeom : ∀ i, i + 1 ≤ N → (α i : ℝ) = q * (α (i + 1) : ℝ))
    {i j : ℕ} (hij : i ≤ j) (hjN : j ≤ N) : (α j : ℝ) ≤ (α i : ℝ) := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih =>
    have h1 : (0 : ℝ) < (α (k + 1) : ℝ) := (α (k + 1)).2
    have h2 : (α k : ℝ) = q * (α (k + 1) : ℝ) := hgeom k hjN
    have h3 : (α (k + 1) : ℝ) ≤ (α k : ℝ) := by rw [h2]; nlinarith
    exact h3.trans (ih (Nat.le_of_succ_le hjN))

/-- The negative half-powers of a geometric grid with ratio `q > 1` increase. -/
public theorem rpow_neg_half_le_of_geometric {N : ℕ} {α : ℕ → Set.Ioi (0 : ℝ)} {q : ℝ}
    (hq : 1 < q) (hgeom : ∀ i, i + 1 ≤ N → (α i : ℝ) = q * (α (i + 1) : ℝ))
    {i j : ℕ} (hij : i ≤ j) (hjN : j ≤ N) :
    (α i : ℝ) ^ (-(1 : ℝ) / 2) ≤ (α j : ℝ) ^ (-(1 : ℝ) / 2) :=
  Real.rpow_le_rpow_of_nonpos (α j).2
    (as_le_of_geometric hq hgeom hij hjN) (by norm_num)

end AutoIp
