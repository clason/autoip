/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# FiniteDimensional

Finite-dimensionality of a monotone family of subspaces with prescribed ranks.
-/

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A monotone family of subspaces whose `n`-th member has rank `n` is
finite-dimensional at every index. -/
public theorem finiteDimensional_of_monotone_finrank {X : ℕ → Submodule 𝕜 E}
    (hmono : Monotone X) (hfin : ∀ n, Module.finrank 𝕜 (X n) = n) (m : ℕ) :
    FiniteDimensional 𝕜 (X m) := by
  have : FiniteDimensional 𝕜 (X (m + 1)) :=
    FiniteDimensional.of_finrank_pos (by rw [hfin]; omega)
  exact Submodule.finiteDimensional_of_le (hmono (Nat.le_succ m))

end AutoIp
