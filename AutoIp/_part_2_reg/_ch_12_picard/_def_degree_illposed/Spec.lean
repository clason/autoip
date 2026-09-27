/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_08_svd._def_singular_system

section _def_degree_illposed

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {I : Set ℕ} {σ : I → ℝ} {v : I → E} {u : I → F}

/-- `K` is moderately ill-posed: there are `c, r > 0` with `σₙ ≥ c n^{-r}` for all `n ∈ I`. The
indices start at `0`, so `n` is written `i + 1`, and an unused singular-system argument records that
the `σₙ` are the singular values of `K`. Severely ill-posed, the negation, has no declaration of its
own. -/
-- The condition is an argument because the object is defined only under it, though the
-- formula does not read it.
@[expose]
public def IsModeratelyIllPosed (_hs : IsOrderedSingularSystem K σ v u) : Prop :=
  ∃ c r : ℝ, 0 < c ∧ 0 < r ∧ ∀ i : I, c * (((i : ℕ) : ℝ) + 1) ^ (-r) ≤ σ i

/-- `K` is exponentially ill-posed: there are `c, r > 0` with `σₙ ≤ c e^{-n^r}` for all
`n ∈ I`. The indices start at `0`, so `n` is written `i + 1`, and an unused singular-system
argument records that the `σₙ` are the singular values of `K`. -/
-- The condition is an argument because the object is defined only under it, though the
-- formula does not read it.
@[expose]
public def IsExponentiallyIllPosed (_hs : IsOrderedSingularSystem K σ v u) : Prop :=
  ∃ c r : ℝ, 0 < c ∧ 0 < r ∧ ∀ i : I, σ i ≤ c * Real.exp (-((((i : ℕ) : ℝ) + 1) ^ r))

end AutoIp

end _def_degree_illposed
