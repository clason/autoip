/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_fun_calc

section _def_general_source

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- The general source set `X_{φ,ρ} := {φ(K*K) w : w ∈ X, ‖w‖ ≤ ρ}` for `ρ > 0`.

`φ` need not be an index function: the definition asks only that it be bounded on the
`σᵢ²`, which the functional calculus needs, and `K` need only have a singular system. The
hypothesis `0 < ρ` is not used by the body. -/
public def sourceSetIndex (hs : IsSingularSystem K σ v u) (φ : ℝ → ℝ)
    (hφ : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C) (ρ : ℝ)
    -- The condition is an argument because the set is defined only under it, though the
    -- formula does not read it.
    (_hρ : 0 < ρ) : Set E :=
  (hs.funCalc φ hφ) '' {w : E | ‖w‖ ≤ ρ}

end AutoIp

end _def_general_source
