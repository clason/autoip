/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Real.Basic

section _def_log_index

namespace AutoIp

/-- The logarithmic index function `φ^log_p(λ) := (log (eκ/λ))^(-p)` for `λ ∈ (0, κ]`, and
`φ^log_p(0) := 0`, for `p > 0`.

The function is defined on all of `ℝ`: it is `0` for `λ ≤ 0` and given by the same formula
for `λ > κ`. The hypothesis `0 < p` is not used by the body. -/
public noncomputable def logIndex (κ p : ℝ)
    -- The condition is an argument because the function is defined only under it, though the
    -- formula does not read it.
    (_hp : 0 < p) (lam : ℝ) : ℝ :=
  if lam ≤ 0 then 0 else (Real.log (Real.exp 1 * κ / lam)) ^ (-p)

end AutoIp

end _def_log_index
