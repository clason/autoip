/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Real.Basic

section _def_landweber_residual_poly

namespace AutoIp

/-- The Landweber residual family `q_k(λ) = (1 - ωλ)^k`, `k ≥ 0`. It is defined for every real
`ω`, where the prose fixes `ω ∈ (0, κ⁻¹]`. -/
public noncomputable def landweberResidualPoly (ω : ℝ) : ℕ → Polynomial ℝ :=
  fun k => (1 - Polynomial.C ω * Polynomial.X) ^ k

end AutoIp

end _def_landweber_residual_poly
