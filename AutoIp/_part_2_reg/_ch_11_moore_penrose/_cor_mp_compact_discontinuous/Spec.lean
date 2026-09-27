/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import AutoIp._part_1_funcanal._ch_06_compact_operators._thm_compact_range_not_closed
import AutoIp._part_2_reg._ch_11_moore_penrose._thm_mp_continuous_iff_closed_range

section _cor_mp_compact_discontinuous

section

open scoped Topology
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- For compact `K`, `Ran(K)` is closed if and only if it is finite-dimensional. The Lean
asks only that `X` and `Y` be Banach spaces. -/
public
theorem IsCompactOperator.isClosed_range_iff_finiteDimensional [CompleteSpace E] [CompleteSpace F]
    {K : E →L[𝕜] F} (hK : IsCompactOperator K) :
    IsClosed (K.toLinearMap.range : Set F) ↔
      FiniteDimensional 𝕜 K.toLinearMap.range := by
  constructor
  · intro hc
    by_contra hfin
    exact hK.not_isClosed_range_of_not_finiteDimensional hfin hc
  · intro hfin
    exact (LinearMap.range K.toLinearMap).closed_of_finiteDimensional


end

section

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- If `K ∈ K(X,Y)` has infinite-dimensional range, then `K†` is unbounded: there is no
bound `‖K† y‖ ≤ C ‖y‖` on `Dom(K†)`. -/
public theorem not_exists_norm_moorePenrose_le_of_isCompactOperator {K : E →L[𝕜] F}
    (hK : IsCompactOperator K)
    (hinf : ¬ FiniteDimensional 𝕜 K.toLinearMap.range) :
    ¬ ∃ C : ℝ, ∀ y : (moorePenrose K).domain,
      ‖moorePenrose K y‖ ≤ C * ‖(y : F)‖ := fun hbdd =>
  hK.not_isClosed_range_of_not_finiteDimensional hinf
    (exists_norm_moorePenrose_le_iff_isClosed_range.1 hbdd)

end AutoIp

end

end _cor_mp_compact_discontinuous
