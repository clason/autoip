/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.RCLike.Lemmas

section _lem_finrank_compact

open scoped Topology
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A bounded linear operator T between normed spaces with finite-dimensional range 𝓡(T) is
compact. -/
public theorem IsCompactOperator.of_finiteDimensional_range (T : E →L[𝕜] F)
    (h : FiniteDimensional 𝕜 T.toLinearMap.range) : IsCompactOperator T := by
  -- Corestrict to the range, which is proper because it is finite-dimensional over an
  -- `RCLike` field, then compose back in.
  have hproper : ProperSpace (LinearMap.range T.toLinearMap) :=
    FiniteDimensional.proper_rclike 𝕜 _
  have hcod : IsCompactOperator
      (T.codRestrict (LinearMap.range T.toLinearMap) fun x => ⟨x, rfl⟩) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  exact hcod.clm_comp (LinearMap.range T.toLinearMap).subtypeL

end _lem_finrank_compact
