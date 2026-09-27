/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import AutoIp.Auxiliary.FiniteDimensional

section _lem_lsq_range_closed

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- For `T ∈ L(X, Y)` and nested subspaces `X₁ ⊂ X₂ ⊂ ⋯` of `X` with `dim Xₙ = n`, the range
`Ran(T Pₙ)` is closed for every `n`, where `Pₙ := P_{Xₙ}`. -/
public theorem isClosed_range_lsq (T : E →L[𝕜] F) (X : ℕ → Submodule 𝕜 E)
    [∀ n, (X n).HasOrthogonalProjection] (hmono : Monotone X)
    (hfin : ∀ n, Module.finrank 𝕜 (X n) = n) (n : ℕ) :
    IsClosed ((T ∘L (X n).starProjection).toLinearMap.range : Set F) := by
  have : FiniteDimensional 𝕜 (X n) :=
    finiteDimensional_of_monotone_finrank hmono hfin n
  have : FiniteDimensional 𝕜
      (LinearMap.range (T ∘L (X n).starProjection).toLinearMap) := by
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.map T.toLinearMap (X n)) ?_
    rintro z ⟨x, rfl⟩
    exact ⟨(X n).starProjection x, (X n).starProjection_apply_mem x, rfl⟩
  exact Submodule.closed_of_finiteDimensional _

end AutoIp

end _lem_lsq_range_closed
