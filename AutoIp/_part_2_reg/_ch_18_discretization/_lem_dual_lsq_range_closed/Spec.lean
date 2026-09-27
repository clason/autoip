/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

section _lem_dual_lsq_range_closed

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- For `T ∈ L(X, Y)` and nested subspaces `Y₁ ⊂ Y₂ ⊂ ⋯` of `Y` with `dim Yₙ = n`, the range
`Ran(Qₙ T)` is closed for every `n`, where `Qₙ := P_{Yₙ}`. -/
public theorem isClosed_range_dualLsq (T : E →L[𝕜] F) (Y : ℕ → Submodule 𝕜 F)
    [∀ n, (Y n).HasOrthogonalProjection] (hmono : Monotone Y)
    (hfin : ∀ n, Module.finrank 𝕜 (Y n) = n) (n : ℕ) :
    IsClosed (((Y n).starProjection ∘L T).toLinearMap.range : Set F) := by
  have : FiniteDimensional 𝕜 (Y (n + 1)) :=
    FiniteDimensional.of_finrank_pos (by rw [hfin]; omega)
  have : FiniteDimensional 𝕜 (Y n) :=
    Submodule.finiteDimensional_of_le (hmono (Nat.le_succ n))
  have : FiniteDimensional 𝕜
      (LinearMap.range ((Y n).starProjection ∘L T).toLinearMap) := by
    refine Submodule.finiteDimensional_of_le (S₂ := Y n) ?_
    rintro z ⟨x, rfl⟩
    exact (Y n).starProjection_apply_mem _
  exact Submodule.closed_of_finiteDimensional _

end AutoIp

end _lem_dual_lsq_range_closed
