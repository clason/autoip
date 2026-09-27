/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

section _lem_proj_characterisation

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Characterisation of the orthogonal projection: for a closed subspace `U` and `x ∈ X`,
`z = P_U x` if and only if `z ∈ U` and `z - x ∈ U⊥`.

Of `U` only the existence of the orthogonal projection onto it is assumed, which holds for a
closed subspace of a Hilbert space; `X` itself need not be complete. -/
public theorem Submodule.eq_starProjection_iff
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (x z : E) :
    z = U.starProjection x ↔ z ∈ U ∧ z - x ∈ Uᗮ := by
  constructor
  · rintro rfl
    refine ⟨U.starProjection_apply_mem x, ?_⟩
    simpa only [neg_sub] using Submodule.neg_mem _ (U.sub_starProjection_mem_orthogonal x)
  · rintro ⟨hz, hzx⟩
    refine (U.eq_starProjection_of_mem_orthogonal hz ?_).symm
    simpa only [neg_sub] using Submodule.neg_mem _ hzx

end _lem_proj_characterisation
