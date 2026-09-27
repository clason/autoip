/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Orthogonal

section _lem_dim_count

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Dimension counting: if `U`, `V` are subspaces with `U` finite-dimensional and
`dim U < dim V`, then `V ∩ U⊥ ≠ {0}`, that is, some `v ≠ 0` lies in both `V` and `U⊥`.

The dimensions are compared as cardinals, so `V` may be infinite-dimensional. The ambient
space need not be complete. -/
public theorem Submodule.exists_ne_zero_mem_inf_orthogonal_of_rank_lt
    {U V : Submodule 𝕜 E} [FiniteDimensional 𝕜 U]
    (h : Module.rank 𝕜 U < Module.rank 𝕜 V) :
    ∃ v : E, v ≠ 0 ∧ v ∈ V ∧ v ∈ Uᗮ := by
  -- `v ↦ P_U v` on `V` cannot be injective, since `V` has the larger dimension, and its
  -- kernel is `V ⊓ Uᗮ`.
  set f : V →ₗ[𝕜] U :=
    (U.orthogonalProjectionOnto : E →L[𝕜] U).toLinearMap.comp V.subtype with hf
  have hninj : ¬ Function.Injective f := fun hinj =>
    (LinearMap.rank_le_of_injective f hinj).not_gt h
  have hker : LinearMap.ker f ≠ ⊥ := by
    rwa [Ne, LinearMap.ker_eq_bot]
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨(w : E), ?_, w.2, ?_⟩
  · simpa using hw0
  · have : U.orthogonalProjectionOnto (w : E) = 0 := hw
    rwa [Submodule.orthogonalProjectionOnto_eq_zero_iff] at this

end _lem_dim_count
