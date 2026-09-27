/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Group.Quotient

/-!
# QuotientNorm

On the orthogonal complement of a submodule the quotient norm of the quotient by
that submodule is the norm itself.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- On `Kᗮ` the quotient norm of `E ⧸ K` is the norm itself. -/
public theorem Submodule.Quotient.norm_mk_eq_norm_of_mem_orthogonal (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] {w : E} (hw : w ∈ Kᗮ) :
    ‖(Submodule.Quotient.mk w : E ⧸ K)‖ = ‖w‖ := by
  have h : K.quotientEquivOrthogonal (Submodule.Quotient.mk w) = ⟨w, hw⟩ :=
    Submodule.quotientEquivOfIsCompl_apply_mk_right K.isCompl_orthogonal ⟨w, hw⟩
  rw [← K.quotientEquivOrthogonal.norm_map (Submodule.Quotient.mk w), h]
  rfl
