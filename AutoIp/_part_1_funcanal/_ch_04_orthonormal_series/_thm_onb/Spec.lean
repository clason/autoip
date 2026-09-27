/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
import Cite.Attribute

section _thm_onb

attribute [cite] HilbertBasis.hasSum_repr
attribute [cite] HilbertBasis.tsum_inner_mul_inner
attribute [cite] exists_hilbertBasis

attribute [cite] HilbertBasis.repr_apply_apply

end _thm_onb

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {ι : Type*}

/- The expansion with the inner products as coefficients: `x = ∑ᵢ ⟨uᵢ, x⟩ uᵢ`. -/
example (b : HilbertBasis ι 𝕜 E) (x : E) :
    HasSum (fun i => (inner 𝕜 (b i) x : 𝕜) • b i) x := by
  simpa [b.repr_apply_apply] using b.hasSum_repr x
