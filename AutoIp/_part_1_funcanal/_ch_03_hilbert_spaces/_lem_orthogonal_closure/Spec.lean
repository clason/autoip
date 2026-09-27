/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule -- shake: keep
import Cite.Attribute

section _lem_orthogonal_closure

attribute [cite] Submodule.orthogonal_closure

end _lem_orthogonal_closure

-- The second claim, that `M` is dense if and only if `M⊥ = {0}`, is not cited: Mathlib's
-- statement of it is already cited by another node, and a constant is cited once. The
-- example shows that it is what the node says, for a subspace of a Hilbert space.
example {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] (M : Submodule 𝕜 E) : Dense (M : Set E) ↔ Mᗮ = ⊥ := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  exact Submodule.topologicalClosure_eq_top_iff
