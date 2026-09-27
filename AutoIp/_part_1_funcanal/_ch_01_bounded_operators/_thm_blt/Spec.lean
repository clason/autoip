/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
import Cite.Attribute

section _thm_blt

attribute [cite] ContinuousLinearMap.extend
attribute [cite] ContinuousLinearMap.extend_eq
attribute [cite] ContinuousLinearMap.extend_unique
attribute [cite] ContinuousLinearMap.opNorm_extend_le

end _thm_blt

-- The cited extension is along a dense embedding; along the inclusion of a dense subspace `M`
-- of `X` it is the node: a bounded operator `T` on `M` with values in a Banach space extends to
-- a bounded operator on `X` with no larger norm, and any two bounded extensions agree.
example {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y] (M : Submodule 𝕜 X)
    (hM : Dense (M : Set X)) (T : M →L[𝕜] Y) :
    (∃ S : X →L[𝕜] Y, S.comp M.subtypeL = T ∧ ‖S‖ ≤ ‖T‖) ∧
      ∀ S₁ S₂ : X →L[𝕜] Y, S₁.comp M.subtypeL = T → S₂.comp M.subtypeL = T → S₁ = S₂ := by
  have hd : DenseRange M.subtypeL := hM.denseRange_val
  have hi : IsUniformInducing M.subtypeL := isUniformEmbedding_subtype_val.isUniformInducing
  refine ⟨⟨T.extend M.subtypeL, ?_, ?_⟩, fun S₁ S₂ h₁ h₂ => ?_⟩
  · ext x
    exact ContinuousLinearMap.extend_eq T hd hi x
  · simpa using T.opNorm_extend_le (N := 1) hd (fun x => by simp)
  · rw [← ContinuousLinearMap.extend_unique T hd hi S₁ h₁,
      ContinuousLinearMap.extend_unique T hd hi S₂ h₂]
