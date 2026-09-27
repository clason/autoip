/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual -- shake: keep
import Cite.Attribute

section _def_dual_operator

-- The dual operator is precomposition, which Mathlib has in the generality of
-- semilinear maps between topological modules.  Its name says composition
-- rather than duality, so the examples below relate it to the blueprint's
-- wording.
attribute [cite] ContinuousLinearMap.precomp

end _def_dual_operator

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

-- `T' ∈ L(Y', X')` for `T ∈ L(X, Y)`: the types the prose assigns.
example (T : E →L[𝕜] F) : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E :=
  ContinuousLinearMap.precomp 𝕜 T

-- `T'g = g ∘ T`, the defining equation.
example (T : E →L[𝕜] F) (g : StrongDual 𝕜 F) :
    ContinuousLinearMap.precomp 𝕜 T g = g.comp T := rfl

-- `⟨Tx, g⟩ = ⟨x, T'g⟩`, the characterisation, in the pairing of a space with
-- its dual: both sides are `g (T x)`.
example (T : E →L[𝕜] F) (g : StrongDual 𝕜 F) (x : E) :
    g (T x) = ContinuousLinearMap.precomp 𝕜 T g x := rfl

-- The dual of the identity is the identity.
example : ContinuousLinearMap.precomp 𝕜 (ContinuousLinearMap.id 𝕜 E)
    = ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 E) := by
  ext g x
  simp

-- Contravariance: `(T ∘ S)' = S' ∘ T'`.
example {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (S : E →L[𝕜] F) (T : F →L[𝕜] G) :
    ((ContinuousLinearMap.precomp 𝕜 S).comp (ContinuousLinearMap.precomp 𝕜 T)
        : StrongDual 𝕜 G →L[𝕜] StrongDual 𝕜 E)
      = ContinuousLinearMap.precomp 𝕜 (T.comp S) := by
  ext g x
  simp
