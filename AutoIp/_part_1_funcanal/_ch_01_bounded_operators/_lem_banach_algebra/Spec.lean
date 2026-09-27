/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
import Cite.Attribute

section _lem_banach_algebra

attribute [cite] ContinuousLinearMap.opNorm_comp_le
attribute [cite] ContinuousLinearMap.toNormedRing

attribute [cite] ContinuousLinearMap.toNormedAlgebra

end _lem_banach_algebra

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/- If `X` is Banach, `L(X,X)` is a Banach algebra: a complete normed algebra. -/
example : Nonempty (NormedAlgebra 𝕜 (E →L[𝕜] E)) := ⟨inferInstance⟩

example [CompleteSpace E] : CompleteSpace (E →L[𝕜] E) := inferInstance
