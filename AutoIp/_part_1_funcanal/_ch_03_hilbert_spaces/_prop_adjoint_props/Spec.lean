/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Cite.Attribute

section _prop_adjoint_props

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Properties of the adjoint: `(α T)* = ᾱ T*`. -/
public theorem adjoint_smul (a : 𝕜) (T : E →L[𝕜] F) :
    adjoint (a • T) = (starRingEnd 𝕜) a • adjoint T :=
  map_smulₛₗ _ a T

/-- Properties of the adjoint: `‖T*‖ = ‖T‖`. -/
public theorem norm_adjoint (T : E →L[𝕜] F) : ‖adjoint T‖ = ‖T‖ :=
  (adjoint (𝕜 := 𝕜) (E := E) (F := F)).norm_map T

end ContinuousLinearMap

attribute [cite] ContinuousLinearMap.adjoint_adjoint
attribute [cite] ContinuousLinearMap.adjoint_comp
attribute [cite] ContinuousLinearMap.norm_adjoint_comp_self

end _prop_adjoint_props
