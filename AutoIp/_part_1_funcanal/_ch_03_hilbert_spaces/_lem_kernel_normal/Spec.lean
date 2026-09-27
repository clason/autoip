/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Cite.Attribute

section _lem_kernel_normal

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The normal operator has the same co-range: for `T ∈ 𝓛(X, Y)` between Hilbert spaces, the
closure of `R(T*T)` equals the closure of `R(T*)`, the second identity of the node. -/
public theorem ContinuousLinearMap.topologicalClosure_range_adjoint_comp_self
    [CompleteSpace E] [CompleteSpace F] (T : E →L[𝕜] F) :
    (T.adjoint ∘L T).toLinearMap.range.topologicalClosure =
      T.adjoint.toLinearMap.range.topologicalClosure := by
  have hsa : ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint T ∘L T) =
      ContinuousLinearMap.adjoint T ∘L T := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  calc (LinearMap.range (ContinuousLinearMap.adjoint T ∘L T).toLinearMap).topologicalClosure
      = ((ContinuousLinearMap.adjoint T ∘L T).ker)ᗮ := by
        rw [ContinuousLinearMap.orthogonal_ker, hsa]
    _ = (T.ker)ᗮ := by rw [ContinuousLinearMap.ker_adjoint_comp_self]
    _ = (LinearMap.range (ContinuousLinearMap.adjoint T).toLinearMap).topologicalClosure :=
        ContinuousLinearMap.orthogonal_ker T


attribute [cite] ContinuousLinearMap.ker_adjoint_comp_self

end _lem_kernel_normal
