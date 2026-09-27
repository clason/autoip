/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_08_svd._def_singular_system.Spec

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Each left singular vector is orthogonal to `ker K`. -/
public theorem IsSingularSystem.mem_orthogonal_ker (hs : IsSingularSystem K σ v u) (i : ι) :
    v i ∈ (K.toLinearMap.ker)ᗮ := by
  rw [← hs.span_left]
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)
