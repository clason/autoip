/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_18_discretization._def_lsq_projection.Spec
import all AutoIp._part_2_reg._ch_18_discretization._def_lsq_projection.Spec

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The defining equation. -/
public theorem lsqProjection_def (T : E →L[𝕜] F) (X : ℕ → Submodule 𝕜 E)
    [∀ n, (X n).HasOrthogonalProjection] (y : F)
    (hy : ∀ n, y ∈ mpDomain (T ∘L (X n).starProjection)) (n : ℕ) :
    lsqProjection T X y hy n = moorePenrose (T ∘L (X n).starProjection) ⟨y, (hy n)⟩ := by
  unfold lsqProjection
  rfl

end AutoIp
