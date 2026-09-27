/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_18_discretization._def_dual_lsq_projection.Spec
import all AutoIp._part_2_reg._ch_18_discretization._def_dual_lsq_projection.Spec

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The defining equation. -/
public theorem dualLsqProjection_def (T : E →L[𝕜] F) (Y : ℕ → Submodule 𝕜 F)
    [∀ n, (Y n).HasOrthogonalProjection] (y : F)
    (hy : ∀ n, (Y n).starProjection y ∈ mpDomain ((Y n).starProjection ∘L T)) (n : ℕ) :
    dualLsqProjection T Y y hy n
      = moorePenrose ((Y n).starProjection ∘L T) ⟨((Y n).starProjection y), (hy n)⟩ := by
  unfold dualLsqProjection
  rfl

end AutoIp
