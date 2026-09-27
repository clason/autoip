/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose

section _def_regularization

namespace AutoIp

open Filter Topology
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The family `{R_α}_{α>0} ⊆ L(Y,X)` is a regularization of `T†`: `R_α y → T†y` as `α → 0`,
for every `y ∈ Dom(T†)`. -/
@[expose]
public def IsRegularization (T : E →L[𝕜] F) (R : Set.Ioi (0 : ℝ) → F →L[𝕜] E) : Prop :=
  ∀ y, ∀ hy : y ∈ mpDomain T,
    Tendsto (fun α => R α y) atBot (𝓝 (moorePenrose T ⟨y, hy⟩))

end AutoIp

end _def_regularization
