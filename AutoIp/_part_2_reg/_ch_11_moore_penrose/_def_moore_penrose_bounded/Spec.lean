/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module -- shake: keep-all

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
public import AutoIp._part_2_reg._ch_11_moore_penrose._thm_mp_continuous_iff_closed_range
public import AutoIp._part_2_reg._ch_11_moore_penrose._thm_mp_inverse
public import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_domain_dense

section _def_moore_penrose_bounded

namespace AutoIp

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- For `Ran(T)` closed, the Moore–Penrose inverse `T†` as an element of `L(Y,X)`. -/
@[expose]
public noncomputable def moorePenroseL {T : E →L[𝕜] F}
    (hclosed : IsClosed (T.toLinearMap.range : Set F)) : F →L[𝕜] E :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun y => moorePenrose T ⟨y, (mem_mpDomain_of_isClosed_range hclosed y)⟩
      map_add' := fun y z =>
        (moorePenrose T).map_add ⟨y, mem_mpDomain_of_isClosed_range hclosed _⟩
          ⟨z, mem_mpDomain_of_isClosed_range hclosed _⟩
      map_smul' := fun c y => by
        simp only [RingHom.id_apply]
        exact (moorePenrose T).map_smul c
          ⟨y, mem_mpDomain_of_isClosed_range hclosed _⟩ }
    (by
      obtain ⟨C, hC⟩ := exists_norm_moorePenrose_le_iff_isClosed_range.2 hclosed
      exact ⟨C, fun y => hC ⟨y, mem_mpDomain_of_isClosed_range hclosed y⟩⟩)

/-- The element of `L(Y,X)` is `T†`: it agrees with `T†` at every `y ∈ Y`. -/
public theorem moorePenroseL_apply {T : E →L[𝕜] F}
    (hclosed : IsClosed (T.toLinearMap.range : Set F)) (y : F) :
    moorePenroseL hclosed y
      = moorePenrose T ⟨y, (mem_mpDomain_of_isClosed_range hclosed y)⟩ := rfl

end AutoIp

end _def_moore_penrose_bounded
