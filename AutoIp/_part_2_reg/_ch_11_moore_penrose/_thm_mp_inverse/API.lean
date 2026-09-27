/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._thm_mp_inverse.Spec
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_domain_dense
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_equations
import AutoIp._part_2_reg._ch_11_moore_penrose._thm_mp_minnorm

open scoped InnerProductSpace
namespace AutoIp

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- `T† 0 = 0`. -/
public theorem moorePenrose_zero {T : E →L[𝕜] F} :
    moorePenrose T ⟨(0 : F), (Submodule.zero_mem _)⟩ = 0 := by
  simpa using moorePenrose_apply_apply_of_mem_orthogonal (T := T) (Submodule.zero_mem _)

end AutoIp
