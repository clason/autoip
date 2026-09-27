/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_domain_dense.Spec

namespace AutoIp

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- If `Ran(T)` is closed, then every `y ∈ Y` lies in `Dom(T†)`. -/
public theorem mem_mpDomain_of_isClosed_range {T : E →L[𝕜] F}
    (hclosed : IsClosed (T.toLinearMap.range : Set F)) (y : F) : y ∈ mpDomain T := by
  rw [mpDomain_eq_top_iff.2 hclosed]; exact Submodule.mem_top

end AutoIp
