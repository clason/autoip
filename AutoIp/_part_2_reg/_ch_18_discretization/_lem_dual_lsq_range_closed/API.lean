/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_18_discretization._lem_dual_lsq_range_closed.Spec
public import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_domain_dense

namespace AutoIp

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- For nested subspaces `Yₙ` with `dim Yₙ = n`, `Qₙ w ∈ Dom((Qₙ T)†)` for every `w`, since
`Ran(Qₙ T)` is closed. -/
public theorem mem_mpDomain_dualLsq (T : E →L[𝕜] F) (Y : ℕ → Submodule 𝕜 F)
    [∀ n, (Y n).HasOrthogonalProjection] (hmono : Monotone Y)
    (hfin : ∀ n, Module.finrank 𝕜 (Y n) = n) (w : F) (n : ℕ) :
    (Y n).starProjection w ∈ mpDomain ((Y n).starProjection ∘L T) :=
  mem_mpDomain_of_isClosed_range (isClosed_range_dualLsq T Y hmono hfin n) _

end AutoIp
