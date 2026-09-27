/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose_bounded
public import AutoIp._part_1_funcanal._ch_03_hilbert_spaces._lem_closed_range_adjoint
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_characterisation
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_equations

section

open scoped InnerProductSpace
namespace AutoIp

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- If `Ran(T)` is closed, then `T†` is its bounded realisation in `L(Y,X)`, viewed as a
partially defined operator with domain `Y`. -/
public theorem moorePenrose_eq_toPMap {T : E →L[𝕜] F}
    (hclosed : IsClosed (T.toLinearMap.range : Set F)) :
    moorePenrose T = (moorePenroseL hclosed : F →ₗ[𝕜] E).toPMap ⊤ := by
  refine LinearPMap.ext ?_ ?_
  · exact mpDomain_eq_top_iff.2 hclosed
  · intro y hf hg
    exact moorePenroseL_apply hclosed y |>.symm

end AutoIp

end
