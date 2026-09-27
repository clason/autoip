/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose.Spec
import all AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose.Spec

namespace AutoIp

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- If `T x = y` has a least squares solution, then `y ∈ Dom(T†)`. -/
public theorem IsLeastSquares.mem_mpDomain {T : E →L[𝕜] F} {y : F} {x : E}
    (hx : IsLeastSquares T y x) : y ∈ mpDomain T := by
  rw [mpDomain]
  have he : y = T x + (y - T x) := by abel
  rw [he]
  exact Submodule.add_mem_sup ⟨x, rfl⟩ (isLeastSquares_iff_sub_mem_orthogonal_range.1 hx)

/-- `T† y` is the minimum norm solution of `T x = y`. -/
public theorem moorePenrose_isMinimumNorm [CompleteSpace E] {T : E →L[𝕜] F}
    (y : (moorePenrose T).domain) :
    IsMinimumNorm T (y : F) (moorePenrose T y) := by
  unfold moorePenrose moorePenroseLinear
  exact (exists_isMinimumNorm_of_mem_sup y.2).choose_spec

/-- `T† y ∈ Ker(T)ᗮ`. -/
public theorem moorePenrose_mem_orthogonal_ker [CompleteSpace E] {T : E →L[𝕜] F}
    (y : (moorePenrose T).domain) :
    moorePenrose T y ∈ T.toLinearMap.kerᗮ :=
  (isMinimumNorm_iff.1 (moorePenrose_isMinimumNorm y)).2

/-- `y - T T† y ∈ Ran(T)ᗮ`. -/
public theorem sub_apply_moorePenrose_mem_orthogonal [CompleteSpace E] {T : E →L[𝕜] F}
    (y : (moorePenrose T).domain) :
    (y : F) - T (moorePenrose T y) ∈ T.toLinearMap.rangeᗮ :=
  (isMinimumNorm_iff.1 (moorePenrose_isMinimumNorm y)).1

end AutoIp
