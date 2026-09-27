/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
import AutoIp._part_2_reg._ch_11_moore_penrose._thm_mp_minnorm

section _cor_normal_equation

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- For `y ∈ Y`, `x ∈ X` is a least squares solution of `T x = y` if and only if
`T* T x = T* y`. -/
public theorem isLeastSquares_iff_adjoint_comp_self_apply_eq [CompleteSpace F] {T : E →L[𝕜] F}
    {y : F} {x : E} :
    IsLeastSquares T y x ↔
      (T.adjoint ∘L T) x = T.adjoint y := by
  rw [isLeastSquares_iff_sub_mem_orthogonal_range, T.orthogonal_range, LinearMap.mem_ker]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, map_sub, sub_eq_zero]
  exact eq_comm

/-- If `x` is a least squares solution of `T x = y` with `x ∈ Ker(T)ᗮ`, then `y ∈ Dom(T†)`
and `x = T† y`. The membership `y ∈ Dom(T†)` is not a separate conclusion: the statement
derives it from the hypotheses to form `T† y`. -/
public theorem eq_moorePenrose_of_isLeastSquares {T : E →L[𝕜] F} {y : F} {x : E}
    (hx : IsLeastSquares T y x) (hker : x ∈ T.toLinearMap.kerᗮ) :
    x = moorePenrose T ⟨y, hx.mem_mpDomain⟩ :=
  (isMinimumNorm_iff.2 ⟨isLeastSquares_iff_sub_mem_orthogonal_range.1 hx, hker⟩).unique
    (moorePenrose_isMinimumNorm ⟨_, hx.mem_mpDomain⟩)

end AutoIp

end _cor_normal_equation
