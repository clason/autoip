/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
import AutoIp._part_2_reg._ch_11_moore_penrose._cor_normal_equation

section _lem_normal_mp

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- For `y ∈ Dom(T†)`, `T* y ∈ Dom((T* T)†)`, so that the right-hand side of
`T† y = (T* T)† T* y` is defined. The node leaves this membership implicit. -/
public theorem mem_mpDomain_adjoint_comp_self {T : E →L[𝕜] F} {y : F} (hy : y ∈ mpDomain T) :
    T.adjoint y ∈ mpDomain (T.adjoint ∘L T) :=
  Submodule.mem_sup_left
    ⟨moorePenrose T ⟨y, hy⟩,
      isLeastSquares_iff_adjoint_comp_self_apply_eq.1 (moorePenrose_isMinimumNorm ⟨_, hy⟩).1⟩

/-- For `y ∈ Dom(T†)` one has `T† y = (T* T)† T* y`. -/
public
theorem moorePenrose_eq_moorePenrose_adjoint_comp_self {T : E →L[𝕜] F} {y : F}
    (hy : y ∈ mpDomain T) :
    moorePenrose T ⟨y, hy⟩ = moorePenrose (T.adjoint ∘L
        T) ⟨(T.adjoint y), (mem_mpDomain_adjoint_comp_self hy)⟩ := by
  have hmin := moorePenrose_isMinimumNorm ⟨_, hy⟩
  have hker : moorePenrose T ⟨y, hy⟩ ∈ (LinearMap.ker T.toLinearMap)ᗮ := (isMinimumNorm_iff.1
      hmin).2
  have hnormal : (ContinuousLinearMap.adjoint T ∘L T) (moorePenrose T ⟨y, hy⟩)
      = ContinuousLinearMap.adjoint T y := isLeastSquares_iff_adjoint_comp_self_apply_eq.1
        hmin.1
  have hls2 : IsLeastSquares (ContinuousLinearMap.adjoint T ∘L T)
      (ContinuousLinearMap.adjoint T y) (moorePenrose T ⟨y, hy⟩) := by
    intro z
    rw [hnormal, sub_self, norm_zero]
    exact norm_nonneg _
  have hkerS : moorePenrose T ⟨y, hy⟩ ∈
      (LinearMap.ker (ContinuousLinearMap.adjoint T ∘L T).toLinearMap)ᗮ := by
    rw [ContinuousLinearMap.ker_adjoint_comp_self]
    exact hker
  exact eq_moorePenrose_of_isLeastSquares hls2 hkerS

end AutoIp

end _lem_normal_mp
