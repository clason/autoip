/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_lsq_minnorm
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Orthogonal

namespace AutoIp

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- For `y ∈ Ran(T) + Ran(T)ᗮ`, the equation `T x = y` has a minimum norm solution. -/
public theorem exists_isMinimumNorm_of_mem_sup {T : E →L[𝕜] F} {y : F}
    (hy : y ∈ T.toLinearMap.range ⊔ T.toLinearMap.rangeᗮ) :
    ∃ x, IsMinimumNorm T y x := by
  rw [Submodule.mem_sup] at hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hy
  obtain ⟨x₀, rfl⟩ := ha
  refine ⟨x₀ - (LinearMap.ker T.toLinearMap).starProjection x₀, isMinimumNorm_iff.2 ⟨?_, ?_⟩⟩
  · have hkm : (LinearMap.ker T.toLinearMap).starProjection x₀ ∈ LinearMap.ker T.toLinearMap :=
      Submodule.starProjection_apply_mem _ _
    have hT : T (x₀ - (LinearMap.ker T.toLinearMap).starProjection x₀) = T x₀ := by
      have h0 : T ((LinearMap.ker T.toLinearMap).starProjection x₀) = 0 :=
        LinearMap.mem_ker.1 hkm
      rw [map_sub, h0, sub_zero]
    rw [hT]
    simpa using hb
  · exact (LinearMap.ker T.toLinearMap).sub_starProjection_mem_orthogonal x₀

end AutoIp
