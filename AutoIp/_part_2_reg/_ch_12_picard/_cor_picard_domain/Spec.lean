/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_08_svd._def_singular_system
public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_equations
import AutoIp._part_2_reg._ch_12_picard._thm_picard

section _cor_picard_domain

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- `K† y = ∑ₙ σₙ⁻¹ ⟨uₙ, y⟩ vₙ` for every `y ∈ Dom(K†)`. The singular system need not be
ordered, and `K` need not be compact. -/
public theorem hasSum_moorePenrose (hs : IsSingularSystem K σ v u) {y : F} (hy : y ∈ mpDomain K) :
    HasSum (fun i => ((((σ i)⁻¹ : ℝ) : 𝕜) * inner 𝕜 (u i) y) • v i)
      (moorePenrose K ⟨y, hy⟩) := by
  have hz : K (moorePenrose K ⟨y, hy⟩) ∈ LinearMap.range K.toLinearMap :=
    ⟨moorePenrose K ⟨y, hy⟩, rfl⟩
  have hsum := hasSum_moorePenrose_of_mem_range hs hz
  rw [moorePenrose_comp_self_comp_moorePenrose hy] at hsum
  have hcoef : ∀ i, (inner 𝕜 (u i) (K (moorePenrose K ⟨y, hy⟩)) : 𝕜) = inner 𝕜 (u i) y := by
    intro i
    rw [apply_moorePenrose ⟨_, hy⟩]
    have hui : u i ∈ (LinearMap.range K.toLinearMap).topologicalClosure := by
      rw [← hs.span_right]
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hui]
  have hfun : (fun i => ((RCLike.ofReal (σ i)⁻¹ : 𝕜) *
        inner 𝕜 (u i) (K (moorePenrose K ⟨y, hy⟩))) • v i)
      = fun i => ((RCLike.ofReal (σ i)⁻¹ : 𝕜) * inner 𝕜 (u i) y) • v i := by
    funext i
    rw [hcoef i]
  rwa [hfun] at hsum

end AutoIp

end _cor_picard_domain
