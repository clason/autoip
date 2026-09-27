/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_08_svd._def_singular_system
public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
import AutoIp._part_2_reg._ch_12_picard._cor_picard_domain

section _lem_mp_singular_vector

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- `uₙ ∈ Dom(K†)` for every index `n`. -/
public theorem mem_mpDomain_u (hs : IsSingularSystem K σ v u) (i : ι) : u i ∈ mpDomain K := by
  have hne : (RCLike.ofReal (σ i) : 𝕜) ≠ 0 := by simpa using (hs.pos i).ne'
  have hK : K ((RCLike.ofReal (σ i)⁻¹ : 𝕜) • v i) = u i := by
    rw [ContinuousLinearMap.map_smul, hs.map_left, smul_smul, RCLike.ofReal_inv,
      inv_mul_cancel₀ hne, one_smul]
  exact Submodule.mem_sup_left ⟨(RCLike.ofReal (σ i)⁻¹ : 𝕜) • v i, hK⟩

/-- `K† uₙ = σₙ⁻¹ vₙ` for every index `n`. The singular system need not be ordered, and `K`
need not be compact. -/
public theorem moorePenrose_apply_u (hs : IsSingularSystem K σ v u) (i : ι) :
    moorePenrose K ⟨(u i), (mem_mpDomain_u hs i)⟩ = (((σ i)⁻¹ : ℝ) : 𝕜) • v i := by
  classical
  have h1 := hasSum_moorePenrose hs (mem_mpDomain_u hs i)
  have hfun : (fun m => ((RCLike.ofReal (σ m)⁻¹ : 𝕜) * inner 𝕜 (u m) (u i)) • v m)
      = fun m => if m = i then ((RCLike.ofReal (σ i)⁻¹ : 𝕜)) • v i else 0 := by
    funext m
    rw [orthonormal_iff_ite.1 hs.orthonormal_right m i]
    by_cases h : m = i
    · subst h; simp
    · simp [h]
  rw [hfun] at h1
  exact h1.unique (hasSum_ite_eq i _)

end AutoIp

end _lem_mp_singular_vector
