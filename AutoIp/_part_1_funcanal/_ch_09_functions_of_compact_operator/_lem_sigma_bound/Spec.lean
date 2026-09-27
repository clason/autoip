/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_08_svd._def_singular_system

section _lem_sigma_bound

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- `σₙ² ∈ [0, ‖K‖²]` for every index `n` of a singular system of `K`, ordered or not. The
singular system may be indexed by an arbitrary type. -/
public theorem IsSingularSystem.sq_mem_Icc (hs : IsSingularSystem K σ v u) (i : ι) :
    σ i ^ 2 ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2) := by
  have hv1 : ‖v i‖ = 1 := hs.orthonormal_left.1 i
  have hu1 : ‖u i‖ = 1 := hs.orthonormal_right.1 i
  have h1 : ‖K (v i)‖ = σ i := by
    rw [hs.map_left i, norm_smul, RCLike.norm_ofReal, abs_of_pos (hs.pos i), hu1, mul_one]
  have h2 : σ i ≤ ‖K‖ := by
    rw [← h1]
    simpa [hv1] using K.le_opNorm (v i)
  exact ⟨by positivity, by nlinarith [hs.pos i, norm_nonneg K]⟩

/-- `σₙ ≤ ‖K‖` for every index `n` of a singular system of `K`, ordered or not. The singular
system may be indexed by an arbitrary type. -/
public theorem IsSingularSystem.le_opNorm (hs : IsSingularSystem K σ v u) (i : ι) : σ i ≤ ‖K‖ := by
  have h := (hs.sq_mem_Icc i).2
  nlinarith [hs.pos i, norm_nonneg K]

end _lem_sigma_bound
