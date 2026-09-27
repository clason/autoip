/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_12_picard._lem_mp_singular_vector.Spec
import AutoIp._part_2_reg._ch_12_picard._cor_picard_domain

open scoped InnerProductSpace
namespace AutoIp

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- `‖K† uₙ‖ = σₙ⁻¹` for every index `n`. -/
public theorem norm_moorePenrose_apply_u (hs : IsSingularSystem K σ v u) (i : ι) :
    ‖moorePenrose K ⟨(u i), (mem_mpDomain_u hs i)⟩‖ = (σ i)⁻¹ := by
  rw [moorePenrose_apply_u hs i, norm_smul, RCLike.norm_ofReal,
    hs.orthonormal_left.1 i, mul_one, abs_of_nonneg (inv_nonneg.mpr (hs.pos i).le)]

end AutoIp
