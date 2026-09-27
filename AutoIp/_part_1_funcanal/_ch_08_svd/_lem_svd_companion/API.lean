/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_08_svd._lem_svd_companion.Spec
import AutoIp._part_1_funcanal._ch_03_hilbert_spaces._lem_kernel_normal
import AutoIp._part_1_funcanal._ch_04_orthonormal_series._lem_riesz_fischer

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- If `z = ∑ᵢ bᵢ vᵢ`, then `‖K z‖² = ∑ᵢ σᵢ² ‖bᵢ‖²`. -/
public theorem IsSingularSystem.norm_map_sq_eq_tsum_of_hasSum (hs : IsSingularSystem K σ v u)
    {b : ι → 𝕜} {z : E}
    (hz : HasSum (fun i => b i • v i) z) :
    ‖K z‖ ^ 2 = ∑' i, σ i ^ 2 * ‖b i‖ ^ 2 := by
  have hinner : ∀ j, (inner 𝕜 (v j) z : 𝕜) = b j := fun j =>
    hs.orthonormal_left.inner_right_of_hasSum hz j
  have h := hs.hasSum z
  simp only [hinner] at h
  rw [hs.orthonormal_right.norm_sq_eq_tsum_norm_sq h]
  refine tsum_congr fun i => ?_
  rw [norm_mul, RCLike.norm_ofReal, mul_pow, sq_abs]
