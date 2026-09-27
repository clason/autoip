/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_04_orthonormal_series._lem_riesz_fischer
public import AutoIp._part_1_funcanal._ch_08_svd._def_singular_system
import AutoIp._part_1_funcanal._ch_03_hilbert_spaces._lem_proj_characterisation
import AutoIp._part_1_funcanal._ch_04_orthonormal_series._lem_inner_through_series
import AutoIp._part_1_funcanal._ch_08_svd._lem_svd_companion
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound
import AutoIp.Auxiliary.BoundedOnIcc

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- The series defining the calculus converges whenever the function is bounded on the
squared singular values. -/
public theorem IsSingularSystem.summable_mul_inner_smul (hs : IsSingularSystem K σ v u) {φ : ℝ → ℝ}
    (hφ : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C) (x : E) :
    Summable (fun i => ((φ (σ i ^ 2) : 𝕜) * inner 𝕜 (v i) x) • v i) :=
  hs.orthonormal_left.summable_mul_inner_smul
    (hφ.imp fun _ hC i => by rw [RCLike.norm_ofReal]; exact hC i) x
