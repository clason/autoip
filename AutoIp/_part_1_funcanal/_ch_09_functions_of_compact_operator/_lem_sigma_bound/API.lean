/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound.Spec

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- A nonnegative real power is bounded at the squared singular values, `(‖K‖²)^c` being
a bound. -/
public theorem IsSingularSystem.exists_bound_rpow_sq (hs : IsSingularSystem K σ v u) {c : ℝ}
    (hc : 0 ≤ c) : ∃ C, ∀ i, |(fun t : ℝ => t ^ c) (σ i ^ 2)| ≤ C := by
  refine ⟨(‖K‖ ^ 2) ^ c, fun i => ?_⟩
  simp only
  rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact Real.rpow_le_rpow (by positivity) (hs.sq_mem_Icc i).2 hc
