/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_04_orthonormal_series._lem_riesz_fischer.Spec
public import Mathlib.Analysis.InnerProductSpace.Orthonormal

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*}

/-- For an orthonormal family `eᵢ` and bounded scalars `aᵢ`, the series `∑ᵢ aᵢ ⟨eᵢ, x⟩ eᵢ`
converges for every `x`. -/
public
theorem Orthonormal.summable_mul_inner_smul [CompleteSpace E] {e : ι → E} (he : Orthonormal 𝕜 e)
    {a : ι → 𝕜} (ha : ∃ C, ∀ i, ‖a i‖ ≤ C) (x : E) :
    Summable (fun i => (a i * inner 𝕜 (e i) x) • e i) := by
  obtain ⟨C, hC⟩ := ha
  rw [he.summable_iff_norm_sq_summable]
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    ((he.inner_products_summable (x := x)).mul_left (max C 0 ^ 2))
  rw [norm_mul, mul_pow]
  have hb : ‖a i‖ ≤ max C 0 := le_trans (hC i) (le_max_left _ _)
  have h2 : ‖a i‖ ^ 2 ≤ max C 0 ^ 2 := by nlinarith [norm_nonneg (a i)]
  exact mul_le_mul_of_nonneg_right h2 (by positivity)

