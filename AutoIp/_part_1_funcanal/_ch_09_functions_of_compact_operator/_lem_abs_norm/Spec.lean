/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_frac_power
import AutoIp._part_1_funcanal._ch_08_svd._lem_svd_companion
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound

section _lem_abs_norm

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- `|K|^r` is self-adjoint. It is stated for `r ≥ 0`, where the prose has `r > 0`. -/
public theorem IsSingularSystem.isSelfAdjoint_absRpow (hs : IsSingularSystem K σ v u) (r : ℝ)
    (hr : 0 ≤ r) : IsSelfAdjoint (hs.absRpow r hr) := by
  rw [hs.absRpow_def r hr (hs.exists_bound_rpow_sq (by linarith))]
  exact hs.isSelfAdjoint_funCalc _

/-- `‖|K| x‖_X = ‖K x‖_Y` for all `x ∈ X`. -/
public theorem IsSingularSystem.norm_absRpow_one_apply_eq_norm_map (hs : IsSingularSystem K σ v u)
    (x : E) :
    ‖hs.absRpow 1 zero_le_one x‖ = ‖K x‖ := by
  have hval : ∀ i, (σ i ^ 2) ^ ((1 : ℝ) / 2) = σ i := hs.rpow_sq_half
  have hb : ∃ C, ∀ i, |(fun t : ℝ => t ^ ((1 : ℝ) / 2)) (σ i ^ 2)| ≤ C :=
    hs.exists_bound_rpow_sq (c := 1 / 2) (by norm_num)
  have h := hs.hasSum_funCalc_sub_starProjection (φ := fun t : ℝ => t ^ ((1 : ℝ) / 2)) hb x
  simp only [hval, Real.zero_rpow (by norm_num : (1 : ℝ) / 2 ≠ 0), RCLike.ofReal_zero,
    zero_smul, sub_zero] at h
  have h1 := hs.orthonormal_left.norm_sq_eq_tsum_norm_sq h
  have h2 := hs.orthonormal_right.norm_sq_eq_tsum_norm_sq (hs.hasSum x)
  have h3 : ‖hs.absRpow 1 zero_le_one x‖ ^ 2 = ‖K x‖ ^ 2 := by
    rw [hs.absRpow_def 1 zero_le_one hb, h1, h2]
  have h4 := congrArg Real.sqrt h3
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h4

/-- `ℛ(|K|) = ℛ(K*)`. -/
public theorem IsSingularSystem.range_absRpow_one (hs : IsSingularSystem K σ v u) :
    (hs.absRpow 1 zero_le_one).toLinearMap.range =
      K.adjoint.toLinearMap.range := by
  have hval : ∀ i, (σ i ^ 2) ^ ((1 : ℝ) / 2) = σ i := hs.rpow_sq_half
  have hb : ∃ C, ∀ i, |(fun t : ℝ => t ^ ((1 : ℝ) / 2)) (σ i ^ 2)| ≤ C :=
    hs.exists_bound_rpow_sq (c := 1 / 2) (by norm_num)
  have habs : ∀ x : E, HasSum (fun i => ((RCLike.ofReal (σ i) : 𝕜) * inner 𝕜 (v i) x) • v i)
      (hs.absRpow 1 zero_le_one x) := by
    intro x
    have h := hs.hasSum_funCalc_sub_starProjection (φ := fun t : ℝ => t ^ ((1 : ℝ) / 2)) hb x
    simp only [hval, Real.zero_rpow (by norm_num : (1 : ℝ) / 2 ≠ 0), RCLike.ofReal_zero,
      zero_smul, sub_zero] at h
    rw [hs.absRpow_def 1 zero_le_one hb]
    exact h
  refine le_antisymm ?_ ?_
  · rintro z ⟨w, rfl⟩
    have hsummable : Summable (fun i => (inner 𝕜 (v i) w : 𝕜) • u i) := by
      rw [hs.orthonormal_right.summable_iff_norm_sq_summable]
      exact hs.orthonormal_left.inner_products_summable (x := w)
    have hy := hsummable.hasSum
    have hcoef : ∀ i, (inner 𝕜 (u i) (∑' i, (inner 𝕜 (v i) w : 𝕜) • u i) : 𝕜)
        = inner 𝕜 (v i) w := fun i => hs.orthonormal_right.inner_right_of_hasSum hy i
    refine ⟨∑' i, (inner 𝕜 (v i) w : 𝕜) • u i, ?_⟩
    have h1 := hs.hasSum_adjoint (∑' i, (inner 𝕜 (v i) w : 𝕜) • u i)
    simp only [hcoef] at h1
    exact h1.unique (habs w)
  · rintro z ⟨y, rfl⟩
    have hsummable : Summable (fun i => (inner 𝕜 (u i) y : 𝕜) • v i) := by
      rw [hs.orthonormal_left.summable_iff_norm_sq_summable]
      exact hs.orthonormal_right.inner_products_summable (x := y)
    have hw := hsummable.hasSum
    have hcoef : ∀ i, (inner 𝕜 (v i) (∑' i, (inner 𝕜 (u i) y : 𝕜) • v i) : 𝕜)
        = inner 𝕜 (u i) y := fun i => hs.orthonormal_left.inner_right_of_hasSum hw i
    refine ⟨∑' i, (inner 𝕜 (u i) y : 𝕜) • v i, ?_⟩
    have h1 := habs (∑' i, (inner 𝕜 (u i) y : 𝕜) • v i)
    simp only [hcoef] at h1
    exact h1.unique (hs.hasSum_adjoint y)

end _lem_abs_norm
