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
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_fun_calc.Helpers

section _def_fun_calc

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- The series `x ↦ ∑ₙ φ(σₙ²) ⟨vₙ, x⟩ vₙ` in the formula for `φ(K*K)`, as a linear map. It is in
the Spec because `φ(K*K)` is built from it and a definition can live only in a Spec; it is private
because it is a step of the construction that the node does not state. -/
noncomputable def IsSingularSystem.funCalcLinear (hs : IsSingularSystem K σ v u)
    (φ : ℝ → ℝ) (hφ : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C) : E →ₗ[𝕜] E where
  toFun x := ∑' i, ((RCLike.ofReal (φ (σ i ^ 2)) : 𝕜) * inner 𝕜 (v i) x) • v i
  map_add' x y := by
    have h := (hs.summable_mul_inner_smul hφ x).hasSum.add
      (hs.summable_mul_inner_smul hφ y).hasSum
    have hfun : (fun i => ((RCLike.ofReal (φ (σ i ^ 2)) : 𝕜) * inner 𝕜 (v i) x) • v i
        + ((RCLike.ofReal (φ (σ i ^ 2)) : 𝕜) * inner 𝕜 (v i) y) • v i)
        = fun i => ((RCLike.ofReal (φ (σ i ^ 2)) : 𝕜) * inner 𝕜 (v i) (x + y)) • v i := by
      funext i
      rw [inner_add_right, mul_add, add_smul]
    rw [hfun] at h
    exact h.tsum_eq
  map_smul' c x := by
    have h := (hs.summable_mul_inner_smul hφ x).hasSum.const_smul c
    have hfun : (fun i => c • (((RCLike.ofReal (φ (σ i ^ 2)) : 𝕜) * inner 𝕜 (v i) x) • v i))
        = fun i => ((RCLike.ofReal (φ (σ i ^ 2)) : 𝕜) * inner 𝕜 (v i) (c • x)) • v i := by
      funext i
      rw [inner_smul_right, smul_smul]
      ring_nf
    rw [hfun] at h
    exact h.tsum_eq

/-- The bound `‖∑ₙ φ(σₙ²) ⟨vₙ, x⟩ vₙ‖ ≤ C ‖x‖`, needed in the Spec because the definition of
`φ(K*K)` takes it as the continuity bound of the series, and it is stated through the series as
a linear map, a definition of this Spec. -/
theorem IsSingularSystem.norm_funCalcLinear_le (hs : IsSingularSystem K σ v u)
    (φ : ℝ → ℝ) (hφ : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C) (x : E) :
    ‖hs.funCalcLinear φ hφ x‖ ≤ max hφ.choose 0 * ‖x‖ := by
  set C := max hφ.choose 0 with hCdef
  have hC0 : (0 : ℝ) ≤ C := le_max_right _ _
  have hCb : ∀ i, |φ (σ i ^ 2)| ≤ C := fun i =>
    le_trans (hφ.choose_spec i) (le_max_left _ _)
  have hz := (hs.summable_mul_inner_smul hφ x).hasSum
  have hnorm := hs.orthonormal_left.norm_sq_eq_tsum_norm_sq hz
  have hsq : ‖∑' i, ((RCLike.ofReal (φ (σ i ^ 2)) : 𝕜) * inner 𝕜 (v i) x) • v i‖ ^ 2
      ≤ (C * ‖x‖) ^ 2 := by
    rw [hnorm, mul_pow]
    calc ∑' i, ‖(RCLike.ofReal (φ (σ i ^ 2)) : 𝕜) * inner 𝕜 (v i) x‖ ^ 2
        ≤ ∑' i, C ^ 2 * ‖(inner 𝕜 (v i) x : 𝕜)‖ ^ 2 := by
          refine Summable.tsum_le_tsum (fun i => ?_) ?_
              ((hs.orthonormal_left.inner_products_summable (x := x)).mul_left _)
          · rw [norm_mul, mul_pow, RCLike.norm_ofReal]
            have h2 : |φ (σ i ^ 2)| ^ 2 ≤ C ^ 2 := by
              nlinarith [abs_nonneg (φ (σ i ^ 2)), hCb i]
            exact mul_le_mul_of_nonneg_right h2 (by positivity)
          · rw [← hs.orthonormal_left.summable_iff_norm_sq_summable]
            exact hs.summable_mul_inner_smul hφ x
      _ = C ^ 2 * ∑' i, ‖(inner 𝕜 (v i) x : 𝕜)‖ ^ 2 :=
          (hs.orthonormal_left.inner_products_summable (x := x)).tsum_mul_left _
      _ ≤ C ^ 2 * ‖x‖ ^ 2 :=
          mul_le_mul_of_nonneg_left
            (hs.orthonormal_left.tsum_inner_products_le x) (by positivity)
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq

/-- The operator `φ(K*K) ∈ ℒ(X,X)` for a real-valued `φ`, given by
`φ(K*K) x = ∑ₙ φ(σₙ²) ⟨vₙ, x⟩ vₙ + φ(0) P_{𝒩(K)} x`.

The hypothesis asks `φ` to be bounded only at the points `σₙ²`, not on all of `[0, κ]`, and `φ`
is a function on `ℝ`. The operator is built from the given singular system; that it does not
depend on the choice of singular system is not stated. -/
public noncomputable def IsSingularSystem.funCalc (hs : IsSingularSystem K σ v u)
    (φ : ℝ → ℝ) (hφ : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C) : E →L[𝕜] E :=
  LinearMap.mkContinuous (hs.funCalcLinear φ hφ) (max hφ.choose 0)
      (hs.norm_funCalcLinear_le φ hφ)
    + (RCLike.ofReal (φ 0) : 𝕜) • (LinearMap.ker K.toLinearMap).starProjection

/-- The formula defining `φ(K*K)`: for every `x ∈ X` the series `∑ₙ φ(σₙ²) ⟨vₙ, x⟩ vₙ`
converges to `φ(K*K) x - φ(0) P_{𝒩(K)} x`. -/
public theorem IsSingularSystem.hasSum_funCalc_sub_starProjection (hs : IsSingularSystem K σ v u)
    {φ : ℝ → ℝ} (hφ : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C) (x : E) :
    HasSum (fun i => ((φ (σ i ^ 2) : 𝕜) * inner 𝕜 (v i) x) • v i)
      (hs.funCalc φ hφ x
        - (φ 0 : 𝕜) • K.toLinearMap.ker.starProjection x) := by
  have hsum : Summable
      (fun i => ((RCLike.ofReal (φ (σ i ^ 2)) : 𝕜) * inner 𝕜 (v i) x) • v i) :=
    hs.summable_mul_inner_smul hφ x
  have hdef : hs.funCalc φ hφ x -
      (RCLike.ofReal (φ 0) : 𝕜) • (LinearMap.ker K.toLinearMap).starProjection x
      = ∑' i, ((RCLike.ofReal (φ (σ i ^ 2)) : 𝕜) * inner 𝕜 (v i) x) • v i := by
    unfold IsSingularSystem.funCalc
    simp [IsSingularSystem.funCalcLinear]
  rw [hdef]
  exact hsum.hasSum

end _def_fun_calc
