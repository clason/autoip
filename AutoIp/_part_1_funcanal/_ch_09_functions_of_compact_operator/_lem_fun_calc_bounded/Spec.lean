/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_fun_calc

section _lem_fun_calc_bounded

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- The bound on `‖φ(K*K)‖`: for any `a` with `|φ(σₙ²)| ≤ a` for all `n`,
`‖φ(K*K)‖ ≤ max a |φ(0)|`. This is the sharp form, from which the two printed bounds
`sup_n |φ(σₙ²)| + |φ(0)|` and `2 sup_{[0,κ]} |φ|` follow; they are not stated separately. -/
public theorem IsSingularSystem.norm_funCalc_le (hs : IsSingularSystem K σ v u) (φ : ℝ → ℝ)
    (a : ℝ) (ha : ∀ i, |φ (σ i ^ 2)| ≤ a) :
    ‖hs.funCalc φ ⟨a, ha⟩‖ ≤ max a |φ 0| := by
  have hb : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C := ⟨a, ha⟩
  have hM0 : (0 : ℝ) ≤ max a |φ 0| := le_trans (abs_nonneg _) (le_max_right _ _)
  refine ContinuousLinearMap.opNorm_le_bound _ hM0 (fun x => ?_)
  have h := hs.hasSum_funCalc_sub_starProjection hb x
  set Pv := (LinearMap.ker K.toLinearMap).starProjection x with hPvdef
  set S := hs.funCalc φ hb x - (RCLike.ofReal (φ 0) : 𝕜) • Pv with hSdef
  have hSmem : S ∈ (LinearMap.ker K.toLinearMap)ᗮ :=
    hs.funCalc_sub_smul_starProjection_mem_orthogonal hb x
  have hPmem : Pv ∈ LinearMap.ker K.toLinearMap :=
    (LinearMap.ker K.toLinearMap).starProjection_apply_mem x
  have horth : (inner 𝕜 S ((RCLike.ofReal (φ 0) : 𝕜) • Pv) : 𝕜) = 0 := by
    rw [inner_smul_right, ← inner_conj_symm, (Submodule.mem_orthogonal _ _).mp hSmem Pv hPmem]
    simp
  have hsplit : hs.funCalc φ hb x = S + (RCLike.ofReal (φ 0) : 𝕜) • Pv := by rw [hSdef]; abel
  have hpyth : ‖hs.funCalc φ hb x‖ ^ 2 = ‖S‖ ^ 2 + ‖(RCLike.ofReal (φ 0) : 𝕜) • Pv‖ ^ 2 := by
    rw [hsplit, sq, sq, sq]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜) _ _ horth
  have hnormS := hs.orthonormal_left.norm_sq_eq_tsum_norm_sq h
  have hnormP := hs.orthonormal_left.norm_sq_eq_tsum_norm_sq (hs.hasSum_sub_starProjection x)
  have hSle : ‖S‖ ^ 2 ≤ max a |φ 0| ^ 2 * ‖x - Pv‖ ^ 2 := by
    rw [hnormS, hnormP]
    calc ∑' i, ‖(RCLike.ofReal (φ (σ i ^ 2)) : 𝕜) * inner 𝕜 (v i) x‖ ^ 2
        ≤ ∑' i, max a |φ 0| ^ 2 * ‖(inner 𝕜 (v i) x : 𝕜)‖ ^ 2 := by
          refine Summable.tsum_le_tsum (fun i => ?_) ?_
            ((hs.orthonormal_left.inner_products_summable (x := x)).mul_left _)
          · rw [norm_mul, mul_pow, RCLike.norm_ofReal]
            have hb2 : |φ (σ i ^ 2)| ^ 2 ≤ max a |φ 0| ^ 2 := by
              nlinarith [abs_nonneg (φ (σ i ^ 2)), ha i, le_max_left a |φ 0|]
            exact mul_le_mul_of_nonneg_right hb2 (by positivity)
          · rw [← hs.orthonormal_left.summable_iff_norm_sq_summable]
            exact h.summable
      _ = max a |φ 0| ^ 2 * ∑' i, ‖(inner 𝕜 (v i) x : 𝕜)‖ ^ 2 :=
          (hs.orthonormal_left.inner_products_summable (x := x)).tsum_mul_left _
  have hkerle : ‖(RCLike.ofReal (φ 0) : 𝕜) • Pv‖ ^ 2 ≤ max a |φ 0| ^ 2 * ‖Pv‖ ^ 2 := by
    rw [norm_smul, RCLike.norm_ofReal, mul_pow]
    have hb2 : |φ 0| ^ 2 ≤ max a |φ 0| ^ 2 := by
      nlinarith [abs_nonneg (φ 0), le_max_right a |φ 0|]
    exact mul_le_mul_of_nonneg_right hb2 (by positivity)
  have hsum2 : ‖Pv‖ ^ 2 + ‖x - Pv‖ ^ 2 = ‖x‖ ^ 2 := by
    have := (LinearMap.ker K.toLinearMap).norm_sq_eq_add_norm_sq_starProjection x
    rw [Submodule.starProjection_orthogonal_val] at this
    linarith
  have hfinal : ‖hs.funCalc φ hb x‖ ^ 2 ≤ (max a |φ 0| * ‖x‖) ^ 2 := by
    rw [hpyth, mul_pow, ← hsum2]
    nlinarith [hSle, hkerle]
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hfinal

end _lem_fun_calc_bounded
