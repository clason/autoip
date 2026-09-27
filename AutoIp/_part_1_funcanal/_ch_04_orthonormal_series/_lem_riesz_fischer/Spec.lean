/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal
import AutoIp._part_1_funcanal._ch_04_orthonormal_series._lem_inner_through_series
import Mathlib.Analysis.InnerProductSpace.Subspace

section _lem_riesz_fischer

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*}

/-- Riesz–Fischer for orthonormal systems, the last assertion: if `∑ₙ cₙ eₙ` converges to
`x`, the coefficients of the sum are the `cₙ`, that is, `⟨eⱼ, x⟩ = cⱼ` for every `j`.

This holds without completeness of `X`. -/
public theorem Orthonormal.inner_right_of_hasSum {e : ι → E} (he : Orthonormal 𝕜 e)
    {c : ι → 𝕜} {x : E} (hx : HasSum (fun i => c i • e i) x) (j : ι) :
    inner 𝕜 (e j) x = c j := by
  classical
  have h := HasSum.inner_right (𝕜 := 𝕜) hx (e j)
  simp only [inner_smul_right, orthonormal_iff_ite.mp he, mul_ite, mul_one, mul_zero] at h
  have hfun : (fun i => if j = i then c i else 0) = fun i => if i = j then c j else 0 := by
    funext i
    by_cases hij : j = i
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  rw [hfun] at h
  exact h.unique (hasSum_ite_eq j (c j))

/-- Riesz–Fischer for orthonormal systems, the norm identity: if `∑ₙ cₙ eₙ` converges to `x`,
then `‖x‖² = ∑ₙ |cₙ|²`.

This holds without completeness of `X`. -/
public theorem Orthonormal.norm_sq_eq_tsum_norm_sq
    {e : ι → E} (he : Orthonormal 𝕜 e) {c : ι → 𝕜} {x : E}
    (hx : HasSum (fun i => c i • e i) x) :
    ‖x‖ ^ 2 = ∑' i, ‖c i‖ ^ 2 := by
  -- Push `x` through the *first* slot: the `i`-th term becomes `conj (c i) * ⟪e i, x⟫`,
  -- and `inner_right_of_hasSum` identifies `⟪e i, x⟫` with `c i`, leaving `‖c i‖ ^ 2`.
  have h := HasSum.inner_left (𝕜 := 𝕜) hx x
  have hfun : (fun i => (inner 𝕜 (c i • e i) x : 𝕜)) =
      fun i => (RCLike.ofReal (‖c i‖ ^ 2) : 𝕜) := by
    funext i
    rw [inner_smul_left, Orthonormal.inner_right_of_hasSum he hx i, RCLike.conj_mul]
    simp
  rw [hfun] at h
  have hre := h.mapL (RCLike.reCLM (K := 𝕜))
  simp only [RCLike.reCLM_apply, RCLike.ofReal_re] at hre
  rw [hre.tsum_eq, inner_self_eq_norm_sq]

/-- Riesz–Fischer for orthonormal systems: for scalars `cₙ`, the series `∑ₙ cₙ eₙ` converges
if and only if `∑ₙ |cₙ|² < ∞`. -/
public theorem Orthonormal.summable_iff_norm_sq_summable [CompleteSpace E]
    {e : ι → E} (he : Orthonormal 𝕜 e) (c : ι → 𝕜) :
    Summable (fun i => c i • e i) ↔ Summable (fun i => ‖c i‖ ^ 2) := by
  -- The family form is stated through `LinearIsometry.toSpanSingleton`; `simpa` applies its
  -- `@[simp]` apply-equation.
  simpa using he.orthogonalFamily.summable_iff_norm_sq_summable c

end _lem_riesz_fischer
