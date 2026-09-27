/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_12_picard._def_source_set
import AutoIp._part_2_reg._ch_12_picard._cor_picard_domain
public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose

section _lem_source_picard

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- For `ν > 0` and `y ∈ Dom(K†)`: `K† y ∈ X_ν` if and only if
`∑ₙ σₙ^{-2-2ν} |⟨uₙ, y⟩|² < ∞`. -/
public theorem moorePenrose_mem_sourceSetAll_iff (hs : IsSingularSystem K σ v u) {ν : ℝ}
    (hν : 0 < ν) {y : F}
    (hy : y ∈ mpDomain K) :
    moorePenrose K ⟨y, hy⟩ ∈ sourceSetAll hs ν hν ↔
      Summable (fun i => (σ i) ^ (-2 - 2 * ν) * ‖(inner 𝕜 (u i) y : 𝕜)‖ ^ 2) := by
  have habs : ∀ w : E, HasSum (fun i => ((RCLike.ofReal (σ i ^ ν) : 𝕜) * inner 𝕜 (v i) w) • v i)
      (hs.absRpow ν hν.le w) := fun w => hs.hasSum_absRpow hν w
  have hx := hasSum_moorePenrose hs hy
  have hcx : ∀ m, (inner 𝕜 (v m) (moorePenrose K ⟨y, hy⟩) : 𝕜)
      = (RCLike.ofReal (σ m)⁻¹ : 𝕜) * inner 𝕜 (u m) y :=
    fun m => hs.orthonormal_left.inner_right_of_hasSum hx m
  rw [mem_sourceSetAll_iff]
  constructor
  · rintro ⟨w, hw⟩
    have hcw : ∀ m, (RCLike.ofReal (σ m ^ ν) : 𝕜) * inner 𝕜 (v m) w
        = (RCLike.ofReal (σ m)⁻¹ : 𝕜) * inner 𝕜 (u m) y := by
      intro m
      have h := hs.orthonormal_left.inner_right_of_hasSum (habs w) m
      rw [hw, hcx m] at h
      exact h.symm
    have hnorm : ∀ m, σ m ^ (-2 - 2 * ν) * ‖(inner 𝕜 (u m) y : 𝕜)‖ ^ 2
        = ‖(inner 𝕜 (v m) w : 𝕜)‖ ^ 2 := by
      intro m
      have hs0 : 0 < σ m := hs.pos m
      have hs0' : σ m ≠ 0 := hs0.ne'
      have h := congrArg norm (hcw m)
      rw [norm_mul, norm_mul, RCLike.norm_ofReal, RCLike.norm_ofReal,
        abs_of_pos (Real.rpow_pos_of_pos hs0 ν), abs_of_pos (inv_pos.mpr hs0)] at h
      have hb2 : ‖(inner 𝕜 (u m) y : 𝕜)‖ = σ m * (σ m ^ ν * ‖(inner 𝕜 (v m) w : 𝕜)‖) := by
        rw [h]
        field_simp
      have hprod : σ m ^ (-2 - 2 * ν) * ((σ m) ^ (2 : ℕ) * (σ m ^ ν) ^ (2 : ℕ)) = 1 := by
        rw [← Real.rpow_natCast (σ m) 2, ← Real.rpow_natCast (σ m ^ ν) 2,
          ← Real.rpow_mul hs0.le, ← Real.rpow_add hs0, ← Real.rpow_add hs0,
          show (-2 - 2 * ν + ((2 : ℕ) + ν * (2 : ℕ)) : ℝ) = 0 by push_cast; ring,
          Real.rpow_zero]
      calc σ m ^ (-2 - 2 * ν) * ‖(inner 𝕜 (u m) y : 𝕜)‖ ^ 2
          = σ m ^ (-2 - 2 * ν) * ((σ m) ^ (2 : ℕ) * (σ m ^ ν) ^ (2 : ℕ))
              * ‖(inner 𝕜 (v m) w : 𝕜)‖ ^ 2 := by rw [hb2]; ring
        _ = ‖(inner 𝕜 (v m) w : 𝕜)‖ ^ 2 := by rw [hprod, one_mul]
    exact (hs.orthonormal_left.inner_products_summable (x := w)).congr fun i => (hnorm i).symm
  · intro hsum
    have hc2 : ∀ i, ‖((RCLike.ofReal (σ i ^ (-1 - ν)) : 𝕜) * inner 𝕜 (u i) y)‖ ^ 2
        = σ i ^ (-2 - 2 * ν) * ‖(inner 𝕜 (u i) y : 𝕜)‖ ^ 2 := by
      intro i
      have hs0 : 0 < σ i := hs.pos i
      have hsq : (σ i ^ (-1 - ν)) ^ (2 : ℕ) = σ i ^ (-2 - 2 * ν) := by
        rw [← Real.rpow_natCast (σ i ^ (-1 - ν)) 2, ← Real.rpow_mul hs0.le]
        congr 1
        push_cast
        ring
      rw [norm_mul, mul_pow, RCLike.norm_ofReal,
        abs_of_pos (Real.rpow_pos_of_pos hs0 _), hsq]
    have hsummable : Summable
        (fun i => ((RCLike.ofReal (σ i ^ (-1 - ν)) : 𝕜) * inner 𝕜 (u i) y) • v i) := by
      rw [hs.orthonormal_left.summable_iff_norm_sq_summable]
      exact hsum.congr fun i => (hc2 i).symm
    obtain ⟨w, hw⟩ := hsummable
    refine ⟨w, ?_⟩
    have hcw : ∀ m, (inner 𝕜 (v m) w : 𝕜)
        = (RCLike.ofReal (σ m ^ (-1 - ν)) : 𝕜) * inner 𝕜 (u m) y :=
      fun m => hs.orthonormal_left.inner_right_of_hasSum hw m
    have h1 := habs w
    have hfun : (fun i => ((RCLike.ofReal (σ i ^ ν) : 𝕜) * inner 𝕜 (v i) w) • v i)
        = fun i => ((RCLike.ofReal (σ i)⁻¹ : 𝕜) * inner 𝕜 (u i) y) • v i := by
      funext i
      have hs0 : 0 < σ i := hs.pos i
      have hexp : ν + (-1 - ν) = -1 := by ring
      rw [hcw i, ← mul_assoc, ← RCLike.ofReal_mul, ← Real.rpow_add hs0, hexp,
        Real.rpow_neg_one]
    rw [hfun] at h1
    exact h1.unique hx

end AutoIp

end _lem_source_picard
