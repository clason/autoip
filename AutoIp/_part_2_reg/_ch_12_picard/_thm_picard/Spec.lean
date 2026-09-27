/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_08_svd._def_singular_system
public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
import AutoIp._part_1_funcanal._ch_04_orthonormal_series._lem_riesz_fischer
import AutoIp._part_2_reg._ch_11_moore_penrose._cor_normal_equation
import AutoIp._part_2_reg._ch_12_picard._thm_picard.Helpers

section _thm_picard

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- For `y` in the closure of `Ran(K)`: `y ∈ Ran(K)` if and only if
`∑ₙ σₙ⁻² |⟨uₙ, y⟩|² < ∞`. The singular system need not be ordered, and `K` need not be
compact. -/
public theorem mem_range_iff_picard (hs : IsSingularSystem K σ v u) {y : F}
    (hy : y ∈ K.toLinearMap.range.topologicalClosure) :
    y ∈ K.toLinearMap.range ↔
      Summable (fun i => (σ i)⁻¹ ^ 2 * ‖(inner 𝕜 (u i) y : 𝕜)‖ ^ 2) := by
  constructor
  · rintro ⟨x, rfl⟩
    have hbess := hs.orthonormal_left.inner_products_summable (x := x)
    refine hbess.congr fun i => ?_
    have hσ := hs.pos i
    have hco : (inner 𝕜 (u i) (K x) : 𝕜) = (RCLike.ofReal (σ i) : 𝕜) * inner 𝕜 (v i) x := by
      rw [← ContinuousLinearMap.adjoint_inner_left, hs.map_right, inner_smul_left,
        RCLike.conj_ofReal]
    simp only [ContinuousLinearMap.coe_coe]
    rw [hco, norm_mul, RCLike.norm_ofReal, abs_of_pos hσ, mul_pow, ← mul_assoc, inv_pow]
    rw [inv_mul_cancel₀ (by positivity), one_mul]
  · intro hsum
    obtain ⟨x, -, -, hKx⟩ := exists_hasSum_of_picard hs hy hsum
    exact ⟨x, by simpa using hKx⟩

/-- For `y ∈ Ran(K)`: `K† y = ∑ₙ σₙ⁻¹ ⟨uₙ, y⟩ vₙ`. The singular system need not be ordered, and
`K` need not be compact. -/
public theorem hasSum_moorePenrose_of_mem_range (hs : IsSingularSystem K σ v u) {y : F}
    (hy : y ∈ K.toLinearMap.range) :
    HasSum (fun i => ((((σ i)⁻¹ : ℝ) : 𝕜) * inner 𝕜 (u i) y) • v i)
      (moorePenrose K ⟨y, (Submodule.mem_sup_left hy)⟩) := by
  have hyc : y ∈ (LinearMap.range K.toLinearMap).topologicalClosure :=
    Submodule.le_topologicalClosure _ hy
  have hsum := (mem_range_iff_picard hs hyc).1 hy
  obtain ⟨x, hx, hxk, hKx⟩ := exists_hasSum_of_picard hs hyc hsum
  have hls : IsLeastSquares K y x := by
    intro z
    rw [hKx, sub_self, norm_zero]
    exact norm_nonneg _
  have hxeq := eq_moorePenrose_of_isLeastSquares hls hxk
  rw [hxeq] at hx
  exact hx

end AutoIp

end _thm_picard
