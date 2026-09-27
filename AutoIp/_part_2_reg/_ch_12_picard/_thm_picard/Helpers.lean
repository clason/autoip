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

section

open scoped InnerProductSpace
namespace AutoIp

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- For `y` in the closure of `Ran(K)` with `∑ₙ σₙ⁻² |⟨uₙ, y⟩|² < ∞`, the series
`∑ₙ σₙ⁻¹ ⟨uₙ, y⟩ vₙ` converges to some `x ∈ Ker(K)ᗮ` with `K x = y`. -/
public theorem exists_hasSum_of_picard (hs : IsSingularSystem K σ v u) {y : F}
    (hy : y ∈ K.toLinearMap.range.topologicalClosure)
    (hsum : Summable (fun i => (σ i)⁻¹ ^ 2 * ‖(inner 𝕜 (u i) y : 𝕜)‖ ^ 2)) :
    ∃ x : E, HasSum (fun i => ((((σ i)⁻¹ : ℝ) : 𝕜) * inner 𝕜 (u i) y) • v i) x ∧
      x ∈ K.toLinearMap.kerᗮ ∧ K x = y := by
  have hvU : ∀ i, v i ∈ (LinearMap.ker K.toLinearMap)ᗮ := fun i => by
    rw [← hs.span_left]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)
  have hcsq : ∀ i, ‖((RCLike.ofReal (σ i)⁻¹ : 𝕜) * inner 𝕜 (u i) y)‖ ^ 2
      = (σ i)⁻¹ ^ 2 * ‖(inner 𝕜 (u i) y : 𝕜)‖ ^ 2 := by
    intro i
    rw [norm_mul, mul_pow, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr (hs.pos i).le)]
  have hsummable : Summable (fun i => ((RCLike.ofReal (σ i)⁻¹ : 𝕜) * inner 𝕜 (u i) y) • v i) := by
    rw [hs.orthonormal_left.summable_iff_norm_sq_summable]
    exact hsum.congr fun i => (hcsq i).symm
  obtain ⟨x, hx⟩ := hsummable
  have hxk : x ∈ (LinearMap.ker K.toLinearMap)ᗮ := by
    refine (Submodule.isClosed_orthogonal _).mem_of_tendsto hx ?_
    exact Filter.Eventually.of_forall fun s =>
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hvU i)
  have hKx : HasSum (fun i => (inner 𝕜 (u i) y : 𝕜) • u i) (K x) := by
    have hK := hx.mapL K
    have hfun : (fun i => K (((RCLike.ofReal (σ i)⁻¹ : 𝕜) * inner 𝕜 (u i) y) • v i))
        = fun i => (inner 𝕜 (u i) y : 𝕜) • u i := by
      funext i
      have hne : (RCLike.ofReal (σ i) : 𝕜) ≠ 0 := by
        simpa using (hs.pos i).ne'
      have h1 : ((RCLike.ofReal (σ i)⁻¹ : 𝕜) * inner 𝕜 (u i) y) * (RCLike.ofReal (σ i) : 𝕜)
          = inner 𝕜 (u i) y := by
        rw [RCLike.ofReal_inv]
        field_simp
      rw [ContinuousLinearMap.map_smul, hs.map_left, smul_smul, h1]
    rwa [hfun] at hK
  refine ⟨x, hx, hxk, ?_⟩
  have hcoef : ∀ j, (inner 𝕜 (u j) (K x) : 𝕜) = inner 𝕜 (u j) y :=
    fun j => hs.orthonormal_right.inner_right_of_hasSum hKx j
  have hperp : y - K x ∈ (Submodule.span 𝕜 (Set.range u))ᗮ :=
    (Submodule.isOrtho_span (𝕜 := 𝕜) (s := {y - K x}) (t := Set.range u)).mpr
      (by
        rintro z rfl w ⟨j, rfl⟩
        rw [← inner_conj_symm, inner_sub_right, hcoef j, sub_self, map_zero])
      |>.le (Submodule.mem_span_singleton_self _)
  have hperp' : y - K x ∈ ((LinearMap.range K.toLinearMap).topologicalClosure)ᗮ := by
    rw [← hs.span_right, Submodule.orthogonal_closure]
    exact hperp
  have hmem : y - K x ∈ (LinearMap.range K.toLinearMap).topologicalClosure :=
    Submodule.sub_mem _ hy (Submodule.le_topologicalClosure _ ⟨x, rfl⟩)
  have hzero : y - K x = 0 :=
    Submodule.disjoint_def.1 (Submodule.orthogonal_disjoint _) _ hmem hperp'
  rw [sub_eq_zero] at hzero
  exact hzero.symm

end AutoIp

end
