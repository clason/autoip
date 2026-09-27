/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_fun_calc_y
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound
import AutoIp._part_1_funcanal._ch_04_orthonormal_series._lem_riesz_fischer

section _lem_spectral_residual_form

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Spectral form of `R_α y`, item (i), with `c_n = ⟨u_n, y⟩`:
`R_α y = ∑ φ_α(σ_n²) σ_n c_n v_n` and `‖R_α y‖² = ∑ |φ_α(σ_n²)|² σ_n² |c_n|²`, both series
converging.
The family `{φ_α}` need not be a regularizing filter; the bound of each `φ_α` at the `σ_n²` is
there because the spectral regularization needs it as an argument.

It holds for every `K`, `K = 0` included. -/
public theorem hasSum_spectralReg_and_norm_sq (hs : IsSingularSystem K σ v u)
    {φ : Set.Ioi (0 : ℝ) → ℝ → ℝ} (hφ : ∀ α : Set.Ioi (0 : ℝ), ∃ C, ∀ i, |φ α (σ i ^ 2)| ≤ C)
    {α : Set.Ioi (0 : ℝ)} (y : F) :
    HasSum (fun i => (((φ α (σ i ^ 2) * σ i : ℝ) : 𝕜) * inner 𝕜 (u i) y) • v i)
        (spectralReg hs φ hφ α y) ∧
      HasSum (fun i => |φ α (σ i ^ 2)| ^ 2 * σ i ^ 2 * ‖(inner 𝕜 (u i) y : 𝕜)‖ ^ 2)
        (‖spectralReg hs φ hφ α y‖ ^ 2) := by
  have hR := hasSum_spectralReg hs φ hφ α y
  have hn := ((hs.orthonormal_left.summable_iff_norm_sq_summable _).1 hR.summable).hasSum_iff.2
    (hs.orthonormal_left.norm_sq_eq_tsum_norm_sq hR).symm
  refine ⟨hR, hn.congr_fun fun i => ?_⟩
  rw [norm_mul, RCLike.norm_ofReal, mul_pow, abs_mul, mul_pow, sq_abs, sq_abs]

/-- Spectral form of `K R_α y`, item (ii), with `c_n = ⟨u_n, y⟩`:
`K R_α y = ∑ φ_α(σ_n²) σ_n² c_n u_n` and `‖K R_α y‖² = ∑ |φ_α(σ_n²)|² σ_n⁴ |c_n|²`, both
series converging.
The family `{φ_α}` need not be a regularizing filter; the bound of each `φ_α` at the `σ_n²` is
there because the spectral regularization needs it as an argument.

It holds for every `K`, `K = 0` included. -/
public theorem hasSum_apply_spectralReg_and_norm_sq (hs : IsSingularSystem K σ v u)
    {φ : Set.Ioi (0 : ℝ) → ℝ → ℝ} (hφ : ∀ α : Set.Ioi (0 : ℝ), ∃ C, ∀ i, |φ α (σ i ^ 2)| ≤ C)
    {α : Set.Ioi (0 : ℝ)} (y : F) :
    HasSum (fun i => (((φ α (σ i ^ 2) * σ i ^ 2 : ℝ) : 𝕜) * inner 𝕜 (u i) y) • u i)
        (K (spectralReg hs φ hφ α y)) ∧
      HasSum (fun i => |φ α (σ i ^ 2)| ^ 2 * σ i ^ 4 * ‖(inner 𝕜 (u i) y : 𝕜)‖ ^ 2)
        (‖K (spectralReg hs φ hφ α y)‖ ^ 2) := by
  set c : ι → 𝕜 := fun i => (inner 𝕜 (u i) y : 𝕜) with hcdef
  have hKR : HasSum (fun i => (((φ α (σ i ^ 2) * σ i ^ 2 : ℝ) : 𝕜) * c i) • u i)
      (K (spectralReg hs φ hφ α y)) := by
    have h := (hasSum_spectralReg hs φ hφ α y).mapL K
    simp only [ContinuousLinearMap.map_smul, hs.map_left, smul_smul] at h
    refine h.congr_fun fun i => ?_
    congr 1
    push_cast
    ring
  have hn := ((hs.orthonormal_right.summable_iff_norm_sq_summable _).1 hKR.summable).hasSum_iff.2
    (hs.orthonormal_right.norm_sq_eq_tsum_norm_sq hKR).symm
  refine ⟨hKR, hn.congr_fun fun i => ?_⟩
  rw [norm_mul, RCLike.norm_ofReal, mul_pow, abs_mul, mul_pow, sq_abs, sq_abs]
  ring

/-- Spectral form of the residual, item (iii), with `c_n = ⟨u_n, y⟩`,
`r_α(λ) = 1 − λ φ_α(λ)` and `P_R` the orthogonal projection onto the closure of `Ran(K)`:
`y − K R_α y = (Id − P_R) y + ∑ r_α(σ_n²) c_n u_n`, stated as
`P_R y − K R_α y = ∑ r_α(σ_n²) c_n u_n`, and
`‖y − K R_α y‖² = ‖(Id − P_R) y‖² + ∑ |r_α(σ_n²)|² |c_n|²`, stated as the scalar series
converging to `‖P_R y − K R_α y‖²` and `‖y − K R_α y‖² = ‖(Id − P_R) y‖² + ‖P_R y − K R_α y‖²`.
The family `{φ_α}` need not be a regularizing filter; the bound of each `φ_α` at the `σ_n²` is
there because the spectral regularization needs it as an argument.

It holds for every `K`, `K = 0` included. -/
public theorem hasSum_starProjection_sub_apply_spectralReg_and_norm_sq
    (hs : IsSingularSystem K σ v u)
    {φ : Set.Ioi (0 : ℝ) → ℝ → ℝ} (hφ : ∀ α : Set.Ioi (0 : ℝ), ∃ C, ∀ i, |φ α (σ i ^ 2)| ≤ C)
    {α : Set.Ioi (0 : ℝ)} (y : F) :
    HasSum (fun i => (((1 - σ i ^ 2 * φ α (σ i ^ 2) : ℝ) : 𝕜) * inner 𝕜 (u i) y) • u i)
        (K.toLinearMap.range.topologicalClosure.starProjection y -
          K (spectralReg hs φ hφ α y)) ∧
      HasSum (fun i => |1 - σ i ^ 2 * φ α (σ i ^ 2)| ^ 2 * ‖(inner 𝕜 (u i) y : 𝕜)‖ ^ 2)
        (‖K.toLinearMap.range.topologicalClosure.starProjection y -
          K (spectralReg hs φ hφ α y)‖ ^ 2) ∧
      ‖y - K (spectralReg hs φ hφ α y)‖ ^ 2 =
        ‖y - K.toLinearMap.range.topologicalClosure.starProjection y‖ ^ 2 +
          ‖K.toLinearMap.range.topologicalClosure.starProjection y -
            K (spectralReg hs φ hφ α y)‖ ^ 2 := by
  set c : ι → 𝕜 := fun i => (inner 𝕜 (u i) y : 𝕜) with hcdef
  set P := K.toLinearMap.range.topologicalClosure.starProjection y with hP
  have hres : HasSum (fun i => (((1 - σ i ^ 2 * φ α (σ i ^ 2) : ℝ) : 𝕜) * c i) • u i)
      (P - K (spectralReg hs φ hφ α y)) := by
    refine ((hs.hasSum_starProjection_range y).sub
      (hasSum_apply_spectralReg_and_norm_sq hs hφ (α := α) y).1).congr_fun fun i => ?_
    rw [← sub_smul]
    congr 1
    rw [RCLike.ofReal_sub, RCLike.ofReal_one,
      show φ α (σ i ^ 2) * σ i ^ 2 = σ i ^ 2 * φ α (σ i ^ 2) by ring]
    ring
  have hn := ((hs.orthonormal_right.summable_iff_norm_sq_summable _).1 hres.summable).hasSum_iff.2
    (hs.orthonormal_right.norm_sq_eq_tsum_norm_sq hres).symm
  refine ⟨hres, hn.congr_fun fun i => ?_, ?_⟩
  · rw [norm_mul, RCLike.norm_ofReal, mul_pow]
  have hmem : P - K (spectralReg hs φ hφ α y) ∈ K.toLinearMap.range.topologicalClosure :=
    Submodule.sub_mem _ (Submodule.starProjection_apply_mem _ y)
      (Submodule.le_topologicalClosure _ ⟨spectralReg hs φ hφ α y, rfl⟩)
  have hz : (inner 𝕜 (y - P) (P - K (spectralReg hs φ hφ α y)) : 𝕜) = 0 := by
    have h := Submodule.sub_starProjection_mem_orthogonal
      (K := K.toLinearMap.range.topologicalClosure) y
    rw [Submodule.mem_orthogonal] at h
    rw [← inner_conj_symm, h _ hmem, map_zero]
  have hsplit : y - K (spectralReg hs φ hφ α y) = (y - P) + (P - K (spectralReg hs φ hφ α y)) := by
    abel
  rw [hsplit, norm_add_sq (𝕜 := 𝕜), hz]
  simp

/-- Spectral form of `y`, item (iv), with `c_n = ⟨u_n, y⟩` and `P_R` the orthogonal projection
onto the closure of `Ran(K)`: `‖y‖² = ‖(Id − P_R) y‖² + ∑ |c_n|²`, stated as the series
converging to `‖P_R y‖²` and `‖y‖² = ‖(Id − P_R) y‖² + ‖P_R y‖²`.

It holds for every `K`, `K = 0` included. -/
public theorem hasSum_norm_sq_inner_starProjection_range (hs : IsSingularSystem K σ v u)
    (y : F) :
    HasSum (fun i => ‖(inner 𝕜 (u i) y : 𝕜)‖ ^ 2)
        (‖K.toLinearMap.range.topologicalClosure.starProjection y‖ ^ 2) ∧
      ‖y‖ ^ 2 =
        ‖y - K.toLinearMap.range.topologicalClosure.starProjection y‖ ^ 2 +
          ‖K.toLinearMap.range.topologicalClosure.starProjection y‖ ^ 2 := by
  set P := K.toLinearMap.range.topologicalClosure.starProjection y with hP
  have hproj : HasSum (fun i => (inner 𝕜 (u i) y : 𝕜) • u i) P :=
    hs.hasSum_starProjection_range y
  refine ⟨((hs.orthonormal_right.summable_iff_norm_sq_summable _).1
    hproj.summable).hasSum_iff.2 (hs.orthonormal_right.norm_sq_eq_tsum_norm_sq hproj).symm, ?_⟩
  have hz : (inner 𝕜 (y - P) P : 𝕜) = 0 := by
    have h := Submodule.sub_starProjection_mem_orthogonal
      (K := K.toLinearMap.range.topologicalClosure) y
    rw [Submodule.mem_orthogonal] at h
    rw [← inner_conj_symm, h _ (Submodule.starProjection_apply_mem _ y), map_zero]
  have hsplit : y = (y - P) + P := by abel
  conv_lhs => rw [hsplit]
  rw [norm_add_sq (𝕜 := 𝕜), hz]
  simp

end AutoIp

end _lem_spectral_residual_form
