/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_fun_calc
import AutoIp._part_1_funcanal._ch_08_svd._lem_svd_companion
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound

section _lem_fun_calc_basic

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- `𝟏(K*K) = Id_X`. -/
public theorem IsSingularSystem.funCalc_one (hs : IsSingularSystem K σ v u)
    (h1 : ∃ C, ∀ i, |(fun _ : ℝ => (1 : ℝ)) (σ i ^ 2)| ≤ C) :
    hs.funCalc (fun _ => 1) h1 = ContinuousLinearMap.id 𝕜 E := by
  ext x
  have h := hs.hasSum_funCalc_sub_starProjection (φ := fun _ => 1) h1 x
  simp only [RCLike.ofReal_one, one_mul, one_smul] at h
  have heq := h.unique (hs.hasSum_sub_starProjection x)
  simp only [ContinuousLinearMap.id_apply]
  have : hs.funCalc (fun _ => 1) h1 x - (LinearMap.ker K.toLinearMap).starProjection x
      = x - (LinearMap.ker K.toLinearMap).starProjection x := heq
  exact sub_left_injective this

/-- `id(K*K) = K*K`. -/
public theorem IsSingularSystem.funCalc_id (hs : IsSingularSystem K σ v u)
    (hid : ∃ C, ∀ i, |id (σ i ^ 2)| ≤ C) :
    hs.funCalc id hid = K.adjoint ∘L K := by
  ext x
  have h := hs.hasSum_funCalc_sub_starProjection hid x
  simp only [id_eq, RCLike.ofReal_zero, zero_smul, sub_zero] at h
  exact h.unique (hs.hasSum_adjoint_comp_self x)

/-- `√(K*K) ∘ √(K*K) = K*K`. -/
public theorem IsSingularSystem.funCalc_sqrt_comp_funCalc_sqrt (hs : IsSingularSystem K σ v u)
    (hb : ∃ C, ∀ i, |Real.sqrt (σ i ^ 2)| ≤ C) :
    hs.funCalc Real.sqrt hb ∘L hs.funCalc Real.sqrt hb = K.adjoint ∘L K := by
  have hbid : ∃ C, ∀ i, |id (σ i ^ 2)| ≤ C :=
    ⟨‖K‖ ^ 2, fun i => by
      rw [id_eq, abs_of_nonneg (by positivity)]; exact (hs.sq_mem_Icc i).2⟩
  rw [← hs.funCalc_mul' hb hb, ← hs.funCalc_id hbid]
  refine hs.funCalc_congr' _ _ (by simp) fun i => ?_
  simp only [Pi.mul_apply, id_eq]
  rw [Real.sqrt_sq (hs.pos i).le]
  ring

end _lem_fun_calc_basic
