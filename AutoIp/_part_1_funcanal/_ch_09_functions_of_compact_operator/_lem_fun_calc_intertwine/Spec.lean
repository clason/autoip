/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_fun_calc_y

section _lem_fun_calc_intertwine

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- `φ(K*K) K* = K* φ(KK*)`. The hypothesis asks `φ` to be bounded only at the points `σₙ²`,
not on all of `[0, κ]`. -/
public theorem IsSingularSystem.funCalc_comp_adjoint (hs : IsSingularSystem K σ v u) {φ : ℝ → ℝ}
    (hb : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C) :
    hs.funCalc φ hb ∘L K.adjoint =
      K.adjoint ∘L hs.funCalcRight φ hb := by
  ext y
  simp only [ContinuousLinearMap.comp_apply]
  -- left-hand side: `K* y` lies in `(ker K)ᗮ`, so the kernel term drops
  have h := hs.hasSum_funCalc_sub_starProjection hb (ContinuousLinearMap.adjoint K y)
  have hKy : ContinuousLinearMap.adjoint K y ∈ (LinearMap.ker K.toLinearMap)ᗮ := by
    rw [ContinuousLinearMap.orthogonal_ker]
    exact Submodule.le_topologicalClosure _ ⟨y, rfl⟩
  rw [(Submodule.starProjection_apply_eq_zero_iff _).mpr hKy, smul_zero, sub_zero] at h
  have hfun : (fun i => ((RCLike.ofReal (φ (σ i ^ 2)) : 𝕜)
        * inner 𝕜 (v i) (ContinuousLinearMap.adjoint K y)) • v i)
      = fun i => ((RCLike.ofReal (φ (σ i ^ 2)) : 𝕜) * inner 𝕜 (u i) y
          * (RCLike.ofReal (σ i) : 𝕜)) • v i := by
    funext i
    have hin : (inner 𝕜 (v i) (ContinuousLinearMap.adjoint K y) : 𝕜)
        = (RCLike.ofReal (σ i) : 𝕜) * inner 𝕜 (u i) y := by
      rw [ContinuousLinearMap.adjoint_inner_right, hs.map_left i, inner_smul_left,
        RCLike.conj_ofReal]
    rw [hin]
    ring_nf
  rw [hfun] at h
  -- right-hand side: `K*` annihilates the `Y`-side kernel term
  have h2 := hs.hasSum_funCalcRight_sub_starProjection hb y
  have hPmem : (LinearMap.ker (ContinuousLinearMap.adjoint K).toLinearMap).starProjection y
      ∈ LinearMap.ker (ContinuousLinearMap.adjoint K).toLinearMap :=
    (LinearMap.ker (ContinuousLinearMap.adjoint K).toLinearMap).starProjection_apply_mem y
  have hker : ContinuousLinearMap.adjoint K
      ((LinearMap.ker (ContinuousLinearMap.adjoint K).toLinearMap).starProjection y) = 0 := hPmem
  have h3 := h2.mapL (ContinuousLinearMap.adjoint K)
  simp only [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_smul, hs.map_right,
    smul_smul, hker] at h3
  rw [smul_zero, sub_zero] at h3
  exact h.unique h3

/-- `K φ(K*K) = φ(KK*) K`. The hypothesis asks `φ` to be bounded only at the points `σₙ²`,
not on all of `[0, κ]`. -/
public theorem IsSingularSystem.comp_funCalc (hs : IsSingularSystem K σ v u) {φ : ℝ → ℝ}
    (hb : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C) :
    K ∘L hs.funCalc φ hb = hs.funCalcRight φ hb ∘L K := by
  have hL : IsSelfAdjoint (hs.funCalc φ hb) := hs.isSelfAdjoint_funCalc hb
  have hR : IsSelfAdjoint (hs.funCalcRight φ hb) := hs.isSelfAdjoint_funCalcRight hb
  have h := congrArg ContinuousLinearMap.adjoint (hs.funCalc_comp_adjoint hb)
  rwa [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, hL.adjoint_eq, hR.adjoint_eq] at h

end _lem_fun_calc_intertwine
