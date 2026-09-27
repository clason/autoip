/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_17_landweber._def_landweber
public import Mathlib.Analysis.InnerProductSpace.Adjoint

section _lem_landweber_closed_form

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F}

/-- Closed form of the iterates: `xₘ = ω ∑_{n=0}^{m-1} (Id - ω K*K)ⁿ K* y` for all `m ∈ ℕ`.

It holds for every `ω` and every bounded `K`. -/
public theorem landweber_eq_sum (K : E →L[𝕜] F) (ω : ℝ) (y : F) (m : ℕ) :
    landweber K ω y m =
      (ω : 𝕜) •
        ∑ n ∈ Finset.range m,
          ((ContinuousLinearMap.id 𝕜 E -
              (ω : 𝕜) • (K.adjoint ∘L K)) ^ n)
            (K.adjoint y) := by
  set T : E →L[𝕜] E := ContinuousLinearMap.id 𝕜 E -
      (RCLike.ofReal ω : 𝕜) • (ContinuousLinearMap.adjoint K ∘L K) with hTdef
  induction m with
  | zero => simp [landweber_zero]
  | succ m ih =>
    have hstep : landweber K ω y (m + 1) =
        T (landweber K ω y m) + (RCLike.ofReal ω : 𝕜) • ContinuousLinearMap.adjoint K y := by
      rw [landweber_succ]
      simp only [hTdef, sub_apply, ContinuousLinearMap.id_apply,
        smul_apply, ContinuousLinearMap.coe_comp,
        Function.comp_apply, map_sub, smul_sub]
      abel
    rw [hstep, ih, map_smul, ← smul_add]
    refine congrArg _ ?_
    rw [map_sum, Finset.sum_range_succ']
    congr 1
    exact Finset.sum_congr rfl fun n _ => by rw [pow_succ', mul_apply_eq_comp]

end AutoIp

end _lem_landweber_closed_form
