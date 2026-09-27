/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_08_svd._lem_svd_companion
public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_fun_calc
import AutoIp._part_1_funcanal._ch_03_hilbert_spaces._prop_adjoint_props
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_basic
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_bounded
public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_hom

section _def_fun_calc_y

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- The operator `ψ(KK*) ∈ ℒ(Y,Y)` for a real-valued `ψ`, given by
`ψ(KK*) y = ∑ₙ ψ(σₙ²) ⟨uₙ, y⟩ uₙ + ψ(0) P_{𝒩(K*)} y`.

The hypothesis asks `ψ` to be bounded only at the points `σₙ²`, not on all of `[0, κ]`, and `ψ`
is a function on `ℝ`. -/
public noncomputable def IsSingularSystem.funCalcRight (hs : IsSingularSystem K σ v u)
    (ψ : ℝ → ℝ) (hψ : ∃ C, ∀ i, |ψ (σ i ^ 2)| ≤ C) : F →L[𝕜] F :=
  hs.adjoint.funCalc ψ hψ

/-- The formula defining `ψ(KK*)`: for every `y ∈ Y` the series `∑ₙ ψ(σₙ²) ⟨uₙ, y⟩ uₙ`
converges to `ψ(KK*) y - ψ(0) P_{𝒩(K*)} y`. -/
public theorem IsSingularSystem.hasSum_funCalcRight_sub_starProjection
    (hs : IsSingularSystem K σ v u) {ψ : ℝ → ℝ} (hψ : ∃ C, ∀ i, |ψ (σ i ^ 2)| ≤ C) (y : F) :
    HasSum (fun i => ((ψ (σ i ^ 2) : 𝕜) * inner 𝕜 (u i) y) • u i)
      (hs.funCalcRight ψ hψ y - (ψ 0 : 𝕜)
        • K.adjoint.toLinearMap.ker.starProjection y) :=
  hs.adjoint.hasSum_funCalc_sub_starProjection hψ y

end _def_fun_calc_y
