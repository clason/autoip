/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_well_posed
import Mathlib.Analysis.Normed.Operator.Banach

section _prop_well_posed_banach

namespace AutoIp

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If `X`, `Y` are Banach spaces and `T ∈ L(X,Y)` satisfies (i) and (ii) of Hadamard
well-posedness, then `T` is bijective, `T⁻¹ ∈ L(Y,X)`, and (iii) holds. The inverse `T⁻¹ ∈ L(Y,X)`
is stated as a bounded two-sided inverse `S`, and (iii) as the well-posedness of `T`. -/
public theorem isWellPosed_of_bijective [CompleteSpace E] [CompleteSpace F] (T : E →L[𝕜] F)
    (hsurj : ∀ y : F, ∃ x : E, T x = y) (hinj : ∀ x x' : E, T x = T x' → x = x') :
    Function.Bijective T ∧ (∃ S : F →L[𝕜] E, (∀ y, T (S y) = y) ∧ ∀ x, S (T x) = x) ∧
      IsWellPosed (T : E →ₗ[𝕜] F) := by
  have hbij : Function.Bijective T := ⟨fun x x' h => hinj x x' h, hsurj⟩
  have hker : LinearMap.ker (T : E →ₗ[𝕜] F) = ⊥ := LinearMap.ker_eq_bot.2 hbij.1
  have hran : LinearMap.range (T : E →ₗ[𝕜] F) = ⊤ := LinearMap.range_eq_top.2 hbij.2
  let e : E ≃L[𝕜] F := ContinuousLinearEquiv.ofBijective T hker hran
  refine ⟨hbij, ⟨(e.symm : F →L[𝕜] E), ?_, ?_⟩, hsurj, hinj, ?_⟩
  · exact ContinuousLinearEquiv.ofBijective_apply_symm_apply T hker hran
  · exact ContinuousLinearEquiv.ofBijective_symm_apply_apply T hker hran
  · intro x w hw
    have hw' : Filter.Tendsto (fun n => T (w n)) Filter.atTop (nhds (T x)) := by
      simp only [ContinuousLinearMap.coe_coe] at hw
      exact hw
    have := (e.symm.continuous.tendsto (T x)).comp hw'
    simpa [Function.comp_def, e,
      ContinuousLinearEquiv.ofBijective_symm_apply_apply T hker hran] using this

end AutoIp

end _prop_well_posed_banach
