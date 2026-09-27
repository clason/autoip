/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_16_tikhonov._def_value_functions.Spec
import all AutoIp._part_2_reg._ch_16_tikhonov._def_value_functions.Spec

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- The residual value in closed form. -/
public theorem tikhonovResidualValue_def (hs : IsSingularSystem K σ v u) (z : F)
    (α : Set.Ioi (0 : ℝ)) :
    tikhonovResidualValue hs z α
      = ((1 : ℝ) / 2) *
        ‖K (spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) α z)
          - z‖ ^ 2 := by
  unfold tikhonovResidualValue
  rfl

/-- The solution-norm value in closed form. -/
public theorem tikhonovNormValue_def (hs : IsSingularSystem K σ v u) (z : F)
    (α : Set.Ioi (0 : ℝ)) :
    tikhonovNormValue hs z α
      = ((1 : ℝ) / 2) *
        ‖spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) α z‖ ^ 2 := by
  unfold tikhonovNormValue
  rfl

end AutoIp
