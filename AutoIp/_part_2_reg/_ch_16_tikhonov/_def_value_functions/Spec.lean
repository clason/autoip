/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_standard_filters

section _def_value_functions

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- The value function `f(α) = ½‖K x^δ_α - y^δ‖²`, for the datum `y^δ = z`. -/
public noncomputable def tikhonovResidualValue (hs : IsSingularSystem K σ v u) (z : F)
    (α : Set.Ioi (0 : ℝ)) : ℝ :=
  ((1 : ℝ) / 2) *
    ‖K (spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) α z) - z‖ ^ 2

/-- The value function `g(α) = ½‖x^δ_α‖²`, for the datum `y^δ = z`. -/
public noncomputable def tikhonovNormValue (hs : IsSingularSystem K σ v u) (z : F)
    (α : Set.Ioi (0 : ℝ)) : ℝ :=
  ((1 : ℝ) / 2) *
    ‖spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) α z‖ ^ 2

/-- The value function `j(α) = J_α(x^δ_α) = f(α) + α g(α)`, for the datum `y^δ = z`.

It is defined as `f(α) + α g(α)`. -/
public noncomputable def tikhonovValue (hs : IsSingularSystem K σ v u) (z : F)
    (α : Set.Ioi (0 : ℝ)) : ℝ :=
  tikhonovResidualValue hs z α + (α : ℝ) * tikhonovNormValue hs z α

/-- The equality `j(α) = f(α) + α g(α)` of the node.

It holds for every `K`, `K = 0` included. -/
public theorem tikhonovValue_def (hs : IsSingularSystem K σ v u) (z : F)
    (α : Set.Ioi (0 : ℝ)) :
    tikhonovValue hs z α
      = tikhonovResidualValue hs z α + (α : ℝ) * tikhonovNormValue hs z α := by
  unfold tikhonovValue
  rfl

end AutoIp

end _def_value_functions
