/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_16_tikhonov._thm_tikhonov_variational.Spec
import AutoIp._part_2_reg._ch_16_tikhonov._lem_tikhonov_normal

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- The Tikhonov functional `J_α` takes at `x_α` a value no larger than at `x_β`, for every
`β > 0`. -/
public theorem tikhonovResidualValue_add_mul_le (hs : IsSingularSystem K σ v u) (z : F)
    {a : Set.Ioi (0 : ℝ)} (b : Set.Ioi (0 : ℝ)) :
    tikhonovResidualValue hs z a + (a : ℝ) * tikhonovNormValue hs z a
      ≤ tikhonovResidualValue hs z b + (a : ℝ) * tikhonovNormValue hs z b := by
  have h := (tikhonov_isMinimizer_iff hs z (spectralReg hs tikhonovFilter
      (tikhonovFilter_exists_bound_on_spectrum hs) a z)).mpr rfl
    (spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) b z)
  simp only [tikhonovResidualValue_def, tikhonovNormValue_def]
  linarith [h]

end AutoIp
