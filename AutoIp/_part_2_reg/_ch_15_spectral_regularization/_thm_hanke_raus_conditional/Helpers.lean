/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_frac_power
public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
import AutoIp.Auxiliary.Rpow

namespace AutoIp

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- If `y = K x†` with `x† = K† y = |K|^ν w` and `‖w‖ ≤ ρ`, then
`‖y‖ ≤ (‖K‖²)^{(ν+1)/2} ρ`. -/
public theorem norm_le_rpow_of_absRpow_eq (hs : IsSingularSystem K σ v u) (hK : K ≠ 0)
    {ν : ℝ} (hν : 0 < ν) {y : F} (hy : y ∈ mpDomain K)
    (hKxd : K (moorePenrose K ⟨y, hy⟩) = y)
    {w : E} {ρ : ℝ} (hw : hs.absRpow ν hν.le w = moorePenrose K ⟨y, hy⟩) (hwn : ‖w‖ ≤ ρ) :
    ‖y‖ ≤ (‖K‖ ^ 2) ^ ((ν + 1) / 2) * ρ := by
  have h1 : ‖hs.absRpow ν hν.le w‖ ≤ (‖K‖ ^ 2) ^ (ν / 2) * ρ :=
    le_trans ((hs.absRpow ν hν.le).le_opNorm w)
      (mul_le_mul (hs.norm_absRpow_le hν) hwn (norm_nonneg _)
        (Real.rpow_nonneg (sq_nonneg _) _))
  have h2 : ‖y‖ ≤ ‖K‖ * ‖hs.absRpow ν hν.le w‖ := by
    rw [hw]
    calc ‖y‖ = ‖K (moorePenrose K ⟨y, hy⟩)‖ := by rw [hKxd]
      _ ≤ ‖K‖ * ‖moorePenrose K ⟨y, hy⟩‖ := K.le_opNorm _
  calc ‖y‖ ≤ ‖K‖ * ‖hs.absRpow ν hν.le w‖ := h2
    _ ≤ ‖K‖ * ((‖K‖ ^ 2) ^ (ν / 2) * ρ) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = (‖K‖ ^ 2) ^ ((ν + 1) / 2) * ρ := by
        rw [← mul_assoc, mul_rpow_sq_div_two (norm_pos_iff.mpr hK)]

end AutoIp
