/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_20_iterated_tikhonov._def_iterated_tikhonov
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init

section _thm_iterated_tikhonov_qualification

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- For `0 < ν ≤ 2m`, `ω_ν(α) ≤ 1 · α^{ν/2}` for all `α > 0`, where
`ω_ν(α) = sup_{λ ∈ (0,κ]} λ^{ν/2} |1 - λ φ^(m)_α(λ)|`. This is the bound of (Q_ν) with
`C_ν = 1`, not (Q_ν) in its structure form, which adds the regularizing-filter
property.

It holds for every `K`, `K = 0` included. -/
public
theorem iSup_rpow_mul_abs_one_sub_mul_iteratedTikhonovFilter_le (K : E →L[𝕜] F) {m : ℕ} {ν : ℝ}
    (hν : 0 < ν) (hν2 : ν ≤ 2 * m) :
    ∀ α : Set.Ioi (0 : ℝ),
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
        lam ^ (ν / 2) * |1 - lam * iteratedTikhonovFilter m α lam|) ≤
          1 * (α : ℝ) ^ (ν / 2) := by
  intro α
  have hα : (0 : ℝ) < (α : ℝ) := α.2
  have hc : (0 : ℝ) ≤ 1 * (α : ℝ) ^ (ν / 2) := by
    rw [one_mul]; exact Real.rpow_nonneg hα.le _
  refine Real.iSup_le (fun lam => Real.iSup_le (fun h => ?_) hc) hc
  have hlam : (0 : ℝ) < lam := h.1
  have hsum : (0 : ℝ) < (α : ℝ) + lam := by linarith
  have hres := one_sub_mul_iteratedTikhonovFilter (m := m) (α := α) hlam
  have hu0 : (0 : ℝ) ≤ (α : ℝ) / ((α : ℝ) + lam) := by positivity
  rw [hres, one_mul, abs_of_nonneg (pow_nonneg hu0 m)]
  -- Split `α^m` and `(α+λ)^m` at the exponent `ν/2` and compare the factors.
  have hp0 : (0 : ℝ) < ν / 2 := by linarith
  have hpm : ν / 2 ≤ (m : ℝ) := by linarith
  have hpow : ((α : ℝ) / ((α : ℝ) + lam)) ^ m =
      (α : ℝ) ^ (m : ℝ) / ((α : ℝ) + lam) ^ (m : ℝ) := by
    rw [← Real.rpow_natCast ((α : ℝ) / ((α : ℝ) + lam)) m, Real.div_rpow hα.le hsum.le]
  have hA : (0 : ℝ) < ((α : ℝ) + lam) ^ (m : ℝ) := Real.rpow_pos_of_pos hsum _
  rw [hpow, ← mul_div_assoc, div_le_iff₀ hA]
  have e1 : (α : ℝ) ^ (m : ℝ) = (α : ℝ) ^ (ν / 2) * (α : ℝ) ^ ((m : ℝ) - ν / 2) := by
    rw [← Real.rpow_add hα]; congr 1; ring
  have e2 : ((α : ℝ) + lam) ^ (m : ℝ) =
      ((α : ℝ) + lam) ^ (ν / 2) * ((α : ℝ) + lam) ^ ((m : ℝ) - ν / 2) := by
    rw [← Real.rpow_add hsum]; congr 1; ring
  have b1 : lam ^ (ν / 2) ≤ ((α : ℝ) + lam) ^ (ν / 2) :=
    Real.rpow_le_rpow hlam.le (by linarith) hp0.le
  have b2 : (α : ℝ) ^ ((m : ℝ) - ν / 2) ≤ ((α : ℝ) + lam) ^ ((m : ℝ) - ν / 2) :=
    Real.rpow_le_rpow hα.le (by linarith) (by linarith)
  rw [e1, e2]
  calc lam ^ (ν / 2) * ((α : ℝ) ^ (ν / 2) * (α : ℝ) ^ ((m : ℝ) - ν / 2))
      = (lam ^ (ν / 2) * (α : ℝ) ^ ((m : ℝ) - ν / 2)) * (α : ℝ) ^ (ν / 2) := by ring
    _ ≤ (((α : ℝ) + lam) ^ (ν / 2) * ((α : ℝ) + lam) ^ ((m : ℝ) - ν / 2)) *
          (α : ℝ) ^ (ν / 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul b1 b2 (Real.rpow_nonneg hα.le _) (Real.rpow_nonneg hsum.le _))
          (Real.rpow_nonneg hα.le _)
    _ = (α : ℝ) ^ (ν / 2) *
          (((α : ℝ) + lam) ^ (ν / 2) * ((α : ℝ) + lam) ^ ((m : ℝ) - ν / 2)) := by ring

end AutoIp

end _thm_iterated_tikhonov_qualification
