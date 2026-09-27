/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_20_iterated_tikhonov._def_iterated_tikhonov.Spec
public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_fun_calc
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound

namespace AutoIp

open scoped InnerProductSpace

/-- The pointwise bound `|φ^(m)_α(t)| ≤ m/α` for `t ≥ 0`. -/
public theorem abs_iteratedTikhonovFilter_le {m : ℕ} {α : Set.Ioi (0 : ℝ)} {t : ℝ}
    (ht : 0 ≤ t) :
    |iteratedTikhonovFilter m α t| ≤ (m : ℝ) / (α : ℝ) := by
  have hα : (0 : ℝ) < (α : ℝ) := α.2
  rcases ht.lt_or_eq with h0 | h0
  · have hsum : (0 : ℝ) < (α : ℝ) + t := by linarith
    have hu0 : (0 : ℝ) ≤ (α : ℝ) / ((α : ℝ) + t) := by positivity
    have hu1 : (α : ℝ) / ((α : ℝ) + t) ≤ 1 := by rw [div_le_one hsum]; linarith
    have hber : 1 - (m : ℝ) * (t / ((α : ℝ) + t)) ≤ ((α : ℝ) / ((α : ℝ) + t)) ^ m := by
      have hb := one_add_mul_le_pow (a := -(t / ((α : ℝ) + t))) (by
        have : (0 : ℝ) ≤ t / ((α : ℝ) + t) := by positivity
        have h1 : t / ((α : ℝ) + t) ≤ 1 := by rw [div_le_one hsum]; linarith
        linarith) m
      have he : 1 + -(t / ((α : ℝ) + t)) = (α : ℝ) / ((α : ℝ) + t) := by field_simp; ring
      rw [he] at hb
      linarith
    have hpow : ((α : ℝ) / ((α : ℝ) + t)) ^ m ≤ 1 := pow_le_one₀ hu0 hu1
    rw [iteratedTikhonovFilter_of_ne_zero h0.ne',
      abs_of_nonneg (mul_nonneg (inv_nonneg.mpr h0.le) (by linarith))]
    have hstep : t⁻¹ * (1 - ((α : ℝ) / ((α : ℝ) + t)) ^ m) ≤
        t⁻¹ * ((m : ℝ) * (t / ((α : ℝ) + t))) :=
      mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr h0.le)
    refine hstep.trans ?_
    rw [show t⁻¹ * ((m : ℝ) * (t / ((α : ℝ) + t))) = (m : ℝ) / ((α : ℝ) + t) by field_simp]
    exact div_le_div_of_nonneg_left (by positivity) hα (by linarith)
  · rw [← h0, iteratedTikhonovFilter_zero, abs_of_nonneg (by positivity)]

/-- The iterated Tikhonov filter is bounded on the squared singular values, for every `m`,
`m = 0` included. -/
public theorem iteratedTikhonovFilter_exists_bound_on_spectrum {𝕜 : Type*} [RCLike 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] {K : E →L[𝕜] F} {ι : Type*}
    {σ : ι → ℝ} {v : ι → E} {u : ι → F} (hs : IsSingularSystem K σ v u) (m : ℕ) :
    ∀ α : Set.Ioi (0 : ℝ), ∃ c, ∀ i, |iteratedTikhonovFilter m α (σ i ^ 2)| ≤ c :=
  fun α => ⟨(m : ℝ) / (α : ℝ), fun i => abs_iteratedTikhonovFilter_le (hs.sq_mem_Icc i).1⟩

end AutoIp
