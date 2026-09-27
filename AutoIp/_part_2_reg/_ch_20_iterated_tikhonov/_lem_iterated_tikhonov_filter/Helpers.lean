/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_20_iterated_tikhonov._def_iterated_tikhonov

import Mathlib.Topology.Order.AtTopBotIxx
namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- For `m ≥ 1` the iterated Tikhonov filter is a regularizing filter with `C_φ = 1`, and
`sup_{λ ∈ (0,κ]} |φ^(m)_α(λ)| ≤ m α⁻¹` for every `α > 0`. -/
public theorem iteratedTikhonov_filter_aux (K : E →L[𝕜] F) {m : ℕ} (hm : 0 < m) :
    IsRegularizingFilter K (iteratedTikhonovFilter m) 1 ∧
      ∀ α : Set.Ioi (0 : ℝ),
        (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |iteratedTikhonovFilter m α lam|) ≤
          (m : ℝ) * (α : ℝ)⁻¹ := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hkey : ∀ α lam : ℝ, 0 < α → 0 < lam →
      0 ≤ 1 - (α / (α + lam)) ^ m ∧
        1 - (α / (α + lam)) ^ m ≤ (m : ℝ) * (lam / (α + lam)) := by
    intro α lam hα hlam
    have hsum : (0 : ℝ) < α + lam := by linarith
    have hne : α + lam ≠ 0 := hsum.ne'
    have hu0 : (0 : ℝ) ≤ α / (α + lam) := by positivity
    have hu1 : α / (α + lam) ≤ 1 := by rw [div_le_one hsum]; linarith
    have hs0 : (0 : ℝ) ≤ lam / (α + lam) := by positivity
    have hs1 : lam / (α + lam) ≤ 1 := by rw [div_le_one hsum]; linarith
    have hp1 : (α / (α + lam)) ^ m ≤ 1 := pow_le_one₀ hu0 hu1
    refine ⟨by linarith, ?_⟩
    have hb := one_add_mul_le_pow (a := -(lam / (α + lam))) (by linarith) m
    have he : 1 + -(lam / (α + lam)) = α / (α + lam) := by field_simp; ring
    rw [he] at hb
    linarith
  have hphi : ∀ (α : Set.Ioi (0 : ℝ)) (lam : ℝ), 0 < lam →
      0 ≤ iteratedTikhonovFilter m α lam ∧
        iteratedTikhonovFilter m α lam ≤ (m : ℝ) / ((α : ℝ) + lam) := by
    intro α lam hlam
    have hα : (0 : ℝ) < (α : ℝ) := α.2
    obtain ⟨h1, h2⟩ := hkey (α : ℝ) lam hα hlam
    have hsum : (0 : ℝ) < (α : ℝ) + lam := by linarith
    have hne : (α : ℝ) + lam ≠ 0 := hsum.ne'
    rw [iteratedTikhonovFilter_of_ne_zero hlam.ne']
    refine ⟨mul_nonneg (inv_nonneg.mpr hlam.le) h1, ?_⟩
    calc lam⁻¹ * (1 - ((α : ℝ) / ((α : ℝ) + lam)) ^ m)
        ≤ lam⁻¹ * ((m : ℝ) * (lam / ((α : ℝ) + lam))) :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hlam.le)
      _ = (m : ℝ) / ((α : ℝ) + lam) := by field_simp
  have hbdd : ∀ α : Set.Ioi (0 : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2),
      |iteratedTikhonovFilter m α t| ≤ (m : ℝ) / (α : ℝ) :=
    fun _ _ ht => abs_iteratedTikhonovFilter_le ht.1
  refine ⟨⟨one_pos, fun α => ⟨(m : ℝ) / (α : ℝ), hbdd α⟩, ?_, ?_⟩, ?_⟩
  · -- (1) `φ^(m)_α(λ) → λ⁻¹`, since `α/(α+λ) → 0` and `m ≥ 1`.
    intro lam hlam
    have hl : lam ≠ 0 := hlam.1.ne'
    have h1 : Tendsto (fun α : ℝ => α / (α + lam)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : ContinuousAt (fun α : ℝ => α / (α + lam)) 0 := by
        refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
        simpa using hl
      have h := hc.tendsto
      simp only [zero_div, zero_add] at h
      exact h.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun α : ℝ => lam⁻¹ * (1 - (α / (α + lam)) ^ m))
        (𝓝[>] (0 : ℝ)) (𝓝 lam⁻¹) := by
      have h := ((h1.pow m).const_sub 1).const_mul lam⁻¹
      simpa [zero_pow hm.ne'] using h
    exact (h2.comp (map_coe_Ioi_atBot (0 : ℝ)).le).congr fun α =>
      (iteratedTikhonovFilter_of_ne_zero hl m α).symm
  · -- (2) `λ |φ^(m)_α(λ)| = 1 - r^(m)_α(λ) ≤ 1`
    intro α lam hlam
    have hα : (0 : ℝ) < (α : ℝ) := α.2
    obtain ⟨p1, -⟩ := hphi α lam hlam.1
    have hu0 : (0 : ℝ) ≤ ((α : ℝ) / ((α : ℝ) + lam)) ^ m := by
      have : (0 : ℝ) < (α : ℝ) + lam := by linarith [hlam.1]
      positivity
    rw [abs_of_nonneg p1, iteratedTikhonovFilter_of_ne_zero hlam.1.ne', ← mul_assoc,
      mul_inv_cancel₀ hlam.1.ne', one_mul]
    linarith
  · -- condition (F) with `C_F = m`
    intro α
    have hα : (0 : ℝ) < (α : ℝ) := α.2
    have hc : (0 : ℝ) ≤ (m : ℝ) * (α : ℝ)⁻¹ := by positivity
    refine Real.iSup_le (fun lam => Real.iSup_le (fun h => ?_) hc) hc
    have h1 := hbdd α lam ⟨h.1.le, h.2⟩
    rwa [div_eq_mul_inv] at h1

end AutoIp
