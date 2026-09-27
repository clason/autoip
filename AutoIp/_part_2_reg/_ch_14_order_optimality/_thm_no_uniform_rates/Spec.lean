/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_14_order_optimality._def_worst_case_error
import AutoIp._part_2_reg._ch_11_moore_penrose._thm_mp_inverse

section _thm_no_uniform_rates

namespace AutoIp

open Filter Topology
open scoped ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Let `{R_α}` be linear maps `Y → X` and `α` a parameter choice rule. If there is
`ψ : (0,∞) → (0,∞)` with `ψ(t) → 0` as `t → 0` and
`sup_{y ∈ Dom(T†) ∩ B_Y} E(y, δ) ≤ ψ(δ)` for all small `δ > 0`, then `T†` is bounded.
Here `ψ` is a function on `ℝ` positive on `(0,∞)`, and boundedness is stated as a bound
`‖T† y‖ ≤ C ‖y‖` on `Dom(T†)`. -/
public theorem exists_norm_moorePenrose_le_of_uniform_rate {T : E →L[𝕜] F}
    (R : Set.Ioi (0 : ℝ) → F →ₗ[𝕜] E)
    (a : ParameterChoice F) (ψ : ℝ → ℝ) (hψpos : ∀ t > (0 : ℝ), 0 < ψ t)
    (hψ : Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hbound : ∃ δ₀ > (0 : ℝ), ∀ (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) δ₀),
      ∀ y, ∀ hy : y ∈ mpDomain T, ‖y‖ ≤ 1 →
        worstCaseError T (fun α z => R α z) a y hy δ hδ.1 ≤ ENNReal.ofReal (ψ δ)) :
    ∃ C : ℝ, ∀ y : (moorePenrose T).domain, ‖moorePenrose T y‖ ≤ C * ‖(y : F)‖ := by
  obtain ⟨δ₀, hδ₀, hb⟩ := hbound
  have hmin : (0 : ℝ) < min δ₀ 1 := lt_min hδ₀ one_pos
  have h3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ψ t < 1 ∧ t ∈ Set.Ioo (0 : ℝ) (min δ₀ 1) := by
    filter_upwards [hψ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      Ioo_mem_nhdsGT hmin] with t h1 h2 using ⟨h1, h2⟩
  obtain ⟨t₀, hψt₀, ht₀⟩ := h3.exists
  have ht₀0 : (0 : ℝ) < t₀ := ht₀.1
  have ht₀δ : t₀ < δ₀ := lt_of_lt_of_le ht₀.2 (min_le_left _ _)
  have ht₀1 : t₀ ≤ 1 := le_of_lt (lt_of_lt_of_le ht₀.2 (min_le_right _ _))
  have hψnn : (0 : ℝ) ≤ ψ t₀ := (hψpos t₀ ht₀0).le
  have key : ∀ y, ∀ hy : y ∈ mpDomain T, ‖y‖ ≤ 1 → ∀ z : F, ‖z - y‖ ≤ t₀ →
      ‖R ((a).param ⟨t₀, ht₀0⟩ z) z - moorePenrose T ⟨y, hy⟩‖ ≤ ψ t₀ := by
    intro y hy hy1 z hz
    have hmemball : z ∈ Metric.closedBall y t₀ := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have h1 := le_worstCaseError T (fun α z => R α z) a y hy ht₀0 hmemball
    rw [← ofReal_norm] at h1
    exact (ENNReal.ofReal_le_ofReal_iff hψnn).1 (h1.trans (hb t₀ ⟨ht₀0, ht₀δ⟩ y hy hy1))
  have hmp0 : moorePenrose T ⟨(0 : F), Submodule.zero_mem _⟩ = 0 := moorePenrose_zero
  refine ⟨2 / t₀, ?_⟩
  rintro ⟨w, hw⟩
  change ‖moorePenrose T ⟨w, hw⟩‖ ≤ 2 / t₀ * ‖w‖
  rcases eq_or_ne w 0 with rfl | hw0
  · simp [hmp0]
  have hwn : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hw0
  set c : 𝕜 := (RCLike.ofReal (t₀ / ‖w‖) : 𝕜) with hc
  have hcn : ‖c‖ = t₀ / ‖w‖ := by
    rw [hc, RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
  set z : F := c • w with hz
  have hzmem : z ∈ mpDomain T := Submodule.smul_mem _ c hw
  have hzn : ‖z‖ = t₀ := by
    rw [hz, norm_smul, hcn]
    field_simp
  have hz1 : ‖z‖ ≤ 1 := by rw [hzn]; exact ht₀1
  have k1 := key 0 (Submodule.zero_mem _) (by simp) z (by simpa using hzn.le)
  have k2 := key z hzmem hz1 z (by simp [ht₀0.le])
  rw [hmp0, sub_zero] at k1
  have htri : ‖moorePenrose T ⟨z, hzmem⟩‖ ≤ 2 * ψ t₀ := by
    have he : moorePenrose T ⟨z, hzmem⟩ =
        (R ((a).param ⟨t₀, ht₀0⟩ z)) z
          - ((R ((a).param ⟨t₀, ht₀0⟩ z)) z - moorePenrose T ⟨z, hzmem⟩) := by abel
    have hnt := norm_sub_le ((R ((a).param ⟨t₀, ht₀0⟩ z)) z)
      ((R ((a).param ⟨t₀, ht₀0⟩ z)) z - moorePenrose T ⟨z, hzmem⟩)
    rw [← he] at hnt
    linarith
  have hmpz : moorePenrose T ⟨z, hzmem⟩ = c • moorePenrose T ⟨w, hw⟩ := (moorePenrose
      T).map_smul c ⟨w, hw⟩
  rw [hmpz, norm_smul, hcn] at htri
  have hψ1 : ψ t₀ ≤ 1 := hψt₀.le
  have hfin : t₀ / ‖w‖ * ‖moorePenrose T ⟨w, hw⟩‖ ≤ 2 := htri.trans (by linarith)
  rw [div_mul_eq_mul_div, div_le_iff₀ hwn] at hfin
  rw [div_mul_eq_mul_div, le_div_iff₀ ht₀0]
  linarith

end AutoIp

end _thm_no_uniform_rates
