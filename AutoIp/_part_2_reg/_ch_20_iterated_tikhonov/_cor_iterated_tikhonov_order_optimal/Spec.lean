/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_12_picard._def_source_set
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
public import AutoIp._part_2_reg._ch_20_iterated_tikhonov._def_iterated_tikhonov
import AutoIp._part_2_reg._ch_15_spectral_regularization._thm_apriori_order_optimal
import AutoIp._part_2_reg._ch_20_iterated_tikhonov._lem_iterated_tikhonov_filter
import AutoIp._part_2_reg._ch_20_iterated_tikhonov._thm_iterated_tikhonov_qualification
public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
public import AutoIp._part_2_reg._ch_14_order_optimality._def_order_optimal

section _cor_iterated_tikhonov_order_optimal

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- For `0 < ν ≤ 2m`, `y ∈ Dom(K†)` with `x† = K† y ∈ X_{ν,ρ}`, data `y^δ` with
`‖y - y^δ‖ ≤ δ` and `α(δ) = (δ/ρ)^{2/(ν+1)}`:
`‖x^δ_{α(δ)} - x†‖ ≤ (√m + 1) δ^{ν/(ν+1)} ρ^{1/(ν+1)}`.

It holds for every `K`, `K = 0` included. -/
public theorem iteratedTikhonov_apriori_rate (hs : IsSingularSystem K σ v u) {m : ℕ}
    {ν ρ : ℝ} (hν : 0 < ν) (hν2 : ν ≤ 2 * m) (hρ : 0 < ρ)
    {y : F} (hy : y ∈ mpDomain K) (hx : moorePenrose K ⟨y, hy⟩ ∈ sourceSet hs ν hν ρ hρ)
    {δ : ℝ} (hδ : 0 < δ) {z : F} (hz : ‖y - z‖ ≤ δ)
    {α : Set.Ioi (0 : ℝ)} (hαdef : (α : ℝ) = (δ / ρ) ^ (2 / (ν + 1))) :
    ‖spectralReg hs (iteratedTikhonovFilter m)
      (iteratedTikhonovFilter_exists_bound_on_spectrum hs m) α z - moorePenrose K ⟨y, hy⟩‖ ≤
      (Real.sqrt m + 1) * δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1)) := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hν2; linarith
    · exact h
  have hfil := iteratedTikhonovFilter_isRegularizingFilter (K := K) hm
  have hF : HasFilterBound K (iteratedTikhonovFilter m) (m : ℝ) :=
    ⟨⟨1, hfil⟩, by exact_mod_cast hm, iSup_abs_iteratedTikhonovFilter_le (K := K) hm⟩
  have hQ := iSup_rpow_mul_abs_one_sub_mul_iteratedTikhonovFilter_le K hν hν2
  set a : ParameterChoice F := ⟨fun d _ => ((d : ℝ) / ρ) ^ (2 / (ν + 1)),
    fun d _ => Real.rpow_pos_of_pos (div_pos d.2 hρ) _⟩ with hadef
  have hval : ∀ (d : Set.Ioi (0 : ℝ)) (w : F), a d w = ((d : ℝ) / ρ) ^ (2 / (ν + 1)) :=
    fun _ _ => rfl
  have hrule : ∀ (d : Set.Ioi (0 : ℝ)) (w : F),
      1 * ((d : ℝ) / ρ) ^ (2 / (ν + 1)) ≤ a d w ∧
        a d w ≤ 1 * ((d : ℝ) / ρ) ^ (2 / (ν + 1)) := by
    intro d w
    rw [hval d w, one_mul]
    exact ⟨le_rfl, le_rfl⟩
  have h := norm_spectralReg_sub_moorePenrose_le_apriori (cl := 1) (cu := 1) hs hfil
    hν hρ hF hQ a one_pos one_pos hrule hy hx hδ hz
  have hpar : a.param ⟨δ, hδ⟩ z = α := Subtype.ext (by rw [hαdef]; exact hval ⟨δ, hδ⟩ z)
  rw [hpar] at h
  refine h.trans (le_of_eq ?_)
  simp only [one_mul, Real.one_rpow, mul_one]

/-- For `0 < ν ≤ 2m`, iterated Tikhonov with the rule `α(δ) = (δ/ρ)^{2/(ν+1)}` is order
optimal for `ν` and `ρ`, with constant `√m + 1`.

It holds for every `K`, `K = 0` included. -/
public theorem iteratedTikhonov_isOrderOptimal (hs : IsSingularSystem K σ v u) {m : ℕ}
    {ν ρ : ℝ} (hν : 0 < ν) (hν2 : ν ≤ 2 * m) (hρ : 0 < ρ) (a : ParameterChoice F)
    (ha : ∀ (δ : Set.Ioi (0 : ℝ)) (z : F), a δ z = ((δ : ℝ) / ρ) ^ (2 / (ν + 1))) :
    IsOrderOptimal K (fun α w => spectralReg hs (iteratedTikhonovFilter m)
        (iteratedTikhonovFilter_exists_bound_on_spectrum hs m) α w) a hs ν ρ
      (Real.sqrt m + 1) := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hν2; linarith
    · exact h
  have hfil := iteratedTikhonovFilter_isRegularizingFilter (K := K) hm
  have hF : HasFilterBound K (iteratedTikhonovFilter m) (m : ℝ) :=
    ⟨⟨1, hfil⟩, by exact_mod_cast hm, iSup_abs_iteratedTikhonovFilter_le (K := K) hm⟩
  have hQ := iSup_rpow_mul_abs_one_sub_mul_iteratedTikhonovFilter_le K hν hν2
  have hrule : ∀ (d : Set.Ioi (0 : ℝ)) (w : F),
      1 * ((d : ℝ) / ρ) ^ (2 / (ν + 1)) ≤ a d w ∧
        a d w ≤ 1 * ((d : ℝ) / ρ) ^ (2 / (ν + 1)) := by
    intro d w
    rw [ha d w, one_mul]
    exact ⟨le_rfl, le_rfl⟩
  have h := isOrderOptimal_apriori (cl := 1) (cu := 1) hs hfil hν hρ hF hQ a one_pos one_pos
    hrule
  have hc : max 1 (Real.sqrt (1 * (m : ℝ)) * (1 : ℝ) ^ (-(1 : ℝ) / 2) + 1 * (1 : ℝ) ^ (ν / 2))
      = Real.sqrt m + 1 := by
    simp only [one_mul, Real.one_rpow, mul_one]
    exact max_eq_right (by linarith [Real.sqrt_nonneg (m : ℝ)])
  rwa [hc] at h

end AutoIp

end _cor_iterated_tikhonov_order_optimal
