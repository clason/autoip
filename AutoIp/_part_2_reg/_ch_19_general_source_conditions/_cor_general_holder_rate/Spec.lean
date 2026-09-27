/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_12_picard._def_source_set
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_filter
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
public import AutoIp._part_2_reg._ch_19_general_source_conditions._def_general_qualification
public import AutoIp._part_2_reg._ch_19_general_source_conditions._def_theta_function
import AutoIp._part_2_reg._ch_15_spectral_regularization._thm_apriori_order_optimal
import AutoIp._part_2_reg._ch_19_general_source_conditions._lem_holder_is_index
import AutoIp._part_2_reg._ch_19_general_source_conditions._thm_general_apriori_rate
public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_qualification
import Mathlib.Tactic.Positivity.Finset
import AutoIp.Auxiliary.Rpow

section _cor_general_holder_rate

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The Hölder rate, the rule and the bound: under the hypotheses of the general a priori rate
with `φ = φ_ν` and `x† ∈ X_{ν,ρ}`, the rule of the general rate is `α(δ) = (δ/ρ)^{2/(ν+1)}`,
that is, `α(δ) ∈ (0, κ]` with `Θ_{φ_ν}(α(δ)) = δ/ρ`; it gives
`‖x^δ_{α(δ)} - x†‖ ≤ (√(C_φ C_F) + C_ν) δ^{ν/(ν+1)} ρ^{1/(ν+1)}`.

The hypothesis `δ/ρ ≤ κ^{(ν+1)/2}` is `δ/ρ ≤ Θ_{φ_ν}(κ)`. -/
public theorem norm_spectralReg_sub_moorePenrose_le_apriori_index_rpow {𝕜 : Type*} [RCLike 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] {K : E →L[𝕜] F}
    {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F} (hs : IsSingularSystem K σ v u)
    {flt : Set.Ioi (0 : ℝ) → ℝ → ℝ}
    {Cflt : ℝ} (hflt : IsRegularizingFilter K flt Cflt) {ν ρ CF Cν : ℝ} (hν : 0 < ν) (hρ : 0 < ρ)
    (hF : HasFilterBound K flt CF)
    (hQ : HasQualification K flt (fun t => t ^ (ν / 2)) Cν)
    {y : F} (hy : y ∈ mpDomain K) (hx : moorePenrose K ⟨y, hy⟩ ∈ sourceSet hs ν hν ρ hρ)
    {δ : ℝ} (hδ : 0 < δ) (hδρ : δ / ρ ≤ (‖K‖ ^ 2) ^ ((ν + 1) / 2))
    {z : F} (hz : ‖y - z‖ ≤ δ)
    {α : Set.Ioi (0 : ℝ)} (hαdef : (α : ℝ) = (δ / ρ) ^ (2 / (ν + 1))) :
    ((α : ℝ) ≤ ‖K‖ ^ 2 ∧ thetaIndex (fun t : ℝ => t ^ (ν / 2)) (α : ℝ) = δ / ρ) ∧
      ‖spectralReg hs flt (hflt.exists_bound_on_spectrum hs) α z - moorePenrose K ⟨y, hy⟩‖ ≤
        (Real.sqrt (Cflt * CF) + Cν) * δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1)) :=
  by
  have hk0 : (0:ℝ) ≤ ‖K‖ ^ 2 := by positivity
  have ht : (0:ℝ) < δ / ρ := div_pos hδ hρ
  have hν1 : (0:ℝ) < ν + 1 := by linarith
  have hν1' : (ν:ℝ) + 1 ≠ 0 := hν1.ne'
  have hα0 : (0:ℝ) < (α : ℝ) := α.2
  have hα0' : (0:ℝ) < (δ / ρ) ^ (2 / (ν + 1)) := Real.rpow_pos_of_pos ht _
  have he1 : (ν + 1) / 2 * (2 / (ν + 1)) = 1 := by
    field_simp
  have hακ : (α : ℝ) ≤ ‖K‖ ^ 2 := by
    rw [hαdef]
    have h1 : (δ / ρ) ^ (2 / (ν + 1)) ≤ ((‖K‖ ^ 2) ^ ((ν + 1) / 2)) ^ (2 / (ν + 1)) :=
      Real.rpow_le_rpow ht.le hδρ (div_nonneg (by norm_num) hν1.le)
    rwa [← Real.rpow_mul hk0, he1, Real.rpow_one] at h1
  have he2 : 2 / (ν + 1) * (1 / 2 + ν / 2) = 1 := by
    field_simp
    ring
  have hαΘ : thetaIndex (fun t : ℝ => t ^ (ν / 2)) (α : ℝ) = δ / ρ := by
    rw [hαdef, thetaIndex_apply]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hα0', ← Real.rpow_mul ht.le, he2, Real.rpow_one]
  refine ⟨⟨hακ, hαΘ⟩, ?_⟩
  have hxsrc : moorePenrose K ⟨y, hy⟩ ∈ sourceSetIndex hs (fun t : ℝ => t ^ (ν / 2))
      ((isIndexFunction_rpow hν (‖K‖ ^ 2)).exists_bound_on_spectrum hs) ρ hρ := by
    rw [sourceSetIndex_rpow hs hν]
    exact hx
  have hres := norm_spectralReg_sub_moorePenrose_le_apriori_index hs hflt
    (isIndexFunction_rpow hν _) hρ hF hQ
    hy hxsrc hz hακ hαΘ
  refine hres.trans_eq ?_
  have he3 : 2 / (ν + 1) * (ν / 2) = ν / (ν + 1) := by
    field_simp
  have hval : ((α : ℝ)) ^ (ν / 2) = (δ / ρ) ^ (ν / (ν + 1)) := by
    rw [hαdef, ← Real.rpow_mul ht.le, he3]
  have hrho := rpow_split_rate hρ hν1
  have key2 := rpow_div_mul_rate hδ hρ hν1
  rw [hval]
  calc (Real.sqrt (Cflt * CF) + Cν) * ρ * (δ / ρ) ^ (ν / (ν + 1))
      = (Real.sqrt (Cflt * CF) + Cν) * ((δ / ρ) ^ (ν / (ν + 1)) * ρ) := by ring
    _ = (Real.sqrt (Cflt * CF) + Cν) * (δ ^ (ν / (ν + 1)) * ρ ^ ((1:ℝ) / (ν + 1))) := by
        rw [key2]
    _ = (Real.sqrt (Cflt * CF) + Cν) * δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1)) := by ring

/-- The Hölder rate, the comparison with the order-optimal a priori bound: for
`α(δ) = (δ/ρ)^{2/(ν+1)}` the rate is the conclusion of the order-optimal a priori bound with
`c = C = 1`: the rule satisfies `c (δ/ρ)^{2/(ν+1)} ≤ α(δ) ≤ C (δ/ρ)^{2/(ν+1)}` and the constant
`√(C_φ C_F) + C_ν` is `√(C_φ C_F) c^{-1/2} + C_ν C^{ν/2}` for these `c` and `C`.

It needs none of the hypotheses of the general a priori rate. -/
public theorem apriori_index_rpow_bracket_one_and_const_eq {ν δ ρ : ℝ} {α : Set.Ioi (0 : ℝ)}
    (hαdef : (α : ℝ) = (δ / ρ) ^ (2 / (ν + 1))) (Cflt CF Cν : ℝ) :
    ((1 : ℝ) * (δ / ρ) ^ (2 / (ν + 1)) ≤ (α : ℝ) ∧ (α : ℝ) ≤ 1 * (δ / ρ) ^ (2 / (ν + 1))) ∧
      Real.sqrt (Cflt * CF) + Cν =
        Real.sqrt (Cflt * CF) * (1 : ℝ) ^ (-(1 : ℝ) / 2) + Cν * (1 : ℝ) ^ (ν / 2) :=
  ⟨⟨(one_mul _).trans_le hαdef.ge, hαdef.le.trans (one_mul _).ge⟩, by simp⟩

end AutoIp

end _cor_general_holder_rate
