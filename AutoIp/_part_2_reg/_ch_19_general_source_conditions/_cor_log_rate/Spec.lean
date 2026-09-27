/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_filter
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
public import AutoIp._part_2_reg._ch_19_general_source_conditions._def_general_qualification
public import AutoIp._part_2_reg._ch_19_general_source_conditions._def_general_source
public import AutoIp._part_2_reg._ch_19_general_source_conditions._def_theta_function
public import AutoIp._part_2_reg._ch_19_general_source_conditions._lem_log_is_index
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_qualification
import AutoIp._part_2_reg._ch_19_general_source_conditions._thm_general_apriori_rate
import AutoIp.Auxiliary.ExpBound
import Mathlib.Tactic.Positivity.Finset
import AutoIp._part_2_reg._ch_19_general_source_conditions._cor_log_rate.Helpers

section _cor_log_rate

section

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
/-- Logarithmic rate: if the filter satisfies (F) and (Q_{φ^log_p}) and `x† ∈ X_{φ^log_p,ρ}`,
the a priori rule of the general rate theorem gives, for sufficiently small `δ > 0`,
`‖x^δ_{α(δ)} - x†‖ ≤ C ρ (log (ρ/δ))^{-p}`, with `C` depending only on `p`, `κ`, `C_φ`, `C_F`
and `C^q_{φ^log_p}`: one `C` serves every operator `K` with `‖K‖² = κ`, whatever its spaces,
its singular system and its filter.

"Sufficiently small" is `δ/ρ ≤ t₀` for a `t₀ ∈ (0, 1)` depending only on `p` and `κ`. The rule
is given as a parameter `α ∈ (0, κ]` with `Θ_{φ^log_p}(α) = δ/ρ`. -/
public
theorem exists_norm_spectralReg_sub_moorePenrose_le_logIndex {p : ℝ} (hp : 0 < p) (κ : ℝ) :
    ∃ t₀ ∈ Set.Ioo (0 : ℝ) 1,
      ∀ (Cflt CF Cq : ℝ), ∃ C > (0 : ℝ),
        ∀ {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
          [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
          (K : E →L[𝕜] F), ‖K‖ ^ 2 = κ →
        ∀ {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F} (hs : IsSingularSystem K σ v u),
        ∀ (flt : Set.Ioi (0 : ℝ) → ℝ → ℝ), ∀ hflt : IsRegularizingFilter K flt Cflt,
        (HasFilterBound K flt CF) →
        HasQualification K flt (logIndex (‖K‖ ^ 2) p hp) Cq →
        ∀ (ρ : ℝ) (hρ : 0 < ρ), ∀ y, ∀ hy : y ∈ mpDomain K,
          moorePenrose K ⟨y, hy⟩ ∈ sourceSetIndex hs (logIndex (‖K‖ ^ 2) p hp)
            ((isIndexFunction_logIndex hp).exists_bound_on_spectrum hs) ρ hρ →
          ∀ δ > (0 : ℝ), δ / ρ ≤ t₀ → ∀ z : F, ‖y - z‖ ≤ δ →
            ∀ α : Set.Ioi (0 : ℝ), (α : ℝ) ≤ ‖K‖ ^ 2 →
              thetaIndex (logIndex (‖K‖ ^ 2) p hp) (α : ℝ) = δ / ρ →
              ‖spectralReg hs flt (hflt.exists_bound_on_spectrum hs) α z - moorePenrose K ⟨y, hy⟩‖ ≤
                C * ρ * Real.log (ρ / δ) ^ (-p) :=
  by
  rcases le_or_gt κ 0 with hkle | hkpos
  · refine ⟨1/2, ⟨by norm_num, by norm_num⟩, ?_⟩
    intro Cflt CF Cq
    refine ⟨1, one_pos, ?_⟩
    intro 𝕜 _ E F _ _ _ _ _ _ K hK ι σ v u hs flt hflt hF hQ ρ hρ y hy hxsrc δ hδ hδρ z hz α hακ
      hαΘ
    exfalso
    have h1 : (0 : ℝ) < (α : ℝ) := α.2
    linarith
  · obtain ⟨t₀, ht₀mem, hkey⟩ := exists_logIndex_le_log_inv_rpow hkpos hp
    refine ⟨t₀, ht₀mem, ?_⟩
    intro Cflt CF Cq
    refine ⟨|Real.sqrt (Cflt * CF) + Cq| + 1, by positivity, ?_⟩
    intro 𝕜 _ E F _ _ _ _ _ _ K hK ι σ v u hs flt hflt hF hQ ρ hρ y hy hxsrc δ hδ hδρ z hz α hακ
      hαΘ
    subst hK
    have hres := norm_spectralReg_sub_moorePenrose_le_apriori_index hs hflt
      (isIndexFunction_logIndex hp) hρ hF hQ
      hy hxsrc hz hακ hαΘ
    refine hres.trans ?_
    have h2 : (0:ℝ) ≤ logIndex (‖K‖ ^ 2) p hp (α : ℝ) :=
      (isIndexFunction_logIndex hp).nonneg (α : ℝ) ⟨α.2.le, hακ⟩
    have h1 : logIndex (‖K‖ ^ 2) p hp (α : ℝ) ≤ Real.log (ρ / δ) ^ (-p) := by
      have hk := hkey (δ / ρ) (div_pos hδ hρ) hδρ (α : ℝ) α.2 hακ hαΘ
      rwa [one_div_div] at hk
    have hcle : Real.sqrt (Cflt * CF) + Cq ≤ |Real.sqrt (Cflt * CF) + Cq| + 1 := by
      have := le_abs_self (Real.sqrt (Cflt * CF) + Cq)
      linarith
    calc (Real.sqrt (Cflt * CF) + Cq) * ρ * logIndex (‖K‖ ^ 2) p hp (α : ℝ)
        ≤ (|Real.sqrt (Cflt * CF) + Cq| + 1) * ρ * logIndex (‖K‖ ^ 2) p hp (α : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcle hρ.le) h2
      _ ≤ (|Real.sqrt (Cflt * CF) + Cq| + 1) * ρ * Real.log (ρ / δ) ^ (-p) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg (by positivity) hρ.le)

end AutoIp

end

end _cor_log_rate
