/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_12_picard._def_source_set
public import AutoIp._part_2_reg._ch_13_regularization._def_parameter_choice
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_standard_filters

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- A rule whose error obeys the order-optimal bound at `ν = 1` obeys the rate
`c' ρ^(1/2) δ^(1/2)` with `c' > 0`. -/
public theorem exists_sqrt_rate_of_forall_norm_sub_le {a : ParameterChoice F}
    (hs : IsSingularSystem K σ v u) {τ : ℝ}
    (hrate : ∃ c ≥ (1 : ℝ), ∀ (ρ : ℝ) (hρ : 0 < ρ), ∀ x ∈ sourceSet hs 1 one_pos ρ hρ,
      ∀ (δ : ℝ) (hδ : 0 < δ), ∀ z : F, ‖z - K x‖ ≤ δ → τ * δ < ‖z‖ →
        ‖spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) ((a).param
            ⟨δ, hδ⟩ z) z - x‖ ≤
          c * δ ^ ((1 : ℝ) / (1 + 1)) * ρ ^ ((1 : ℝ) / (1 + 1))) :
    ∃ c' > (0 : ℝ), ∀ (ρ : ℝ) (hρ : 0 < ρ), ∀ x ∈ sourceSet hs 1 one_pos ρ hρ,
      ∀ (δ : ℝ) (hδ : 0 < δ), ∀ z : F, ‖z - K x‖ ≤ δ → τ * δ < ‖z‖ →
        ‖spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) ((a).param
            ⟨δ, hδ⟩ z) z - x‖ ≤
          c' * ρ ^ ((1 : ℝ) / 2) * δ ^ ((1 : ℝ) / 2) := by
  obtain ⟨c, hc1, hc2⟩ := hrate
  refine ⟨c, lt_of_lt_of_le zero_lt_one hc1, ?_⟩
  intro ρ hρ x hx δ hδ z hz hτδ
  refine (hc2 ρ hρ x hx δ hδ z hz hτδ).trans (le_of_eq ?_)
  rw [show ((1 : ℝ) / (1 + 1)) = (1 : ℝ) / 2 by norm_num]
  ring

end AutoIp
