/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_12_picard._def_source_set
public import AutoIp._part_2_reg._ch_13_regularization._def_discrepancy_principle
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_standard_filters
import AutoIp._part_2_reg._ch_15_spectral_regularization._thm_discrepancy_order_optimal
import AutoIp._part_2_reg._ch_16_tikhonov._lem_tikhonov_qualification
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_abs_norm
import AutoIp._part_2_reg._ch_16_tikhonov._cor_tikhonov_discrepancy.Helpers

section _cor_tikhonov_discrepancy

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Discrepancy principle for Tikhonov: if `Ran(K)` is dense in `Y` and `τ > 1`, the
discrepancy principle defines a rule `α_τ` for Tikhonov regularization, `(R_α, α_τ)` is a
convergent regularization method, and for every `ν ∈ (0,1]` there is `c ≥ 1` with
`‖x^δ_{α_τ(δ,y^δ)} - x†‖ ≤ c δ^(ν/(ν+1)) ρ^(1/(ν+1))` for every `ρ > 0`, `x† ∈ X_{ν,ρ}`,
`δ > 0` and `y^δ ∈ B_δ(K x†)` with `‖y^δ‖ > τ δ`.

The hypothesis `dim Ran(K) = ∞` of the prose is not needed; `K ≠ 0` is the chapter's standing
assumption. -/
public theorem tikhonov_orderOptimal_discrepancy (hs : IsSingularSystem K σ v u) (hK : K ≠ 0)
    (hdense : Dense (K.toLinearMap.range : Set F))
    {τ : ℝ} (hτ : 1 < τ) :
    ∃ a : ParameterChoice F,
      IsDiscrepancyPrinciple K (spectralReg hs tikhonovFilter
          (tikhonovFilter_exists_bound_on_spectrum hs)) τ a ∧
      IsRegularizationMethod K (fun α w => spectralReg hs tikhonovFilter
          (tikhonovFilter_exists_bound_on_spectrum hs) α w) a ∧
      (∀ (ν : ℝ) (hν : ν ∈ Set.Ioc (0 : ℝ) 1), ∃ c ≥ (1 : ℝ), ∀ (ρ : ℝ) (hρ : 0 < ρ),
        ∀ x ∈ sourceSet hs ν hν.1 ρ hρ,
        ∀ (δ : ℝ) (hδ : 0 < δ), ∀ z : F, ‖z - K x‖ ≤ δ → τ * δ < ‖z‖ →
          ‖spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) ((a).param
              ⟨δ, hδ⟩ z) z - x‖ ≤
            c * δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1))) := by
  obtain ⟨hFq, hQq, hqual⟩ := tikhonov_qualification (K := K) hK
  have hφ : IsRegularizingFilter K tikhonovFilter 1 := tikhonovFilter_isRegularizingFilter K
  have hres : ∀ (α : Set.Ioi (0 : ℝ)) (lam : ℝ), 0 < lam →
      |1 - lam * tikhonovFilter α lam| = (α : ℝ) / (lam + (α : ℝ)) :=
    fun _ _ hlam => abs_one_sub_mul_tikhonovFilter hlam
  have hCr : (⨆ α : Set.Ioi (0 : ℝ), ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
      |1 - lam * tikhonovFilter α lam|) < τ := by
    refine lt_of_le_of_lt ?_ hτ
    refine Real.iSup_le (fun α => ?_) zero_le_one
    refine Real.iSup_le (fun lam => Real.iSup_le (fun hlam => ?_) zero_le_one) zero_le_one
    have hα' : (0 : ℝ) < (α : ℝ) := α.2
    have hlam' : (0 : ℝ) < lam := hlam.1
    rw [hres α lam hlam', div_le_one (by linarith)]
    linarith
  have hcont : ∀ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
      Continuous (fun α : Set.Ioi (0 : ℝ) => tikhonovFilter α lam) := by
    intro lam hlam
    simp only [tikhonovFilter]
    refine Continuous.inv₀ (by fun_prop) ?_
    intro α
    have hpos : (0 : ℝ) < lam + (α : ℝ) := by
      have h1 := hlam.1
      have h2 : (0 : ℝ) < (α : ℝ) := α.2
      linarith
    exact hpos.ne'
  obtain ⟨b, hb1, hb2, hb3⟩ := discrepancy_rate_and_convergence hs hK hφ hdense
    (ν₀ := 2) one_lt_two
    ⟨1, one_pos, ⟨1, tikhonovFilter_isRegularizingFilter K⟩, one_pos, hFq⟩
    (fun ν hν => ⟨1, one_pos, hQq ν hν⟩) hcont hCr
  exact ⟨b, hb1, hb2, fun ν hν => hb3 ν ⟨hν.1, by linarith [hν.2]⟩⟩

/-- The "in particular" rate: if `Ran(K)` is dense in `Y` and `τ > 1`, the discrepancy principle
defines a rule `α_τ` for Tikhonov regularization and there is `c' > 0`, depending only on `τ`
and on `K`, with `‖x^δ_{α_τ(δ,y^δ)} - x†‖ ≤ c' ρ^(1/2) δ^(1/2)` for every `ρ > 0`,
`x† ∈ X_{1,ρ}`, `δ > 0` and `y^δ ∈ B_δ(K x†)` with `‖y^δ‖ > τ δ`.

The hypothesis `dim Ran(K) = ∞` of the prose is not needed; `K ≠ 0` is the chapter's standing
assumption. -/
public theorem tikhonov_sqrt_rate_discrepancy (hs : IsSingularSystem K σ v u) (hK : K ≠ 0)
    (hdense : Dense (K.toLinearMap.range : Set F))
    {τ : ℝ} (hτ : 1 < τ) :
    ∃ a : ParameterChoice F,
      IsDiscrepancyPrinciple K (spectralReg hs tikhonovFilter
          (tikhonovFilter_exists_bound_on_spectrum hs)) τ a ∧
      ∃ c' > (0 : ℝ), ∀ (ρ : ℝ) (hρ : 0 < ρ), ∀ x ∈ sourceSet hs 1 one_pos ρ hρ,
        ∀ (δ : ℝ) (hδ : 0 < δ), ∀ z : F, ‖z - K x‖ ≤ δ → τ * δ < ‖z‖ →
          ‖spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) ((a).param
              ⟨δ, hδ⟩ z) z - x‖ ≤
            c' * ρ ^ ((1 : ℝ) / 2) * δ ^ ((1 : ℝ) / 2) := by
  obtain ⟨a, ha, -, hrate⟩ := tikhonov_orderOptimal_discrepancy hs hK hdense hτ
  exact ⟨a, ha, exists_sqrt_rate_of_forall_norm_sub_le hs (hrate 1 ⟨one_pos, le_rfl⟩)⟩

/-- The inclusion `X_{1,ρ} ⊆ Ran(K*)` of the node.

It holds for every `K`, `K = 0` included. -/
public theorem sourceSet_one_subset_range_adjoint (hs : IsSingularSystem K σ v u) (ρ : ℝ)
    (hρ : 0 < ρ) :
    (sourceSet hs 1 one_pos ρ hρ : Set E)
      ⊆ K.adjoint.toLinearMap.range := by
  intro x hx
  rw [mem_sourceSet_iff] at hx
  obtain ⟨w, -, rfl⟩ := hx
  rw [← hs.range_absRpow_one]
  exact ⟨w, rfl⟩

end AutoIp

end _cor_tikhonov_discrepancy
