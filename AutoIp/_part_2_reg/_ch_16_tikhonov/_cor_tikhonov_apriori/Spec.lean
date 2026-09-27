/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_14_order_optimality._def_order_optimal
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_standard_filters
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_equations
import AutoIp._part_2_reg._ch_12_picard._lem_source_in_kerperp
import AutoIp._part_2_reg._ch_15_spectral_regularization._thm_apriori_order_optimal
import AutoIp._part_2_reg._ch_15_spectral_regularization._thm_spectral_is_regularization
import AutoIp._part_2_reg._ch_16_tikhonov._lem_tikhonov_qualification
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_frac_power
public import AutoIp._part_2_reg._ch_12_picard._def_source_set

section _cor_tikhonov_apriori

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- A priori rule for Tikhonov: for `ν ∈ (0,2]` and an a priori rule `α` with
`c (δ/ρ)^(2/(ν+1)) ≤ α(δ) ≤ C (δ/ρ)^(2/(ν+1))`, Tikhonov regularization is an order optimal
regularization method for that `ν` and `ρ`.

The order optimality constant is given explicitly, as `max(1, c^(-1/2) + C^(ν/2))`. It holds for
every `K`, `K = 0` included. -/
public theorem tikhonov_orderOptimal_apriori (hs : IsSingularSystem K σ v u)
    {ν ρ cl cu : ℝ} (hν : ν ∈ Set.Ioc (0 : ℝ) 2) (hρ : 0 < ρ)
    (hcl : 0 < cl) (hcu : 0 < cu) (a : ParameterChoice F) (ha : a.IsAPriori)
    (hrule : ∀ (δ : Set.Ioi (0 : ℝ)) (z : F),
      cl * ((δ : ℝ) / ρ) ^ (2 / (ν + 1)) ≤ a δ z ∧
        a δ z ≤ cu * ((δ : ℝ) / ρ) ^ (2 / (ν + 1))) :
    IsOrderOptimal K (fun α w => spectralReg hs tikhonovFilter
        (tikhonovFilter_exists_bound_on_spectrum hs) α w) a hs ν ρ
        (max 1 (Real.sqrt (1 * 1) * cl ^ (-(1 : ℝ) / 2) + 1 * cu ^ (ν / 2))) ∧
      IsRegularizationMethod K (fun α w => spectralReg hs tikhonovFilter
          (tikhonovFilter_exists_bound_on_spectrum hs) α w) a := by
  -- (F) and (Q_ν) only; the sharpness of the qualification, and with it `K ≠ 0`, is not
  -- needed for a rate.
  have hFq : HasFilterBound K tikhonovFilter 1 :=
    ⟨⟨1, tikhonovFilter_isRegularizingFilter K⟩, one_pos, iSup_abs_tikhonovFilter_le K⟩
  have hQq : ∀ ν ∈ Set.Ioc (0 : ℝ) 2, ∀ α : Set.Ioi (0 : ℝ),
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
        lam ^ (ν / 2) * |1 - lam * tikhonovFilter α lam|) ≤ 1 * (α : ℝ) ^ (ν / 2) :=
    fun ν hν => iSup_rpow_mul_abs_one_sub_mul_tikhonovFilter_le K hν.1 hν.2
  have hφ : IsRegularizingFilter K tikhonovFilter 1 := tikhonovFilter_isRegularizingFilter K
  have hν0 : (0 : ℝ) < ν := hν.1
  have hν1 : (0 : ℝ) < ν + 1 := by linarith
  have hp : (0 : ℝ) < ν / (ν + 1) := div_pos hν0 hν1
  set c0 : ℝ := Real.sqrt (1 * 1) * cl ^ (-(1 : ℝ) / 2) + 1 * cu ^ (ν / 2) with hc0def
  have hmp : ∀ x ∈ sourceSet hs ν hν0 ρ hρ, moorePenrose K ⟨K x, Submodule.mem_sup_left ⟨x,
      rfl⟩⟩ = x := by
    intro x hx
    have hxk : x ∈ (K.toLinearMap.ker)ᗮ := sourceSet_subset_orthogonal_ker hs hν0 hρ hx
    rw [moorePenrose_apply_apply,
      (Submodule.starProjection_apply_eq_zero_iff _).mpr hxk, sub_zero]
  have hpt : ∀ x ∈ sourceSet hs ν hν0 ρ hρ, ∀ (δ : ℝ) (hδ : 0 < δ), ∀ z : F, ‖K x - z‖ ≤ δ →
      ‖spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) ((a).param ⟨δ,
          hδ⟩ z) z - x‖ ≤
        c0 * δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1)) := by
    intro x hx δ hδ z hz
    have hy : K x ∈ mpDomain K := Submodule.mem_sup_left ⟨x, rfl⟩
    have hx' : moorePenrose K ⟨K x, Submodule.mem_sup_left ⟨x,
        rfl⟩⟩ ∈ sourceSet hs ν hν0 ρ hρ := by rw [hmp x hx]; exact hx
    have hres := norm_spectralReg_sub_moorePenrose_le_apriori hs hφ hν0 hρ hFq (hQq ν hν) a
      hcl hcu hrule hy
      hx' hδ hz
    rw [hmp x hx] at hres
    exact hres
  refine ⟨⟨hν0, hρ, le_max_left _ _, ?_⟩, ?_⟩
  · -- order optimality: take the supremum over the noise ball
    intro x hx δ hδ
    rw [worstCaseError_le_iff K _ a (K x) (Submodule.mem_sup_left ⟨x, rfl⟩) δ hδ]
    intro z hz
    have hzd : ‖K x - z‖ ≤ δ := by
      rw [← dist_eq_norm]
      exact Metric.mem_closedBall'.mp hz
    have hδn : (0 : ℝ) ≤ δ ^ (ν / (ν + 1)) := Real.rpow_nonneg hδ.le _
    have hρn : (0 : ℝ) ≤ ρ ^ ((1 : ℝ) / (ν + 1)) := Real.rpow_nonneg hρ.le _
    rw [hmp x hx, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ((hpt x hx δ hδ z hzd).trans ?_)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right 1 c0) hδn) hρn
  · -- convergence
    have hreg : IsRegularization K (spectralReg hs tikhonovFilter
        (tikhonovFilter_exists_bound_on_spectrum hs)) :=
      isRegularization_spectralReg hs hφ
    have hrpow : Tendsto (fun t : ℝ => t ^ (ν / (ν + 1))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : ContinuousAt (fun t : ℝ => t ^ (ν / (ν + 1))) 0 :=
        Real.continuousAt_rpow_const 0 _ (Or.inr hp.le)
      have h0 : Tendsto (fun t : ℝ => t ^ (ν / (ν + 1))) (𝓝 (0 : ℝ)) (𝓝 0) := by
        have h := hc.tendsto
        rwa [Real.zero_rpow hp.ne'] at h
      exact h0.mono_left nhdsWithin_le_nhds
    exact isRegularizationMethod_apriori hs hφ hreg hν0 hρ hFq a ha hcl hrule

/-- The case `ν = 2` of the node: for `α ∼ δ^(2/3)` there is `c > 0` with
`‖x^δ_{α(δ)} - x†‖ ≤ c δ^(2/3)` for all `x† ∈ X_{2,ρ}` and `y^δ ∈ B_δ(K x†)`.

`α ∼ δ^(2/3)` is read as `c δ^(2/3) ≤ α ≤ C δ^(2/3)` for positive `c`, `C`, and the rule is
not required to be a priori. It holds for every `K`, `K = 0` included. -/
public theorem norm_spectralReg_tikhonov_sub_le_rpow_two_thirds (hs : IsSingularSystem K σ v u)
    {ρ cl cu : ℝ} (hρ : 0 < ρ) (hcl : 0 < cl) (hcu : 0 < cu) (a : ParameterChoice F)
    (hrule : ∀ (δ : Set.Ioi (0 : ℝ)) (z : F),
      cl * (δ : ℝ) ^ ((2 : ℝ) / 3) ≤ a δ z ∧ a δ z ≤ cu * (δ : ℝ) ^ ((2 : ℝ) / 3)) :
    ∃ c > (0 : ℝ), ∀ x ∈ sourceSet hs 2 two_pos ρ hρ, ∀ (δ : ℝ) (hδ : 0 < δ), ∀ z : F,
      ‖K x - z‖ ≤ δ →
        ‖spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs)
            (a.param ⟨δ, hδ⟩ z) z - x‖ ≤ c * δ ^ ((2 : ℝ) / 3) := by
  have hFq : HasFilterBound K tikhonovFilter 1 :=
    ⟨⟨1, tikhonovFilter_isRegularizingFilter K⟩, one_pos, iSup_abs_tikhonovFilter_le K⟩
  have hφ : IsRegularizingFilter K tikhonovFilter 1 := tikhonovFilter_isRegularizingFilter K
  have hQ := iSup_rpow_mul_abs_one_sub_mul_tikhonovFilter_le K (ν := 2) two_pos le_rfl
  -- the rule in terms of `δ/ρ`, by `δ^(2/3) = ρ^(2/3) (δ/ρ)^(2/3)`
  have hr0 : (0 : ℝ) < ρ ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hρ _
  have hconv : ∀ δ : ℝ, 0 ≤ δ →
      (δ : ℝ) ^ ((2 : ℝ) / 3) = ρ ^ ((2 : ℝ) / 3) * (δ / ρ) ^ (2 / ((2 : ℝ) + 1)) := by
    intro δ hδ
    rw [show (2 : ℝ) / (2 + 1) = 2 / 3 by norm_num, Real.div_rpow hδ hρ.le]
    field_simp
  have hrule' : ∀ (δ : Set.Ioi (0 : ℝ)) (z : F),
      cl * ρ ^ ((2 : ℝ) / 3) * ((δ : ℝ) / ρ) ^ (2 / ((2 : ℝ) + 1)) ≤ a δ z ∧
        a δ z ≤ cu * ρ ^ ((2 : ℝ) / 3) * ((δ : ℝ) / ρ) ^ (2 / ((2 : ℝ) + 1)) := by
    intro δ z
    obtain ⟨h1, h2⟩ := hrule δ z
    rw [hconv δ (le_of_lt δ.2)] at h1 h2
    constructor <;> linarith
  set c0 : ℝ := Real.sqrt (1 * 1) * (cl * ρ ^ ((2 : ℝ) / 3)) ^ (-(1 : ℝ) / 2)
    + 1 * (cu * ρ ^ ((2 : ℝ) / 3)) ^ ((2 : ℝ) / 2) with hc0def
  have hc0 : 0 < c0 := by
    have h1 : 0 < (cl * ρ ^ ((2 : ℝ) / 3)) ^ (-(1 : ℝ) / 2) :=
      Real.rpow_pos_of_pos (mul_pos hcl hr0) _
    have h2 : 0 < (cu * ρ ^ ((2 : ℝ) / 3)) ^ ((2 : ℝ) / 2) :=
      Real.rpow_pos_of_pos (mul_pos hcu hr0) _
    rw [hc0def]
    simp only [mul_one, Real.sqrt_one, one_mul]
    linarith
  refine ⟨c0 * ρ ^ ((1 : ℝ) / 3), mul_pos hc0 (Real.rpow_pos_of_pos hρ _), ?_⟩
  intro x hx δ hδ z hz
  have hxk : x ∈ (K.toLinearMap.ker)ᗮ := sourceSet_subset_orthogonal_ker hs two_pos hρ hx
  have hmp : moorePenrose K ⟨K x, Submodule.mem_sup_left ⟨x, rfl⟩⟩ = x := by
    rw [moorePenrose_apply_apply,
      (Submodule.starProjection_apply_eq_zero_iff _).mpr hxk, sub_zero]
  have hy : K x ∈ mpDomain K := Submodule.mem_sup_left ⟨x, rfl⟩
  have hx' : moorePenrose K ⟨K x, hy⟩ ∈ sourceSet hs 2 two_pos ρ hρ := by rw [hmp]; exact hx
  have hres := norm_spectralReg_sub_moorePenrose_le_apriori hs hφ two_pos hρ hFq hQ a
    (mul_pos hcl hr0) (mul_pos hcu hr0) hrule' hy hx' hδ hz
  rw [hmp] at hres
  refine hres.trans (le_of_eq ?_)
  rw [hc0def, show (2 : ℝ) / (2 + 1) = 2 / 3 by norm_num,
    show (1 : ℝ) / (2 + 1) = 1 / 3 by norm_num]
  ring

/-- The inclusion `X_{2,ρ} ⊆ Ran(K*K)` of the node.

It holds for every `K`, `K = 0` included. -/
public theorem sourceSet_two_subset_range_adjoint_comp_self (hs : IsSingularSystem K σ v u)
    (ρ : ℝ) (hρ : 0 < ρ) :
    (sourceSet hs 2 two_pos ρ hρ : Set E)
      ⊆ (K.adjoint ∘L K).toLinearMap.range := by
  intro x hx
  rw [mem_sourceSet_iff] at hx
  obtain ⟨w, -, rfl⟩ := hx
  have h2 : hs.absRpow 2 two_pos.le = ContinuousLinearMap.adjoint K ∘L K := by
    rw [hs.absRpow_congr (show (2 : ℝ) = 1 + 1 by norm_num) two_pos.le
      (add_pos one_pos one_pos).le, hs.absRpow_add one_pos one_pos,
      hs.absRpow_one_comp_absRpow_one]
  exact ⟨w, by rw [← h2]; rfl⟩

end AutoIp

end _cor_tikhonov_apriori
