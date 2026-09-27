/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_12_picard._def_source_set
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_standard_filters
public import AutoIp._part_2_reg._ch_21_perturbed_operator._def_perturbed_problem
import AutoIp._part_2_reg._ch_21_perturbed_operator._lem_tikhonov_operator_perturbation
import AutoIp._part_2_reg._ch_21_perturbed_operator._thm_perturbed_total_error
public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
import AutoIp.Auxiliary.Rpow

section _cor_perturbed_rate

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K Kh : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F} {ι' : Type*}
variable {σ' : ι' → ℝ} {v' : ι' → E} {u' : ι' → F}

/-- Rate when the operator error is small relative to the data error: in the setting of
the total-error bound, with `α(δ) = (δ/ρ)^(2/(ν+1))`, `0 < δ ≤ ρ` and
`h (‖y‖ + δ) ≤ δ α(δ)`, `‖x^{h,δ}_{α(δ)} - x†‖ ≤ (C₁ + 3/2) δ^(ν/(ν+1)) ρ^(1/(ν+1))`, where
`C₁ = 1 + (2‖K‖ + h)/2`.

The Lean assumes `y ∈ Dom(K†)` rather than `y ∈ Ran(K)`, and the closing comparison with
the a priori rate for an exact operator is not stated. -/
public
theorem norm_spectralReg_sub_moorePenrose_le_perturbed_apriori (hs : IsSingularSystem K σ v u)
    (hsh : IsSingularSystem Kh σ' v' u') {y z : F} {h δ ν ρ : ℝ}
    (hd : IsAdmissibleData K Kh y z h δ) (hy : y ∈ mpDomain K)
    (hν : 0 < ν) (hν2 : ν ≤ 2) (hρ : 0 < ρ)
    (hx : moorePenrose K ⟨y, hy⟩ ∈ sourceSet hs ν hν ρ hρ) (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hsmall : h * (‖y‖ + δ) ≤ δ * (δ / ρ) ^ (2 / (ν + 1)))
    {α : Set.Ioi (0 : ℝ)} (hαdef : (α : ℝ) = (δ / ρ) ^ (2 / (ν + 1))) :
    ‖spectralReg hsh tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum
        hsh) α z - moorePenrose K ⟨y, hy⟩‖ ≤
      ((1 + (2 * ‖K‖ + h) / 2) + 3 / 2) *
        (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))) := by
  have hρ : (0 : ℝ) < ρ := lt_of_lt_of_le hδ hδρ
  have hν1 : (0 : ℝ) < ν + 1 := by linarith
  have hν1' : (ν : ℝ) + 1 ≠ 0 := hν1.ne'
  have ht : (0 : ℝ) < δ / ρ := div_pos hδ hρ
  have hexp : (0 : ℝ) < 2 / (ν + 1) := by positivity
  have hα : (0 : ℝ) < (α : ℝ) := α.2
  have hα1 : (α : ℝ) ≤ 1 := by
    rw [hαdef]
    exact Real.rpow_le_one ht.le (by rw [div_le_one hρ]; exact hδρ) hexp.le
  rw [← hαdef] at hsmall
  have hh0 : (0 : ℝ) ≤ h := le_trans (norm_nonneg _) hd.opNorm_sub_le
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have hC1 : (0 : ℝ) ≤ 1 + (2 * ‖K‖ + h) / 2 := by positivity
  have hbase :=
    norm_spectralReg_sub_moorePenrose_le_perturbed (α := α) hs hsh hd hy hν hν2 hρ hx hα1
  set D := δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1)) with hDdef
  set C₁ := 1 + (2 * ‖K‖ + h) / 2 with hC1def
  have hsq0 : 0 < Real.sqrt (α : ℝ) := Real.sqrt_pos.mpr hα
  have hα32 := rpow_three_halves hα
  -- Two identities do all the work: `δ = D √α` and `ρ α^{ν/2} = D`.
  have hsqrtα : Real.sqrt (α : ℝ) = (δ / ρ) ^ ((1 : ℝ) / (ν + 1)) := by
    rw [hαdef, Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
    congr 1
    field_simp
  have hsum1 : ν / (ν + 1) + (1 : ℝ) / (ν + 1) = 1 := by
    rw [← add_div, div_self hν1']
  have hmulρ : ∀ e : ℝ, ρ ^ e * (δ / ρ) ^ e = δ ^ e := by
    intro e
    rw [← Real.mul_rpow hρ.le ht.le, show ρ * (δ / ρ) = δ by field_simp]
  have hkey1 : D * Real.sqrt (α : ℝ) = δ := by
    calc D * Real.sqrt (α : ℝ)
        = δ ^ (ν / (ν + 1)) * (ρ ^ ((1 : ℝ) / (ν + 1)) * (δ / ρ) ^ ((1 : ℝ) / (ν + 1))) := by
          rw [hDdef, hsqrtα]; ring
      _ = δ ^ (ν / (ν + 1)) * δ ^ ((1 : ℝ) / (ν + 1)) := by rw [hmulρ]
      _ = δ := by rw [← Real.rpow_add hδ, hsum1, Real.rpow_one]
  have hδD : δ / Real.sqrt (α : ℝ) = D := by
    rw [div_eq_iff hsq0.ne']; exact hkey1.symm
  have hαν : (α : ℝ) ^ (ν / 2) = (δ / ρ) ^ (ν / (ν + 1)) := by
    rw [hαdef, ← Real.rpow_mul ht.le]
    congr 1
    field_simp
  have hkey2 : ρ * (α : ℝ) ^ (ν / 2) = D := by
    have hρsplit : ρ ^ ((1 : ℝ) / (ν + 1)) * ρ ^ (ν / (ν + 1)) = ρ := by
      rw [← Real.rpow_add hρ, show (1 : ℝ) / (ν + 1) + ν / (ν + 1) = 1 by
        rw [← add_div, show (1 : ℝ) + ν = ν + 1 by ring, div_self hν1'],
        Real.rpow_one]
    calc ρ * (α : ℝ) ^ (ν / 2)
        = (ρ ^ ((1 : ℝ) / (ν + 1)) * ρ ^ (ν / (ν + 1))) * (δ / ρ) ^ (ν / (ν + 1)) := by
          rw [hαν, hρsplit]
      _ = ρ ^ ((1 : ℝ) / (ν + 1)) * (ρ ^ (ν / (ν + 1)) * (δ / ρ) ^ (ν / (ν + 1))) := by ring
      _ = ρ ^ ((1 : ℝ) / (ν + 1)) * δ ^ (ν / (ν + 1)) := by rw [hmulρ]
      _ = D := by rw [hDdef]; ring
  have hterm1 : C₁ * (h * (‖y‖ + δ)) / (α : ℝ) ^ ((3 : ℝ) / 2) ≤ C₁ * D := by
    rw [div_le_iff₀ (by rw [hα32]; positivity)]
    refine (mul_le_mul_of_nonneg_left hsmall hC1).trans (le_of_eq ?_)
    rw [hα32, ← hkey1]
    ring
  have hterm2 : δ / (2 * Real.sqrt (α : ℝ)) = D / 2 := by
    rw [← hδD]; ring
  linarith

end AutoIp

end _cor_perturbed_rate
