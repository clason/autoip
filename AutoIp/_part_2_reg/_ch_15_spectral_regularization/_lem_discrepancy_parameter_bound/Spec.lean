/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_12_picard._def_source_set
public import AutoIp._part_2_reg._ch_13_regularization._def_discrepancy_principle
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_filter
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
import AutoIp._part_2_reg._ch_11_moore_penrose._thm_mp_inverse
import AutoIp._part_2_reg._ch_12_picard._lem_source_in_kerperp
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_omega_nu
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_residual_constant

section _lem_discrepancy_parameter_bound

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- The discrepancy parameter is bounded below: let the regularizing filter satisfy (Q_ν) for all
`ν ∈ (0, ν₀]`, let `τ > C_r`, and let `α_τ` satisfy the discrepancy principle with tolerance `τ`.
Then for every `ν ∈ (0, ν₀ − 1]` there is `c_{τ,ν} > 0` such that
`α_τ(δ, y^δ) ≥ c_{τ,ν} (δ/ρ)^{2/(ν+1)}` for all `ρ > 0`, `x† ∈ X_{ν,ρ}`, `δ > 0` and
`y^δ ∈ B_δ(Kx†)` with `‖y^δ‖ > τδ`. Of the hypotheses of the order-optimality theorem for the
discrepancy principle only these and `K ≠ 0` are assumed, and `ν₀` need not be the qualification.
(Q_ν) is asked for every `α > 0` rather than on `(0, κ]`, which for a regularizing filter changes
only the constant. -/
public theorem discrepancy_param_ge (hs : IsSingularSystem K σ v u) (hK : K ≠ 0)
    {φ : Set.Ioi (0 : ℝ) → ℝ → ℝ} {Cφ : ℝ} (hφ : IsRegularizingFilter K φ Cφ)
    {ν₀ : ℝ}
    (hQ : ∀ ν ∈ Set.Ioc (0 : ℝ) ν₀, ∃ Cν > (0 : ℝ), ∀ α : Set.Ioi (0 : ℝ),
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), lam ^ (ν / 2) * |1 - lam * φ α lam|) ≤
        Cν * (α : ℝ) ^ (ν / 2))
    {τ : ℝ}
    (hτ : (⨆ a : Set.Ioi (0 : ℝ), ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
      |1 - lam * φ a lam|) < τ)
    (a : ParameterChoice F) (ha : IsDiscrepancyPrinciple K (spectralReg hs φ
        (hφ.exists_bound_on_spectrum hs)) τ a) :
    ∀ (ν : ℝ) (hν : ν ∈ Set.Ioc (0 : ℝ) (ν₀ - 1)), ∃ c > (0 : ℝ), ∀ (ρ : ℝ) (hρ : 0 < ρ),
      ∀ x ∈ sourceSet hs ν hν.1 ρ hρ, ∀ (δ : ℝ) (hδ : 0 < δ), ∀ z : F,
        ‖z - K x‖ ≤ δ → τ * δ < ‖z‖ →
        c * (δ / ρ) ^ (2 / (ν + 1)) ≤ a ⟨δ, hδ⟩ z := by
  intro ν hν
  obtain ⟨hν0, hνle⟩ := hν
  have hν1 : (0 : ℝ) < ν + 1 := by linarith
  set Cr := ⨆ b : Set.Ioi (0 : ℝ), ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
      |1 - lam * φ b lam| with hCrdef
  obtain ⟨hCr1, hCrle, hresid⟩ := one_le_iSup_abs_one_sub_mul_and_norm_residual_le hs hK hφ
  obtain ⟨C1, hC10, hC1⟩ := hQ (ν + 1) ⟨by linarith, by linarith⟩
  have hτCr : (0 : ℝ) < τ - Cr := by linarith
  have h2p : (0 : ℝ) < (2 : ℝ) ^ ((ν + 1) / 2) := Real.rpow_pos_of_pos two_pos _
  set A := (τ - Cr) / ((2 : ℝ) ^ ((ν + 1) / 2) * C1) with hAdef
  have hA0 : 0 < A := div_pos hτCr (by positivity)
  refine ⟨A ^ (2 / (ν + 1)), Real.rpow_pos_of_pos hA0 _, ?_⟩
  intro ρ hρ x hx δ hδ z hzx hzn
  set α := a ⟨δ, hδ⟩ z with hαdef
  have hα : 0 < α := a.pos ⟨δ, hδ⟩ z
  have h2α : (0 : ℝ) < 2 * α := by linarith
  set β : Set.Ioi (0 : ℝ) := ⟨2 * α, Set.mem_Ioi.2 h2α⟩ with hβdef
  have hβ : (β : ℝ) = 2 * α := rfl
  have hxperp : x ∈ (K.toLinearMap.ker)ᗮ := sourceSet_subset_orthogonal_ker hs hν0 hρ hx
  have hmp : moorePenrose K ⟨K x, Submodule.mem_sup_left ⟨x,
      rfl⟩⟩ = x := moorePenrose_apply_apply_of_mem_orthogonal hxperp
  have hymem : (K x : F) ∈ mpDomain K := Submodule.mem_sup_left ⟨x, rfl⟩
  have hxsrc : moorePenrose K ⟨K x, Submodule.mem_sup_left ⟨x,
      rfl⟩⟩ ∈ sourceSet hs ν hν0 ρ hρ := by rw [hmp]; exact hx
  obtain ⟨-, hgt⟩ := ha.residual δ hδ z hzn
  have hgt2 := hgt β (by rw [hβ]; linarith)
  have he : K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β z) - z
      = (K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β (K x)) - K x)
        - ((z - K x) - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β (z - K x))) := by
    have hlin : spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β z
        = spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β (K
            x) + spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β (z - K x) := by
      rw [← map_add]; congr 1; abel
    rw [hlin, map_add]; abel
  have hnoise : ‖(z - K x) - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β (z - K
      x))‖ ≤ Cr * δ := by
    refine (hresid (z - K x) β).trans ?_
    exact mul_le_mul_of_nonneg_left hzx (by linarith)
  have hsplit : ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β z) - z‖
      ≤ ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β (K x)) - K x‖ + Cr * δ := by
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith)
  obtain ⟨-, hom⟩ :=
    norm_spectralReg_sub_moorePenrose_le (α := β) hs hφ hν0 hρ hymem hxsrc
  rw [hmp] at hom
  have hom2 : ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β (K x)) - K x‖
      ≤ C1 * (2 * α) ^ ((ν + 1) / 2) * ρ := by
    refine hom.trans ?_
    exact mul_le_mul_of_nonneg_right (hC1 β) hρ.le
  have hpow : ((2 : ℝ) * α) ^ ((ν + 1) / 2)
      = (2 : ℝ) ^ ((ν + 1) / 2) * α ^ ((ν + 1) / 2) :=
    Real.mul_rpow (by norm_num) hα.le
  rw [hpow] at hom2
  have hkey : (τ - Cr) * δ < C1 * ((2 : ℝ) ^ ((ν + 1) / 2) * α ^ ((ν + 1) / 2)) * ρ := by
    nlinarith [hgt2, hsplit, hom2]
  have hAlt : A * (δ / ρ) ≤ α ^ ((ν + 1) / 2) := by
    rw [hAdef, div_mul_div_comm, div_le_iff₀ (by positivity)]
    nlinarith [hkey]
  have hq : (0 : ℝ) ≤ 2 / (ν + 1) := by positivity
  have hstep := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ A * (δ / ρ)) hAlt hq
  have hr : (α ^ ((ν + 1) / 2)) ^ (2 / (ν + 1)) = α := by
    rw [← Real.rpow_mul hα.le,
      show ((ν + 1) / 2) * (2 / (ν + 1)) = 1 by field_simp, Real.rpow_one]
  have hl : (A * (δ / ρ)) ^ (2 / (ν + 1))
      = A ^ (2 / (ν + 1)) * (δ / ρ) ^ (2 / (ν + 1)) :=
    Real.mul_rpow hA0.le (by positivity)
  rw [hr, hl] at hstep
  exact hstep

end AutoIp

end _lem_discrepancy_parameter_bound
