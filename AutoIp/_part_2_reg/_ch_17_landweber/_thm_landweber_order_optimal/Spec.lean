/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_12_picard._def_source_set
public import AutoIp._part_2_reg._ch_13_regularization._def_discrepancy_principle
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_qualification
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_standard_filters
import AutoIp._part_2_reg._ch_15_spectral_regularization._thm_discrepancy_order_optimal
import AutoIp.Auxiliary.ExpBound
import AutoIp._part_2_reg._ch_17_landweber._thm_landweber_order_optimal.Helpers

section _thm_landweber_order_optimal

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- Condition (F) for the Landweber filter with `C = ω(1-ωκ)⁻¹`:
`sup_{λ ∈ (0,κ]} |φ_α(λ)| ≤ ω(1-ωκ)⁻¹ α⁻¹`.

The step size `ω ∈ (0, κ⁻¹)` is stated as `0 < ω` and `ωκ < 1`, which is the same for `K ≠ 0` and,
unlike the interval, makes no use of `0⁻¹`. It holds for every `K`, `K = 0` included. -/
public theorem landweberFilter_iSup_abs_le_inv_mul {𝕜 : Type*} [RCLike 𝕜] {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (K : E →L[𝕜] F) {ω : ℝ} (hω : 0 < ω ∧ ω * ‖K‖ ^ 2 < 1) {α : Set.Ioi (0 : ℝ)} :
    (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |landweberFilter ω α lam|) ≤
      ω * (1 - ω * ‖K‖ ^ 2)⁻¹ * (α : ℝ)⁻¹ := by
  have hα : (0 : ℝ) < (α : ℝ) := α.2
  obtain ⟨hω0, hprod⟩ := hω
  have hbound : (0:ℝ) ≤ ω * (1 - ω * ‖K‖ ^ 2)⁻¹ * (α : ℝ)⁻¹ := by
    have : (0:ℝ) < 1 - ω * ‖K‖ ^ 2 := by linarith
    positivity
  refine Real.iSup_le (fun lam => Real.iSup_le (fun hl => ?_) hbound) hbound
  exact landweberFilter_abs_le hω0 hprod hl

/-- Condition (Q_ν) for the Landweber filter at every `ν > 0`, with
`C_ν = (ν/(2ω))^(ν/2) e^(-ν/2)`: `ω_ν(α) ≤ C_ν α^(ν/2)`.

It is stated for any `κ` with `ωκ ≤ 1` in place of `‖K‖²`, and for every `α > 0`, not only
on `(0,κ]` as (Q_ν) asks. -/
public theorem landweberFilter_iSup_rpow_mul_residual_le {ω κ : ℝ} (hω0 : 0 < ω)
    (hprod : ω * κ ≤ 1) {ν : ℝ} (hν : 0 < ν) {α : Set.Ioi (0 : ℝ)} :
    (⨆ lam ∈ Set.Ioc (0 : ℝ) κ,
      lam ^ (ν / 2) * |1 - lam * landweberFilter ω α lam|) ≤
        (ν / (2 * ω)) ^ (ν / 2) * Real.exp (-ν / 2) * (α : ℝ) ^ (ν / 2) := by
  have hα : (0 : ℝ) < (α : ℝ) := α.2
  have hRHS : (0:ℝ) ≤ (ν / (2 * ω)) ^ (ν / 2) * Real.exp (-ν / 2) * (α : ℝ) ^ (ν / 2) := by
    positivity
  refine Real.iSup_le (fun lam => Real.iSup_le (fun hl => ?_) hRHS) hRHS
  obtain ⟨hl0, hlk⟩ := hl
  have hωlam : ω * lam ≤ ω * κ := by nlinarith
  have hbase : (0:ℝ) ≤ 1 - ω * lam := by linarith
  have hres : |1 - lam * landweberFilter ω α lam| = (1 - ω * lam) ^ ((1:ℝ) / (α : ℝ)) := by
    rw [landweberFilter_residual_eq (ne_of_gt hl0), abs_of_nonneg (Real.rpow_nonneg hbase _)]
  have hexp : (1 - ω * lam) ^ ((1:ℝ) / (α : ℝ)) ≤ Real.exp (-(ω / (α : ℝ) * lam)) := by
    have h1 : 1 - ω * lam ≤ Real.exp (-(ω * lam)) := by
      have := Real.add_one_le_exp (-(ω * lam)); linarith
    have h2 := Real.rpow_le_rpow hbase h1 (by positivity : (0:ℝ) ≤ 1 / (α : ℝ))
    rw [← Real.exp_mul] at h2
    calc (1 - ω * lam) ^ ((1:ℝ) / (α : ℝ)) ≤ Real.exp (-(ω * lam) * (1 / (α : ℝ))) := h2
      _ = Real.exp (-(ω / (α : ℝ) * lam)) := by ring_nf
  rw [hres]
  have hstep : lam ^ (ν / 2) * (1 - ω * lam) ^ ((1:ℝ) / (α : ℝ))
      ≤ lam ^ (ν / 2) * Real.exp (-(ω / (α : ℝ) * lam)) :=
    mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hl0.le _)
  refine hstep.trans ?_
  refine (rpow_mul_exp_neg_le (ω / (α : ℝ)) (ν / 2) lam (by positivity) (by positivity)
    hl0).trans (le_of_eq ?_)
  have hb : (ν / 2) / (ω / (α : ℝ)) = (ν / (2 * ω)) * (α : ℝ) := by field_simp
  rw [hb, Real.mul_rpow (by positivity) hα.le]
  ring_nf

/-- Landweber with the discrepancy principle, the conditions on the filter: the Landweber
filter satisfies (F) with `C = ω(1-ωκ)⁻¹`, and (Q_ν) for every `ν > 0` with
`C_ν = (ν/(2ω))^(ν/2) e^(-ν/2)`.

Neither the density of `Ran(K)` nor the hypothesis `dim Ran(K) = ∞` of the prose is needed.
The step size `ω ∈ (0, κ⁻¹)` is stated as `0 < ω` and `ωκ < 1`, which is the same for `K ≠ 0`
and, unlike the interval, makes no use of `0⁻¹`. It holds for every `K`, `K = 0` included. -/
public theorem landweberFilter_hasFilterBound_and_hasResidualBound {𝕜 : Type*} [RCLike 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] (K : E →L[𝕜] F) {ω : ℝ} (hω : 0 < ω ∧ ω * ‖K‖ ^ 2 < 1) :
    HasFilterBound K (landweberFilter ω) (ω * (1 - ω * ‖K‖ ^ 2)⁻¹) ∧
      ∀ ν > (0 : ℝ), HasResidualBound K (landweberFilter ω) ν
        ((ν / (2 * ω)) ^ (ν / 2) * Real.exp (-ν / 2)) := by
  obtain ⟨hω0, hωκ⟩ := hω
  have hfilt : IsRegularizingFilter K (landweberFilter ω) 1 :=
    landweberFilter_isRegularizingFilter K ⟨hω0, hωκ.le⟩
  have hpos : (0 : ℝ) < 1 - ω * ‖K‖ ^ 2 := by linarith
  exact ⟨⟨⟨1, hfilt⟩, by positivity, fun α => landweberFilter_iSup_abs_le_inv_mul K ⟨hω0, hωκ⟩⟩,
    fun ν hν => ⟨⟨1, hfilt⟩, by positivity,
      fun α _ => landweberFilter_iSup_rpow_mul_residual_le hω0 hωκ.le hν⟩⟩

/-- Landweber with the discrepancy principle, the qualification: the Landweber filter has
infinite qualification.

Neither the density of `Ran(K)` nor the hypothesis `dim Ran(K) = ∞` of the prose is needed.
The step size `ω ∈ (0, κ⁻¹)` is stated as `0 < ω` and `ωκ < 1`, which is the same for `K ≠ 0`
and, unlike the interval, makes no use of `0⁻¹`. It holds for every `K`, `K = 0` included. -/
public theorem qualification_landweberFilter_eq_top {𝕜 : Type*} [RCLike 𝕜] {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (K : E →L[𝕜] F) {ω : ℝ} (hω : 0 < ω ∧ ω * ‖K‖ ^ 2 < 1) :
    qualification K (landweberFilter ω) = (⊤ : ℝ≥0∞) := by
  -- every `ν > 0` is admissible, so the supremum clears every `b < ⊤`
  refine top_unique (le_of_forall_lt fun b hb => ?_)
  have hν : (0:ℝ) < b.toReal + 1 := by positivity
  calc b < ENNReal.ofReal (b.toReal + 1) := by
        rw [ENNReal.lt_ofReal_iff_toReal_lt hb.ne_top]; linarith
    _ ≤ _ := le_qualification K (landweberFilter ω) hν
        ⟨_, (landweberFilter_hasFilterBound_and_hasResidualBound K hω).2 _ hν⟩

/-- Landweber with the discrepancy principle, the residual constant: the Landweber filter has
`C_r = 1`.

Neither the density of `Ran(K)` nor the hypothesis `dim Ran(K) = ∞` of the prose is needed.
The step size `ω ∈ (0, κ⁻¹)` is stated as `0 < ω` and `ωκ < 1`, which is the same for `K ≠ 0`
and, unlike the interval, makes no use of `0⁻¹`. -/
public theorem iSup_abs_one_sub_mul_landweberFilter_eq_one {𝕜 : Type*} [RCLike 𝕜] {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    {K : E →L[𝕜] F} (hK : K ≠ 0) {ω : ℝ} (hω : 0 < ω ∧ ω * ‖K‖ ^ 2 < 1) :
    (⨆ a : Set.Ioi (0 : ℝ), ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
      |1 - lam * landweberFilter ω a lam|) = 1 := by
  obtain ⟨hω0, hωκ⟩ := hω
  have hκ : (0 : ℝ) < ‖K‖ ^ 2 := by positivity
  have hpt : ∀ (a : Set.Ioi (0 : ℝ)), ∀ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
      |1 - lam * landweberFilter ω a lam| ≤ 1 := by
    intro a lam hl
    exact landweberFilter_residual_abs_le_one hl.1 (by nlinarith [hl.1, hl.2]) hω0
  have hone : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.2 one_pos
  have hle : (⨆ a : Set.Ioi (0 : ℝ), ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
      |1 - lam * landweberFilter ω a lam|) ≤ 1 :=
    Real.iSup_le (fun a =>
      Real.iSup_le (fun lam => Real.iSup_le (fun hl => hpt a lam hl) zero_le_one)
        zero_le_one) zero_le_one
  refine le_antisymm hle ?_
  -- the inner supremum at `α = 1`, where the residual is `1 - ωλ → 1` as `λ → 0⁺`
  set S := ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |1 - lam * landweberFilter ω ⟨1, hone⟩ lam|
    with hSdef
  have hbddInner : BddAbove (Set.range (fun lam : ℝ =>
      ⨆ _ : lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
        |1 - lam * landweberFilter ω ⟨1, hone⟩ lam|)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨lam, rfl⟩
    exact Real.iSup_le (fun hl => hpt ⟨1, hone⟩ lam hl) zero_le_one
  have hSge : ∀ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), 1 - ω * lam ≤ S := by
    intro lam hl
    have h1 := le_ciSup hbddInner lam
    rw [ciSup_pos hl] at h1
    have heq : |1 - lam * landweberFilter ω ⟨1, hone⟩ lam| = 1 - ω * lam := by
      rw [landweberFilter_residual_eq (ne_of_gt hl.1), div_one, Real.rpow_one,
        abs_of_nonneg (by nlinarith [hl.1, hl.2] : (0:ℝ) ≤ 1 - ω * lam)]
    rw [heq] at h1
    exact h1
  have hS1 : (1:ℝ) ≤ S := by
    by_contra hc
    push Not at hc
    set lam := min (‖K‖ ^ 2) ((1 - S) / (2 * ω)) with hlamdef
    have hlam0 : 0 < lam := lt_min hκ (by positivity)
    have hlamk : lam ≤ ‖K‖ ^ 2 := min_le_left _ _
    have hlam2 : lam ≤ (1 - S) / (2 * ω) := min_le_right _ _
    have h := hSge lam ⟨hlam0, hlamk⟩
    have hhalf : ω * lam ≤ (1 - S) / 2 := by
      have h2 := mul_le_mul_of_nonneg_left hlam2 hω0.le
      rw [show ω * ((1 - S) / (2 * ω)) = (1 - S) / 2 by field_simp] at h2
      exact h2
    linarith
  have hbddOuter : BddAbove (Set.range (fun a : Set.Ioi (0 : ℝ) =>
      ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |1 - lam * landweberFilter ω a lam|)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact Real.iSup_le (fun lam => Real.iSup_le (fun hl => hpt a lam hl) zero_le_one)
      zero_le_one
  have h2 := le_ciSup hbddOuter ⟨1, hone⟩
  exact hS1.trans (le_trans (le_of_eq hSdef) h2)

/-- Landweber with the discrepancy principle, the consequence: if `Ran(K)` is dense in `Y`, for
every `τ > 1` the discrepancy principle defines a rule `α_τ`, `(R_α, α_τ)` is a convergent
regularization method, and for every `ν > 0` there is `c ≥ 1` with
`‖R_{α_τ(δ,y^δ)} y^δ - x†‖ ≤ c δ^(ν/(ν+1)) ρ^(1/(ν+1))` for every `ρ > 0`, `x† ∈ X_{ν,ρ}`,
`δ > 0` and `y^δ ∈ B_δ(K x†)` with `‖y^δ‖ > τ δ`.

The hypothesis `dim Ran(K) = ∞` of the prose is not needed.

The step size `ω ∈ (0, κ⁻¹)` is stated as `0 < ω` and `ωκ < 1`, which is the same for `K ≠ 0` and,
unlike the interval, makes no use of `0⁻¹`. -/
public theorem landweber_discrepancy_rate {𝕜 : Type*} [RCLike 𝕜] {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [CompleteSpace F] {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E}
    {u : ι → F} (hs : IsSingularSystem K σ v u) (hK : K ≠ 0) {ω : ℝ}
    (hω : 0 < ω ∧ ω * ‖K‖ ^ 2 < 1)
    (hdense : Dense (K.toLinearMap.range : Set F))
    {τ : ℝ} (hτ : 1 < τ) :
    ∃ a : ParameterChoice F,
      IsDiscrepancyPrinciple K (spectralReg hs (landweberFilter ω)
          (landweberFilter_exists_bound_on_spectrum hs ⟨hω.1, hω.2.le⟩)) τ a ∧
      IsRegularizationMethod K (fun α w => spectralReg hs (landweberFilter ω)
          (landweberFilter_exists_bound_on_spectrum hs ⟨hω.1, hω.2.le⟩) α w) a ∧
      ∀ (ν : ℝ) (hν : 0 < ν), ∃ c ≥ (1 : ℝ), ∀ (ρ : ℝ) (hρ : 0 < ρ), ∀ x ∈ sourceSet hs ν hν ρ hρ,
        ∀ (δ : ℝ) (hδ : 0 < δ), ∀ z : F, ‖z - K x‖ ≤ δ → τ * δ < ‖z‖ →
          ‖spectralReg hs (landweberFilter ω) (landweberFilter_exists_bound_on_spectrum hs
              ⟨hω.1, hω.2.le⟩) ((a).param ⟨δ, hδ⟩ z) z - x‖ ≤
            c * δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1)) := by
  obtain ⟨hω0, hωκ⟩ := id hω
  have hfilt : IsRegularizingFilter K (landweberFilter ω) 1 :=
    landweberFilter_isRegularizingFilter K ⟨hω0, hωκ.le⟩
  have hF : ∃ CF > (0 : ℝ), HasFilterBound K (landweberFilter ω) CF := by
    have hpos : (0:ℝ) < 1 - ω * ‖K‖ ^ 2 := by linarith
    exact ⟨_, by positivity, (landweberFilter_hasFilterBound_and_hasResidualBound K hω).1⟩
  have hQall : ∀ n : ℝ, 0 < n → ∃ Cn > (0 : ℝ), ∀ α : Set.Ioi (0 : ℝ),
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
        lam ^ (n / 2) * |1 - lam * landweberFilter ω α lam|) ≤ Cn * (α : ℝ) ^ (n / 2) :=
    fun n hn => ⟨(n / (2 * ω)) ^ (n / 2) * Real.exp (-n / 2), by positivity,
      fun α => landweberFilter_iSup_rpow_mul_residual_le hω0 hωκ.le hn⟩
  have hcont : ∀ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
      Continuous (fun a : Set.Ioi (0 : ℝ) => landweberFilter ω a lam) := by
    intro lam hl
    have hb : (0:ℝ) < 1 - ω * lam := by nlinarith [hl.1, hl.2]
    have heq : ∀ a : Set.Ioi (0 : ℝ), landweberFilter ω a lam
        = lam⁻¹ * (1 - Real.exp (Real.log (1 - ω * lam) * (1 / (a : ℝ)))) := by
      intro a
      rw [landweberFilter_of_ne_zero (ne_of_gt hl.1), Real.rpow_def_of_pos hb]
    have hne : ∀ a : Set.Ioi (0 : ℝ), (a : ℝ) ≠ 0 := fun a => (a.2 : (0:ℝ) < (a : ℝ)).ne'
    refine Continuous.congr ?_ fun a => (heq a).symm
    refine continuous_const.mul (continuous_const.sub ?_)
    refine Real.continuous_exp.comp ?_
    exact continuous_const.mul (continuous_const.div continuous_subtype_val hne)
  have hτ' : (⨆ a : Set.Ioi (0 : ℝ), ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
      |1 - lam * landweberFilter ω a lam|) < τ := by
    rw [iSup_abs_one_sub_mul_landweberFilter_eq_one hK hω]; exact hτ
  -- the rule is the same on all data the principle governs, whatever `ν₀` produced it
  have huniq : ∀ (a a' : ParameterChoice F),
      IsDiscrepancyPrinciple K (spectralReg hs (landweberFilter ω)
          (landweberFilter_exists_bound_on_spectrum hs ⟨hω.1, hω.2.le⟩)) τ a →
      IsDiscrepancyPrinciple K (spectralReg hs (landweberFilter ω)
          (landweberFilter_exists_bound_on_spectrum hs ⟨hω.1, hω.2.le⟩)) τ a' →
      ∀ (δ : ℝ) (hδ : 0 < δ), ∀ z : F, τ * δ < ‖z‖ →
        a' ⟨δ, hδ⟩ z = a ⟨δ, hδ⟩ z := by
    intro a a' ha ha' δ hδ z hz
    obtain ⟨h1, h2⟩ := ha.residual δ hδ z hz
    obtain ⟨h1', h2'⟩ := ha'.residual δ hδ z hz
    rcases lt_trichotomy (a' ⟨δ, hδ⟩ z) (a ⟨δ, hδ⟩ z) with h | h | h
    · exact absurd h1 (not_le.mpr (h2' _ h))
    · exact h
    · exact absurd h1' (not_le.mpr (h2 _ h))
  obtain ⟨a, hd, hm, -⟩ := discrepancy_rate_and_convergence hs hK hfilt hdense
    (ν₀ := 2) (by norm_num) hF
    (fun n hn => hQall n hn.1) hcont hτ'
  refine ⟨a, hd, hm, ?_⟩
  intro ν hν
  obtain ⟨a', hd', -, hr'⟩ := discrepancy_rate_and_convergence hs hK hfilt hdense
    (ν₀ := ν + 1) (by linarith) hF
    (fun n hn => hQall n hn.1) hcont hτ'
  obtain ⟨c, hc1, hc⟩ := hr' ν ⟨hν, by linarith⟩
  refine ⟨c, hc1, fun ρ hρ x hx δ hδ z hzx hzn => ?_⟩
  rw [← a'.param_congr (huniq a a' hd hd' δ hδ z hzn)]
  exact hc ρ hρ x hx δ hδ z hzx hzn

end AutoIp

end _thm_landweber_order_optimal
