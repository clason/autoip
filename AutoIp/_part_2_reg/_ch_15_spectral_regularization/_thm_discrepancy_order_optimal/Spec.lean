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
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_qualification
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_abs_norm
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._thm_interpolation
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_domain_dense
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_equations
import AutoIp._part_2_reg._ch_11_moore_penrose._thm_mp_inverse
import AutoIp._part_2_reg._ch_12_picard._lem_source_in_kerperp
import AutoIp._part_2_reg._ch_13_regularization._lem_error_decomposition
import AutoIp._part_2_reg._ch_13_regularization._thm_discrepancy_well_defined
import Mathlib.Topology.Order.AtTopBotIxx
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_approx_error_spectral
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_discrepancy_parameter_bound
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_filter_norm_bound
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_filter_residual_bound
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_residual_constant
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_spectral_residual_form
import AutoIp._part_2_reg._ch_15_spectral_regularization._thm_apriori_order_optimal
import AutoIp._part_2_reg._ch_15_spectral_regularization._thm_spectral_is_regularization
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import AutoIp.Auxiliary.Rpow

section _thm_discrepancy_order_optimal

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

set_option maxHeartbeats 2000000 in
-- The bump is measured, not guessed: at Lean's default 200000 this declaration times out
-- three times over, in `linarith`'s simplex and in `whnf`, and it still fails at 1000000.
-- The threshold is between 1000000 and 1200000; 2000000 leaves roughly the same headroom
-- again, because a heartbeat count drifts with the Mathlib pin and a limit set to the
-- measured minimum is one that the next bump breaks.
/-- Rate and convergence for the discrepancy principle: let `Ran(K)` be dense in `Y`, let the
regularizing filter satisfy (F) and (Q_ν) for all `ν ∈ (0, ν₀]` with `ν₀ > 1`, let
`α ↦ φ_α(λ)` be continuous on `(0,∞)` for each `λ ∈ (0, κ]`, and let `τ > C_r`. Then there is
a rule `α_τ` satisfying the discrepancy principle with tolerance `τ`, and (rate) for every
`ν ∈ (0, ν₀ − 1]` there is `c ≥ 1`, not depending on `ρ`, with
`‖R_{α_τ(δ,y^δ)} y^δ − x†‖ ≤ c δ^{ν/(ν+1)} ρ^{1/(ν+1)}` for every `ρ > 0`, `x† ∈ X_{ν,ρ}`,
`δ > 0` and `y^δ ∈ B_δ(Kx†)` with `‖y^δ‖ > τδ`; (convergence) `(R_α, α_τ)` is a convergent
regularization method. The hypothesis `dim Ran(K) = ∞` is not assumed, and `ν₀` need not be
the qualification. (Q_ν) is asked for every `α > 0` rather than on `(0, κ]`, which for a
regularizing filter changes only the constant. -/
public theorem discrepancy_rate_and_convergence (hs : IsSingularSystem K σ v u) (hK : K ≠ 0)
    {φ : Set.Ioi (0 : ℝ) → ℝ → ℝ} {Cφ : ℝ} (hφ : IsRegularizingFilter K φ Cφ)
    (hdense : Dense (K.toLinearMap.range : Set F))
    {ν₀ : ℝ} (hν₀ : 1 < ν₀)
    (hF : ∃ CF > (0 : ℝ), HasFilterBound K φ CF)
    (hQ : ∀ ν ∈ Set.Ioc (0 : ℝ) ν₀, ∃ Cν > (0 : ℝ), ∀ α : Set.Ioi (0 : ℝ),
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), lam ^ (ν / 2) * |1 - lam * φ α lam|) ≤
        Cν * (α : ℝ) ^ (ν / 2))
    (hcont : ∀ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
      Continuous (fun a : Set.Ioi (0 : ℝ) => φ a lam))
    {τ : ℝ}
    (hτ : (⨆ a : Set.Ioi (0 : ℝ), ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
      |1 - lam * φ a lam|) < τ) :
    ∃ a : ParameterChoice F, IsDiscrepancyPrinciple K (spectralReg hs φ
        (hφ.exists_bound_on_spectrum hs)) τ a ∧
      IsRegularizationMethod K (fun α w => spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α
          w) a ∧
      ∀ (ν : ℝ) (hν : ν ∈ Set.Ioc (0 : ℝ) (ν₀ - 1)), ∃ c ≥ (1 : ℝ), ∀ (ρ : ℝ) (hρ : 0 < ρ),
        ∀ x ∈ sourceSet hs ν hν.1 ρ hρ, ∀ (δ : ℝ) (hδ : 0 < δ), ∀ z : F, ‖z - K x‖ ≤ δ →
          τ * δ < ‖z‖ →
          ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) ((a).param ⟨δ, hδ⟩ z) z - x‖ ≤
            c * δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1)) := by
  classical
  obtain ⟨CF, hCF0, hCF⟩ := id hF
  have hKn : ‖K‖ ≠ 0 := norm_ne_zero_iff.mpr hK
  have hκ : (0 : ℝ) < ‖K‖ ^ 2 := by positivity
  have hCφ0 : (0 : ℝ) < Cφ := hφ.const_pos
  obtain ⟨hCr1, hCrle, hresid⟩ := one_le_iSup_abs_one_sub_mul_and_norm_residual_le hs hK hφ
  set Cr := ⨆ a : Set.Ioi (0 : ℝ), ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
      |1 - lam * φ a lam| with hCrdef
  have hτraw : (⨆ b : Set.Ioi (0 : ℝ), ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
      |1 - lam * φ b lam|) < τ := by rw [← hCrdef]; exact hτ
  have hτ1 : (1 : ℝ) < τ := lt_of_le_of_lt hCr1 hτ
  have hτ0 : (0 : ℝ) < τ := by linarith
  have hCr0 : (0 : ℝ) ≤ Cr := by linarith
  -- two elementary facts about squares, kept out of the heavy contexts below
  have hsqle : ∀ p q : ℝ, 0 ≤ p → 0 ≤ q → p ^ 2 ≤ q ^ 2 → p ≤ q := by
    intro p q hp hq h
    nlinarith
  have hsqlt : ∀ p q : ℝ, 0 ≤ p → 0 < q → p ^ 2 < q ^ 2 → p < q := by
    intro p q hp hq h
    nlinarith
  set B := 1 + Cφ with hBdef
  have hB1 : (1 : ℝ) ≤ B := by rw [hBdef]; linarith
  have hB0 : (0 : ℝ) ≤ B := by linarith
  have hBub : ∀ (b : Set.Ioi (0 : ℝ)), ∀ s ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2),
      |1 - s * φ b s| ≤ B :=
    fun _ _ hsm => abs_one_sub_mul_le_one_add hφ hsm
  -- The parameter of the family is positive, but the search below runs over the reals, so
  -- the proof reads the family through `ψ`, which agrees with it at every parameter.
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ → ℝ → ℝ,
      ∀ (a : ℝ) (ha : 0 < a), ψ a = φ ⟨a, Set.mem_Ioi.2 ha⟩ :=
    ⟨fun a => if h : 0 < a then φ ⟨a, Set.mem_Ioi.2 h⟩ else 0, fun _ ha => by simp [ha]⟩
  have hψ' : ∀ a : Set.Ioi (0 : ℝ), ψ (a : ℝ) = φ a := fun a => hψ (a : ℝ) a.2
  have hBsq : ∀ b : ℝ, 0 < b → ∀ i : ι,
      |1 - σ i ^ 2 * ψ b (σ i ^ 2)| ^ 2 ≤ B ^ 2 := by
    intro b hb i
    rw [hψ b hb]
    have h := hBub ⟨b, Set.mem_Ioi.2 hb⟩ _ (hs.sq_mem_Icc i)
    have h0 := abs_nonneg (1 - σ i ^ 2 * φ ⟨b, Set.mem_Ioi.2 hb⟩ (σ i ^ 2))
    nlinarith
  have hφpt : ∀ a > (0 : ℝ), ∀ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |ψ a lam| ≤ CF * a⁻¹ := by
    intro a ha lam hlam
    rw [hψ a ha]
    obtain ⟨Bd, hBd⟩ := hφ.bddOn ⟨a, ha⟩
    have hbdd : BddAbove (Set.range (fun s : ℝ =>
        ⨆ _ : s ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |φ ⟨a, Set.mem_Ioi.2 ha⟩ s|)) := by
      refine ⟨max Bd 0, ?_⟩
      rintro _ ⟨s, rfl⟩
      exact Real.iSup_le (fun h => le_trans (hBd s ⟨h.1.le, h.2⟩) (le_max_left _ _))
        (le_max_right _ _)
    have h1 := le_ciSup hbdd lam
    rw [ciSup_pos hlam] at h1
    exact h1.trans (hCF.iSup_le ⟨a, Set.mem_Ioi.2 ha⟩)
  have hQpt : ∀ n : ℝ, 0 < n → ∀ Cn : ℝ,
      (∀ b : Set.Ioi (0 : ℝ), (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
        lam ^ (n / 2) * |1 - lam * φ b lam|) ≤ Cn * (b : ℝ) ^ (n / 2)) →
      ∀ b > (0 : ℝ), ∀ i : ι,
        (σ i ^ 2) ^ (n / 2) * |1 - σ i ^ 2 * ψ b (σ i ^ 2)| ≤ Cn * b ^ (n / 2) := by
    intro n hn Cn hCn b hb i
    rw [hψ b hb]
    have hbdd : BddAbove (Set.range (fun lam : ℝ =>
        ⨆ _ : lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
          lam ^ (n / 2) * |1 - lam * φ ⟨b, Set.mem_Ioi.2 hb⟩ lam|)) := by
      refine ⟨(‖K‖ ^ 2) ^ (n / 2) * B, ?_⟩
      rintro _ ⟨lam, rfl⟩
      refine Real.iSup_le (fun h => ?_)
        (mul_nonneg (Real.rpow_nonneg hκ.le _) hB0)
      exact mul_le_mul (Real.rpow_le_rpow h.1.le h.2 (by positivity))
        (hBub ⟨b, Set.mem_Ioi.2 hb⟩ lam ⟨h.1.le, h.2⟩) (abs_nonneg _)
        (Real.rpow_nonneg hκ.le _)
    have h1 := le_ciSup hbdd (σ i ^ 2)
    rw [ciSup_pos (show σ i ^ 2 ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2) from
      ⟨pow_pos (hs.pos i) 2, (hs.sq_mem_Icc i).2⟩)] at h1
    exact h1.trans (hCn ⟨b, Set.mem_Ioi.2 hb⟩)
  -- The residual depends on the parameter only through `φ a`, so it is a function of a
  -- *real* parameter -- which is where its continuity, and the search below, live.
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : F → ℝ → ℝ, ∀ (z : F) (a : ℝ), Θ z a =
      Real.sqrt
        (‖z - K.toLinearMap.range.topologicalClosure.starProjection z‖ ^ 2
          + ∑' i, |1 - σ i ^ 2 * ψ a (σ i ^ 2)| ^ 2 * ‖(inner 𝕜 (u i) z : 𝕜)‖ ^ 2) :=
    ⟨_, fun _ _ => rfl⟩
  have hthetaeq : ∀ (z : F) (a : Set.Ioi (0 : ℝ)),
      ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) a z) - z‖ = Θ z (a : ℝ) := by
    intro z a
    obtain ⟨-, hr, hn⟩ := hasSum_starProjection_sub_apply_spectralReg_and_norm_sq (α := a) hs
      (hφ.exists_bound_on_spectrum hs) z
    rw [← hr.tsum_eq] at hn
    rw [hΘ, hψ' a, norm_sub_rev, ← hn, Real.sqrt_sq (norm_nonneg _)]
  have hthetaeq' : ∀ (z : F) (a : Set.Ioi (0 : ℝ)),
      ‖z - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) a z)‖ = Θ z (a : ℝ) := by
    intro z a
    rw [norm_sub_rev, hthetaeq]
  have hΘnn : ∀ (z : F) (a : ℝ), (0 : ℝ) ≤ Θ z a := fun z a => by rw [hΘ]; positivity
  have hbess : ∀ z : F, Summable (fun i => ‖(inner 𝕜 (u i) z : 𝕜)‖ ^ 2) :=
    fun z => hs.orthonormal_right.inner_products_summable (x := z)
  have hsumres : ∀ (z : F) (a : ℝ), 0 < a → Summable (fun i =>
      |1 - σ i ^ 2 * ψ a (σ i ^ 2)| ^ 2 * ‖(inner 𝕜 (u i) z : 𝕜)‖ ^ 2) := by
    intro z a ha
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
      ((hbess z).mul_left (B ^ 2))
    exact mul_le_mul_of_nonneg_right (hBsq a ha i) (sq_nonneg _)
  have hψcont : ∀ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
      ContinuousOn (fun a : ℝ => ψ a lam) (Set.Ioi (0 : ℝ)) := by
    intro lam hlam
    rw [continuousOn_iff_continuous_domRestrict]
    exact (hcont lam hlam).congr fun a => (congrFun (hψ' a) lam).symm
  have hthetacont : ∀ z : F, ContinuousOn (Θ z) (Set.Ioi (0 : ℝ)) := by
    intro z
    have hsum : Summable (fun i => B ^ 2 * ‖(inner 𝕜 (u i) z : 𝕜)‖ ^ 2) := (hbess z).mul_left _
    have hg : ContinuousOn
        (fun a => ∑' i, |1 - σ i ^ 2 * ψ a (σ i ^ 2)| ^ 2 * ‖(inner 𝕜 (u i) z : 𝕜)‖ ^ 2)
        (Set.Ioi (0 : ℝ)) := by
      refine continuousOn_tsum (u := fun i => B ^ 2 * ‖(inner 𝕜 (u i) z : 𝕜)‖ ^ 2)
        (fun i => ?_) hsum (fun i a ha => ?_)
      · exact ContinuousOn.mul
          (ContinuousOn.pow (ContinuousOn.abs (continuousOn_const.sub
            (continuousOn_const.mul
              (hψcont (σ i ^ 2) ⟨pow_pos (hs.pos i) 2, (hs.sq_mem_Icc i).2⟩)))) 2)
          continuousOn_const
      · rw [Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_right (hBsq a ha i) (sq_nonneg _)
    have hsq : ContinuousOn (fun a =>
        Real.sqrt (‖z - K.toLinearMap.range.topologicalClosure.starProjection z‖ ^ 2
          + ∑' i, |1 - σ i ^ 2 * ψ a (σ i ^ 2)| ^ 2 * ‖(inner 𝕜 (u i) z : 𝕜)‖ ^ 2))
        (Set.Ioi (0 : ℝ)) :=
      Real.continuous_sqrt.comp_continuousOn (continuousOn_const.add hg)
    exact hsq.congr (fun a _ => hΘ z a)
  have hreg : IsRegularization K (spectralReg hs φ (hφ.exists_bound_on_spectrum
      hs)) := isRegularization_spectralReg hs hφ
  have hbddK : ∃ C : ℝ, ∀ a : Set.Ioi (0 :
      ℝ), ‖K ∘L spectralReg hs φ (hφ.exists_bound_on_spectrum hs) a‖ ≤ C := by
    refine ⟨Cφ, fun a => ?_⟩
    obtain ⟨h1, h2⟩ := opNorm_comp_spectralReg_le (α := a) hs hφ
    linarith
  have hexists : ∀ (δ : ℝ) (z : F), ∃ a : ℝ, 0 < a ∧
      ((0 < δ ∧ τ * δ < ‖z‖) →
        (Θ z a ≤ τ * δ ∧ ∀ b > a, τ * δ < Θ z b)) ∧
      (¬ (0 < δ ∧ τ * δ < ‖z‖) → a = 1) := by
    intro δ z
    by_cases hgood : 0 < δ ∧ τ * δ < ‖z‖
    · obtain ⟨hδ, hzn⟩ := hgood
      have hz0 : (0 : ℝ) < ‖z‖ := lt_trans (mul_pos hτ0 hδ) hzn
      have hzne : ‖z‖ ≠ 0 := hz0.ne'
      set S := {a : ℝ | 0 < a ∧ Θ z a ≤ τ * δ} with hSdef
      have hSmem : ∀ a : ℝ, a ∈ S ↔ (0 < a ∧ Θ z a ≤ τ * δ) := fun a => Iff.rfl
      have hSsub : S ⊆ Set.Ioi (0 : ℝ) := fun a ha => ((hSmem a).mp ha).1
      have hSne : S.Nonempty := by
        obtain ⟨grid, hgrid⟩ : ∃ grid : ℕ → Set.Ioi (0 : ℝ),
            ∀ n : ℕ, (grid n : ℝ) = ((n : ℝ) + 1)⁻¹ :=
          ⟨fun n => ⟨((n : ℝ) + 1)⁻¹, Set.mem_Ioi.2 (by positivity)⟩, fun _ => rfl⟩
        have hcoe : Tendsto (fun n : ℕ => (grid n : ℝ)) atTop (𝓝[>] (0 : ℝ)) := by
          refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
            (Eventually.of_forall fun n => (grid n).2)
          have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
            simpa only [one_div] using h0
          exact h.congr fun n => (hgrid n).symm
        have hnull : Tendsto grid atTop atBot := by
          have hcomap : comap ((↑) : Set.Ioi (0 : ℝ) → ℝ) (𝓝[>] (0 : ℝ)) = atBot :=
            comap_coe_Ioi_nhdsGT (0 : ℝ)
          rw [← hcomap]
          exact tendsto_comap_iff.2 hcoe
        obtain ⟨n, hn, -⟩ := exists_discrepancy_index hreg hdense hbddK hnull hτ0 hδ z
        rw [hthetaeq z (grid n)] at hn
        exact ⟨(grid n : ℝ), (hSmem _).mpr ⟨(grid n).2, hn⟩⟩
      set t := (τ * δ + ‖z‖) / 2 with htdef
      have htlo : τ * δ < t := by rw [htdef]; linarith
      have hthi : t < ‖z‖ := by rw [htdef]; linarith
      have ht0 : (0 : ℝ) < t := lt_trans (mul_pos hτ0 hδ) htlo
      set A := ‖K‖ ^ 2 * CF * ‖z‖ / (‖z‖ - t) with hAdef
      have hSbdd : ∀ a ∈ S, a ≤ A := by
        intro a ha
        obtain ⟨ha0, ha2⟩ := (hSmem a).mp ha
        by_contra hcon
        push Not at hcon
        have haz : (0 : ℝ) < a * ‖z‖ := mul_pos ha0 hz0
        have hpw : ‖K‖ ^ 2 * CF * ‖z‖ < a * (‖z‖ - t) := by
          rw [hAdef, div_lt_iff₀ (by linarith : (0 : ℝ) < ‖z‖ - t)] at hcon
          linarith
        have h2 : ‖K‖ ^ 2 * (CF * a⁻¹) < (‖z‖ - t) / ‖z‖ := by
          refine lt_of_mul_lt_mul_right ?_ haz.le
          have e1 : ‖K‖ ^ 2 * (CF * a⁻¹) * (a * ‖z‖) = ‖K‖ ^ 2 * CF * ‖z‖ := by
            field_simp
          have e2 : (‖z‖ - t) / ‖z‖ * (a * ‖z‖) = a * (‖z‖ - t) := by
            field_simp
          rw [e1, e2]
          exact hpw
        have htz0 : (0 : ℝ) ≤ t / ‖z‖ := div_nonneg ht0.le (norm_nonneg _)
        have hkey : ∀ i : ι, (t / ‖z‖) ^ 2 ≤ |1 - σ i ^ 2 * ψ a (σ i ^ 2)| ^ 2 := by
          intro i
          have hmem : σ i ^ 2 ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2) :=
            ⟨pow_pos (hs.pos i) 2, (hs.sq_mem_Icc i).2⟩
          have h1 : σ i ^ 2 * ψ a (σ i ^ 2) ≤ ‖K‖ ^ 2 * (CF * a⁻¹) := by
            calc σ i ^ 2 * ψ a (σ i ^ 2) ≤ σ i ^ 2 * |ψ a (σ i ^ 2)| :=
                  mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
              _ ≤ ‖K‖ ^ 2 * (CF * a⁻¹) :=
                  mul_le_mul hmem.2 (hφpt a ha0 _ hmem) (abs_nonneg _) (by positivity)
          have hdd : (‖z‖ - t) / ‖z‖ = 1 - t / ‖z‖ := by field_simp
          have h3 : t / ‖z‖ < 1 - σ i ^ 2 * ψ a (σ i ^ 2) := by linarith
          have h4 : t / ‖z‖ ≤ |1 - σ i ^ 2 * ψ a (σ i ^ 2)| := le_trans h3.le (le_abs_self _)
          nlinarith
        obtain ⟨-, hr, hres6⟩ :=
          hasSum_starProjection_sub_apply_spectralReg_and_norm_sq
            (α := ⟨a, Set.mem_Ioi.2 ha0⟩) hs
            (hφ.exists_bound_on_spectrum hs) z
        rw [← hr.tsum_eq] at hres6
        obtain ⟨hc, hres7⟩ := hasSum_norm_sq_inner_starProjection_range hs z
        rw [← hc.tsum_eq] at hres7
        rw [← hψ a ha0] at hres6
        have hge : (t / ‖z‖) ^ 2 * ∑' i, ‖(inner 𝕜 (u i) z : 𝕜)‖ ^ 2
            ≤ ∑' i, |1 - σ i ^ 2 * ψ a (σ i ^ 2)| ^ 2 * ‖(inner 𝕜 (u i) z : 𝕜)‖ ^ 2 := by
          rw [← tsum_mul_left]
          refine Summable.tsum_le_tsum (fun i => ?_) ((hbess z).mul_left _) (hsumres z a ha0)
          exact mul_le_mul_of_nonneg_right (hkey i) (sq_nonneg _)
        have hk0 : (0 : ℝ) ≤ (t / ‖z‖) ^ 2 := sq_nonneg _
        have hk1 : (t / ‖z‖) ^ 2 ≤ 1 := by
          have h : t / ‖z‖ ≤ 1 := by rw [div_le_one hz0]; linarith
          nlinarith
        have hN0 : (0 : ℝ) ≤
            ‖z - K.toLinearMap.range.topologicalClosure.starProjection z‖ ^ 2 :=
          sq_nonneg _
        have he1 : ‖z‖ ^ 2 * (t / ‖z‖) ^ 2 = t ^ 2 := by field_simp
        have harith : ∀ N Sc Sr k w T : ℝ, 0 ≤ N → 0 ≤ k → k ≤ 1 → k * Sc ≤ Sr →
            w = N + Sc → T = N + Sr → w * k = t ^ 2 → t ^ 2 ≤ T := by
          intro N Sc Sr k w T hN hk0' hk1' hks hw hT he
          nlinarith
        have hfinal : t ^ 2 ≤ ‖z - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) ⟨a,
            Set.mem_Ioi.2 ha0⟩ z)‖ ^ 2 :=
          harith _ _ _ _ _ _ hN0 hk0 hk1 hge hres7 hres6 he1
        have hle : t ≤ Θ z a := by
          rw [← hthetaeq' z ⟨a, Set.mem_Ioi.2 ha0⟩]
          exact hsqle _ _ ht0.le (norm_nonneg _) hfinal
        linarith
      have hbdd' : BddAbove S := ⟨A, hSbdd⟩
      have has0 : 0 < sSup S := by
        obtain ⟨s0, hs0⟩ := hSne
        exact lt_of_lt_of_le ((hSmem s0).mp hs0).1 (le_csSup hbdd' hs0)
      refine ⟨sSup S, has0, fun _ => ⟨?_, ?_⟩, fun h => absurd ⟨hδ, hzn⟩ h⟩
      · have hcl : sSup S ∈ closure S := csSup_mem_closure hSne hbdd'
        have hcw : ContinuousWithinAt (Θ z) S (sSup S) :=
          ((hthetacont z) (sSup S) has0).mono hSsub
        have him := hcw.mem_closure_image hcl
        have hsubs : (Θ z) '' S ⊆ Set.Iic (τ * δ) := by
          rintro _ ⟨b, hb, rfl⟩
          exact ((hSmem b).mp hb).2
        have hfin := closure_mono hsubs him
        rwa [isClosed_Iic.closure_eq] at hfin
      · intro b hb
        by_contra hcon
        push Not at hcon
        exact absurd (le_csSup hbdd' ((hSmem b).mpr ⟨lt_trans has0 hb, hcon⟩)) (not_le.mpr hb)
    · exact ⟨1, one_pos, fun h => absurd h hgood, fun _ => rfl⟩
  choose fα hfα0 hfα1 hfα2 using hexists
  set aRule : ParameterChoice F :=
    ⟨fun δ z => fα (δ : ℝ) z, fun δ z => hfα0 (δ : ℝ) z⟩ with haRuledef
  have hred : ∀ (δ : Set.Ioi (0 : ℝ)) (z : F), aRule δ z = fα (δ : ℝ) z := fun _ _ => rfl
  have hDP : IsDiscrepancyPrinciple K (spectralReg hs φ (hφ.exists_bound_on_spectrum
      hs)) τ aRule := by
    refine ⟨hτ1, fun δ hδ z hzn => ?_⟩
    obtain ⟨h1, h2⟩ := hfα1 δ z ⟨hδ, hzn⟩
    refine ⟨?_, fun α hα => ?_⟩
    · rw [hthetaeq z (aRule.param ⟨δ, hδ⟩ z)]
      exact h1
    · rw [hthetaeq z α]
      exact h2 (α : ℝ) hα
  refine ⟨aRule, hDP, ?_, ?_⟩
  · have hclos : K.toLinearMap.range.topologicalClosure = ⊤ :=
      Submodule.dense_iff_topologicalClosure_eq_top.mp hdense
    have hPid : ∀ p : F,
        K.toLinearMap.range.topologicalClosure.starProjection p = p :=
      fun p => Submodule.starProjection_eq_self_iff.mpr (by rw [hclos]; exact Submodule.mem_top)
    have hresidcmp : ∀ (β : Set.Ioi (0 : ℝ)) (p q : F),
        Θ p (β : ℝ) ≤ Θ q (β : ℝ) + Cr * ‖p - q‖ := by
      intro β p q
      rw [← hthetaeq' p β, ← hthetaeq' q β]
      exact norm_residual_le_add hs hK hφ le_rfl p q
    obtain ⟨D1, hD10, hD1⟩ := hQ 1 ⟨one_pos, hν₀.le⟩
    set ν₁ := min 2 ν₀ with hν₁def
    have hν₁1 : (1 : ℝ) < ν₁ := lt_min (by norm_num) hν₀
    have hν₁0 : (0 : ℝ) < ν₁ := by linarith
    obtain ⟨D2, hD20, hD2⟩ := hQ ν₁ ⟨hν₁0, min_le_right _ _⟩
    have hQ1pt : ∀ b > (0 : ℝ), ∀ i,
        σ i * |1 - σ i ^ 2 * ψ b (σ i ^ 2)| ≤ D1 * Real.sqrt b := by
      intro b hb i
      have h := hQpt 1 one_pos D1 hD1 b hb i
      rwa [hs.rpow_sq_half i,
        show (b ^ ((1 : ℝ) / 2) : ℝ) = Real.sqrt b from (Real.sqrt_eq_rpow b).symm] at h
    have hwle : ∀ b > (0 : ℝ), ∀ i,
        σ i * |1 - σ i ^ 2 * ψ b (σ i ^ 2)| / Real.sqrt b ≤ D1 := by
      intro b hb i
      rw [div_le_iff₀ (Real.sqrt_pos.mpr hb)]
      exact hQ1pt b hb i
    have hrpow0 : Tendsto (fun b : ℝ => b ^ ((ν₁ - 1) / 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : ContinuousAt (fun b : ℝ => b ^ ((ν₁ - 1) / 2)) 0 :=
        Real.continuousAt_rpow_const 0 ((ν₁ - 1) / 2) (Or.inr (by linarith))
      have h := hc.tendsto
      rw [Real.zero_rpow (by intro hcon; nlinarith : ((ν₁ - 1) / 2 : ℝ) ≠ 0)] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hwlim : ∀ i, Tendsto
        (fun b => σ i * |1 - σ i ^ 2 * ψ b (σ i ^ 2)| / Real.sqrt b) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      intro i
      have hσ0 : (0 : ℝ) < σ i := hs.pos i
      have hsp : (0 : ℝ) < (σ i ^ 2) ^ (ν₁ / 2) := Real.rpow_pos_of_pos (pow_pos hσ0 2) _
      refine squeeze_zero'
        (g := fun b : ℝ => σ i * D2 / (σ i ^ 2) ^ (ν₁ / 2) * b ^ ((ν₁ - 1) / 2)) ?_ ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with b hb
        exact div_nonneg (mul_nonneg hσ0.le (abs_nonneg _)) (Real.sqrt_nonneg _)
      · filter_upwards [self_mem_nhdsWithin] with b hb
        have hb' : (0 : ℝ) < b := hb
        have hsb : (0 : ℝ) < Real.sqrt b := Real.sqrt_pos.mpr hb'
        have h := hQpt ν₁ hν₁0 D2 hD2 b hb' i
        have hbe : b ^ ((ν₁ - 1) / 2) * Real.sqrt b = b ^ (ν₁ / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add hb']
          congr 1
          ring
        rw [div_le_iff₀ hsb]
        have hrw : σ i * D2 / (σ i ^ 2) ^ (ν₁ / 2) * b ^ ((ν₁ - 1) / 2) * Real.sqrt b
            = σ i * (D2 * b ^ (ν₁ / 2)) / (σ i ^ 2) ^ (ν₁ / 2) := by
          rw [mul_assoc, hbe]
          field_simp
        rw [hrw, le_div_iff₀ hsp]
        have h2 := mul_le_mul_of_nonneg_left h hσ0.le
        nlinarith [h2]
      · have := hrpow0.const_mul (σ i * D2 / (σ i ^ 2) ^ (ν₁ / 2))
        simpa using this
    intro y hy ε hε
    have hKx : K (moorePenrose K ⟨y, hy⟩) = y := by rw [apply_moorePenrose ⟨_, hy⟩, hPid]
    have hcoef : ∀ i, (inner 𝕜 (u i) y : 𝕜)
        = (RCLike.ofReal (σ i) : 𝕜) * inner 𝕜 (v i) (moorePenrose K ⟨y, hy⟩) := by
      intro i
      conv_lhs => rw [← hKx]
      rw [← ContinuousLinearMap.adjoint_inner_left, hs.map_right i, inner_smul_left,
        RCLike.conj_ofReal]
    have hbessx : Summable (fun i => ‖(inner 𝕜 (v i) (moorePenrose K ⟨y, hy⟩) : 𝕜)‖ ^ 2) :=
      hs.orthonormal_left.inner_products_summable (x := moorePenrose K ⟨y, hy⟩)
    have happrox : ∀ β : Set.Ioi (0 : ℝ),
        ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β y - moorePenrose K ⟨y, hy⟩‖ ^ 2
        = ∑' i, |1 - σ i ^ 2 * ψ (β : ℝ) (σ i ^ 2)| ^ 2
            * ‖(inner 𝕜 (v i) (moorePenrose K ⟨y, hy⟩) : 𝕜)‖ ^ 2 := by
      intro β
      obtain ⟨-, hsum⟩ := moorePenrose_sub_spectralReg_eq_funCalc (α := β) hs hφ hy
      rw [hψ' β, ← norm_neg, neg_sub, hs.orthonormal_left.norm_sq_eq_tsum_norm_sq hsum]
      refine tsum_congr fun i => ?_
      rw [norm_mul, RCLike.norm_ofReal, mul_pow]
    have hTheta : ∀ β > (0 : ℝ), Θ y β ^ 2
        = ∑' i, (σ i * |1 - σ i ^ 2 * ψ β (σ i ^ 2)|) ^ 2
            * ‖(inner 𝕜 (v i) (moorePenrose K ⟨y, hy⟩) : 𝕜)‖ ^ 2 := by
      intro β hβ
      obtain ⟨-, hr, h6⟩ :=
        hasSum_starProjection_sub_apply_spectralReg_and_norm_sq
          (α := ⟨β, Set.mem_Ioi.2 hβ⟩) hs
          (hφ.exists_bound_on_spectrum hs) y
      rw [← hr.tsum_eq] at h6
      rw [← hψ β hβ] at h6
      have hzz : ‖y -
          K.toLinearMap.range.topologicalClosure.starProjection y‖ ^ 2 = 0 := by
        rw [hPid]; simp
      rw [← hthetaeq' y ⟨β, Set.mem_Ioi.2 hβ⟩, h6, hzz, zero_add]
      refine tsum_congr fun i => ?_
      rw [hcoef i, norm_mul, RCLike.norm_ofReal, abs_of_pos (hs.pos i)]
      ring
    have hsumapp : ∀ β > (0 : ℝ), Summable (fun i =>
        |1 - σ i ^ 2 * ψ β (σ i ^ 2)| ^ 2
          * ‖(inner 𝕜 (v i) (moorePenrose K ⟨y, hy⟩) : 𝕜)‖ ^ 2) := by
      intro β hβ
      refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
        (hbessx.mul_left (B ^ 2))
      exact mul_le_mul_of_nonneg_right (hBsq β hβ i) (sq_nonneg _)
    have hsumTheta : ∀ β > (0 : ℝ), Summable (fun i =>
        (σ i * |1 - σ i ^ 2 * ψ β (σ i ^ 2)|) ^ 2
          * ‖(inner 𝕜 (v i) (moorePenrose K ⟨y, hy⟩) : 𝕜)‖ ^ 2) := by
      intro β hβ
      refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
        (hbessx.mul_left (‖K‖ ^ 2 * B ^ 2))
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have he : (σ i * |1 - σ i ^ 2 * ψ β (σ i ^ 2)|) ^ 2
          = σ i ^ 2 * |1 - σ i ^ 2 * ψ β (σ i ^ 2)| ^ 2 := by ring
      rw [he]
      exact mul_le_mul (hs.sq_mem_Icc i).2 (hBsq β hβ i) (sq_nonneg _) (by positivity)
    have hΘratio : ∀ b > (0 : ℝ),
        (Θ y b / Real.sqrt b) ^ 2
          = ∑' i, (σ i * |1 - σ i ^ 2 * ψ b (σ i ^ 2)| / Real.sqrt b) ^ 2
              * ‖(inner 𝕜 (v i) (moorePenrose K ⟨y, hy⟩) : 𝕜)‖ ^ 2 := by
      intro b hb
      rw [div_pow, hTheta b hb, div_eq_mul_inv, ← tsum_mul_right]
      refine tsum_congr fun i => ?_
      rw [div_pow, div_eq_mul_inv]
      ring
    have hratio0 : Tendsto (fun b => (Θ y b / Real.sqrt b) ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hdom := tendsto_tsum_of_dominated_convergence
        (𝓕 := 𝓝[>] (0 : ℝ))
        (f := fun (b : ℝ) (i : ι) =>
          (σ i * |1 - σ i ^ 2 * ψ b (σ i ^ 2)| / Real.sqrt b) ^ 2
            * ‖(inner 𝕜 (v i) (moorePenrose K ⟨y, hy⟩) : 𝕜)‖ ^ 2)
        (g := fun _ : ι => (0 : ℝ))
        (bound := fun i => D1 ^ 2 * ‖(inner 𝕜 (v i) (moorePenrose K ⟨y, hy⟩) : 𝕜)‖ ^ 2)
        (hbessx.mul_left _)
        (fun i => by
          have hp := ((hwlim i).pow 2).mul_const
            (‖(inner 𝕜 (v i) (moorePenrose K ⟨y, hy⟩) : 𝕜)‖ ^ 2)
          simpa using hp)
        (by
          filter_upwards [self_mem_nhdsWithin] with b hb i
          have hb' : (0 : ℝ) < b := hb
          have h0 : (0 : ℝ) ≤ σ i * |1 - σ i ^ 2 * ψ b (σ i ^ 2)| / Real.sqrt b :=
            div_nonneg (mul_nonneg (hs.pos i).le (abs_nonneg _)) (Real.sqrt_nonneg _)
          have h1 := hwle b hb' i
          rw [Real.norm_of_nonneg (by positivity)]
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          nlinarith)
      have hdom0 : Tendsto (fun b => ∑' i,
          (σ i * |1 - σ i ^ 2 * ψ b (σ i ^ 2)| / Real.sqrt b) ^ 2
            * ‖(inner 𝕜 (v i) (moorePenrose K ⟨y, hy⟩) : 𝕜)‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa using hdom
      refine hdom0.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with b hb
      exact (hΘratio b hb).symm
    have hΘ0 : Tendsto (fun b => Θ y b / Real.sqrt b)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hratio0
      rw [Real.sqrt_zero] at h
      refine h.congr fun b => ?_
      simp only [Function.comp_apply]
      rw [Real.sqrt_sq (div_nonneg (hΘnn y b) (Real.sqrt_nonneg b))]
    by_cases hy0 : y = 0
    · subst hy0
      have hx0 : moorePenrose K ⟨(0 : F), hy⟩ = 0 :=
        (moorePenrose_eq_zero_iff ⟨_, hy⟩).mpr (Submodule.zero_mem _)
      have hnn : (0 : ℝ) ≤ ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) ⟨1, Set.mem_Ioi.2
          one_pos⟩‖ := norm_nonneg _
      refine ⟨ε / (‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) ⟨1, Set.mem_Ioi.2 one_pos⟩‖
          + 1), by positivity, ?_⟩
      intro δ hδ z hz
      have hzn : ‖z‖ ≤ δ := by simpa using hz
      have hbad : ¬ (0 < δ ∧ τ * δ < ‖z‖) := by
        rintro ⟨-, h⟩
        nlinarith [hδ.1, mul_pos (by linarith : (0 : ℝ) < τ - 1) hδ.1]
      have hone : aRule.param ⟨δ, hδ.1⟩ z = ⟨1, Set.mem_Ioi.2 one_pos⟩ :=
        Subtype.ext (hfα2 δ z hbad)
      rw [hone, hx0]
      have hδlt : δ < ε / (‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) ⟨1, Set.mem_Ioi.2
          one_pos⟩‖ + 1) := hδ.2
      rw [lt_div_iff₀ (by linarith)] at hδlt
      calc ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) ⟨1, Set.mem_Ioi.2 one_pos⟩ z - 0‖
          = ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) ⟨1, Set.mem_Ioi.2
              one_pos⟩ z‖ := by rw [sub_zero]
        _ ≤ ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) ⟨1, Set.mem_Ioi.2 one_pos⟩‖ * ‖z‖ :=
            (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) ⟨1, Set.mem_Ioi.2
                one_pos⟩).le_opNorm z
        _ ≤ ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) ⟨1, Set.mem_Ioi.2 one_pos⟩‖ * δ :=
            mul_le_mul_of_nonneg_left hzn hnn
        _ < ε := by nlinarith [hδ.1]
    · have hyn0 : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy0
      have hτCr : (0 : ℝ) < τ - Cr := by linarith
      set S0 := Real.sqrt (Cφ * CF) with hS0def
      have hS00 : (0 : ℝ) < S0 := Real.sqrt_pos.mpr (by positivity)
      have hεq : (0 : ℝ) < (ε / 4) ^ 2 / (B ^ 2 + 1) := by positivity
      obtain ⟨J, hJ⟩ : ∃ J : Finset ι,
          ∑' i : {i // i ∉ J}, ‖(inner 𝕜 (v (i : ι)) (moorePenrose K ⟨y, hy⟩) : 𝕜)‖ ^ 2
            < (ε / 4) ^ 2 / (B ^ 2 + 1) :=
        ((tendsto_tsum_compl_atTop_zero
          (fun i => ‖(inner 𝕜 (v i) (moorePenrose K ⟨y, hy⟩) : 𝕜)‖ ^ 2)).eventually
          (gt_mem_nhds hεq)).exists
      set TJ := ∑' i : {i // i ∉ J}, ‖(inner 𝕜 (v (i : ι)) (moorePenrose K ⟨y, hy⟩) : 𝕜)‖ ^ 2
        with hTJdef
      set W := ∑ i ∈ J, (σ i ^ 2)⁻¹ with hWdef
      have hW0 : (0 : ℝ) ≤ W := Finset.sum_nonneg (fun i _ => by positivity)
      have hTJ0 : (0 : ℝ) ≤ TJ := by
        rw [hTJdef]
        exact tsum_nonneg (fun i => sq_nonneg _)
      have hBpart : ∀ β : Set.Ioi (0 : ℝ),
          ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β y - moorePenrose K ⟨y, hy⟩‖ ^ 2
          ≤ W * Θ y (β : ℝ) ^ 2 + B ^ 2 * TJ := by
        intro β
        have hβ : (0 : ℝ) < (β : ℝ) := β.2
        rw [happrox β, ← (hsumapp (β : ℝ) hβ).sum_add_tsum_subtype_compl J]
        have h1 : ∑ i ∈ J, |1 - σ i ^ 2 * ψ (β : ℝ) (σ i ^ 2)| ^ 2
              * ‖(inner 𝕜 (v i) (moorePenrose K ⟨y, hy⟩) : 𝕜)‖ ^ 2
            ≤ W * Θ y (β : ℝ) ^ 2 := by
          rw [hWdef, Finset.sum_mul]
          refine Finset.sum_le_sum (fun i _ => ?_)
          have hσ : (0 : ℝ) < σ i ^ 2 := pow_pos (hs.pos i) 2
          have hterm : (σ i * |1 - σ i ^ 2 * ψ (β : ℝ) (σ i ^ 2)|) ^ 2
              * ‖(inner 𝕜 (v i) (moorePenrose K ⟨y, hy⟩) : 𝕜)‖ ^ 2
              ≤ Θ y (β : ℝ) ^ 2 := by
            rw [hTheta (β : ℝ) hβ]
            exact (hsumTheta (β : ℝ) hβ).le_tsum i (fun j _ => by positivity)
          rw [inv_mul_eq_div, le_div_iff₀ hσ]
          nlinarith [hterm]
        have h2 : ∑' i : {i // i ∉ J},
              |1 - σ (i : ι) ^ 2 * ψ (β : ℝ) (σ (i : ι) ^ 2)| ^ 2
              * ‖(inner 𝕜 (v (i : ι)) (moorePenrose K ⟨y, hy⟩) : 𝕜)‖ ^ 2
            ≤ B ^ 2 * TJ := by
          rw [hTJdef, ← tsum_mul_left]
          refine Summable.tsum_le_tsum (fun i => ?_) ((hsumapp (β : ℝ) hβ).subtype _)
            ((hbessx.mul_left (B ^ 2)).subtype _)
          exact mul_le_mul_of_nonneg_right (hBsq (β : ℝ) hβ (i : ι)) (sq_nonneg _)
        linarith
      set η := (τ - Cr) * (ε / 4) / (Real.sqrt 2 * S0) with hηdef
      have hη0 : (0 : ℝ) < η := by
        rw [hηdef]
        have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
        positivity
      have hev := hΘ0.eventually (gt_mem_nhds hη0)
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
      obtain ⟨β₀, hβ₀0, hβ₀⟩ := hev
      set R2 := Real.sqrt (β₀ / 2) with hR2def
      have hR20 : (0 : ℝ) < R2 := Real.sqrt_pos.mpr (by linarith)
      refine ⟨min (min (‖y‖ / (1 + τ)) (ε / (4 * (Real.sqrt W * (τ + Cr) + 1))))
        (ε * R2 / (4 * S0)), ?_, ?_⟩
      · have h1 : (0 : ℝ) < ‖y‖ / (1 + τ) := by positivity
        have h2 : (0 : ℝ) < ε / (4 * (Real.sqrt W * (τ + Cr) + 1)) := by
          have : (0 : ℝ) ≤ Real.sqrt W * (τ + Cr) :=
            mul_nonneg (Real.sqrt_nonneg _) (by linarith)
          positivity
        have h3 : (0 : ℝ) < ε * R2 / (4 * S0) := by positivity
        exact lt_min (lt_min h1 h2) h3
      intro δ hδ z hz
      obtain ⟨hδ0, hδlt⟩ := hδ
      have hd1 : δ < ‖y‖ / (1 + τ) := lt_of_lt_of_le hδlt (le_trans (min_le_left _ _)
        (min_le_left _ _))
      have hd2 : δ < ε / (4 * (Real.sqrt W * (τ + Cr) + 1)) :=
        lt_of_lt_of_le hδlt (le_trans (min_le_left _ _) (min_le_right _ _))
      have hd3 : δ < ε * R2 / (4 * S0) := lt_of_lt_of_le hδlt (min_le_right _ _)
      have hzn : τ * δ < ‖z‖ := by
        have h2 : ‖y‖ - ‖z‖ ≤ ‖y - z‖ := norm_sub_norm_le y z
        rw [lt_div_iff₀ (by linarith : (0 : ℝ) < 1 + τ)] at hd1
        linarith
      obtain ⟨α, hαval⟩ : ∃ α : Set.Ioi (0 : ℝ), (α : ℝ) = fα δ z :=
        ⟨⟨_, Set.mem_Ioi.2 (hfα0 δ z)⟩, rfl⟩
      have hpar : aRule.param ⟨δ, hδ0⟩ z = α := Subtype.ext hαval.symm
      rw [hpar]
      have hα : (0 : ℝ) < (α : ℝ) := α.2
      obtain ⟨hresle, hresgt⟩ := hfα1 δ z ⟨hδ0, hzn⟩
      rw [← hαval] at hresle hresgt
      have hzy : ‖y - z‖ ≤ δ := hz
      have hΘα : Θ y (α : ℝ) ≤ (τ + Cr) * δ := by
        have h := hresidcmp α y z
        nlinarith [mul_le_mul_of_nonneg_left hzy hCr0, hresle]
      have hAbound : ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y - moorePenrose K ⟨y,
          hy⟩‖ < ε / 2 := by
        have hsqW : Real.sqrt W * (τ + Cr) * δ < ε / 4 := by
          have hpp : (0 : ℝ) ≤ Real.sqrt W * (τ + Cr) :=
            mul_nonneg (Real.sqrt_nonneg _) (by linarith)
          rw [lt_div_iff₀ (by linarith : (0 : ℝ) < 4 * (Real.sqrt W * (τ + Cr) + 1))] at hd2
          nlinarith [hδ0, hd2]
        have hb1 : W * Θ y (α : ℝ) ^ 2 ≤ (Real.sqrt W * (τ + Cr) * δ) ^ 2 := by
          have h1 : Θ y (α : ℝ) ^ 2 ≤ ((τ + Cr) * δ) ^ 2 := by
            nlinarith [hΘnn y (α : ℝ), hΘα,
              mul_nonneg (by linarith : (0 : ℝ) ≤ τ + Cr) hδ0.le]
          have hexp : (Real.sqrt W * (τ + Cr) * δ) ^ 2 = W * ((τ + Cr) * δ) ^ 2 := by
            rw [mul_pow, mul_pow, Real.sq_sqrt hW0]
            ring
          rw [hexp]
          exact mul_le_mul_of_nonneg_left h1 hW0
        have hb2 : B ^ 2 * TJ < (ε / 4) ^ 2 := by
          have hBB : (0 : ℝ) < B ^ 2 + 1 := by positivity
          rw [lt_div_iff₀ hBB] at hJ
          nlinarith [hTJ0, hJ]
        have hsq2 : (Real.sqrt W * (τ + Cr) * δ) ^ 2 < (ε / 4) ^ 2 := by
          have hnn : (0 : ℝ) ≤ Real.sqrt W * (τ + Cr) * δ :=
            mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith)) hδ0.le
          nlinarith [hsqW, hnn]
        have hfin : ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y - moorePenrose K ⟨y,
            hy⟩‖ ^ 2 < (ε / 2) ^ 2 := by
          have h := hBpart α
          nlinarith [hb1, hb2, hsq2, mul_pos hε hε]
        exact hsqlt _ _ (norm_nonneg _) (by linarith) hfin
      have hΦ0 : (0 : ℝ) ≤ ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |φ α lam| :=
        Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _
      have hRnorm : ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α‖ ≤ S0 * Real.sqrt (α :
          ℝ)⁻¹ := by
        rw [hS0def]
        exact opNorm_spectralReg_le_sqrt hs hφ hCF0.le (hCF.iSup_le α)
      have hsα : (0 : ℝ) < Real.sqrt (α : ℝ) := Real.sqrt_pos.mpr hα
      have hdataerr : δ * ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α‖ < ε / 4 := by
        have hkey : δ / Real.sqrt (α : ℝ) < ε / (4 * S0) := by
          by_cases hcase : 2 * (α : ℝ) < β₀
          · have h2α : (0 : ℝ) < 2 * (α : ℝ) := by linarith
            have hdist : dist (2 * (α : ℝ)) (0 : ℝ) < β₀ := by
              rw [Real.dist_eq, sub_zero, abs_of_pos h2α]
              exact hcase
            have hlt := hβ₀ hdist h2α
            have hgt := hresgt (2 * (α : ℝ)) (by linarith)
            have hcmp := hresidcmp ⟨2 * (α : ℝ), Set.mem_Ioi.2 h2α⟩ z y
            have hΘ2 : (τ - Cr) * δ < Θ y (2 * (α : ℝ)) := by
              have h2 : ‖z - y‖ ≤ δ := by rw [norm_sub_rev]; exact hzy
              linarith [mul_le_mul_of_nonneg_left h2 hCr0]
            have hs2 : Real.sqrt (2 * (α : ℝ)) = Real.sqrt 2 * Real.sqrt (α : ℝ) :=
              Real.sqrt_mul (by norm_num) (α : ℝ)
            have hs20 : (0 : ℝ) < Real.sqrt (2 * (α : ℝ)) := Real.sqrt_pos.mpr h2α
            rw [div_lt_iff₀ hs20] at hlt
            rw [div_lt_iff₀ hsα]
            have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
            have hS0ne : S0 ≠ 0 := hS00.ne'
            have h2ne : Real.sqrt 2 ≠ 0 := hsqrt2.ne'
            have hτCrne : τ - Cr ≠ 0 := hτCr.ne'
            have hηs : η * Real.sqrt 2 / (τ - Cr) = ε / (4 * S0) := by
              rw [hηdef]
              field_simp
            have hstep : (τ - Cr) * δ < η * (Real.sqrt 2 * Real.sqrt (α : ℝ)) := by
              rw [← hs2]; linarith
            have hfinal : δ < η * Real.sqrt 2 / (τ - Cr) * Real.sqrt (α : ℝ) := by
              rw [div_mul_eq_mul_div, lt_div_iff₀ hτCr]
              nlinarith [hstep]
            rw [hηs] at hfinal
            exact hfinal
          · push Not at hcase
            have hR2le : R2 ≤ Real.sqrt (α : ℝ) := by
              rw [hR2def]
              exact Real.sqrt_le_sqrt (by linarith)
            rw [lt_div_iff₀ (by linarith : (0 : ℝ) < 4 * S0)] at hd3
            have h5 : ε * R2 ≤ ε * Real.sqrt (α : ℝ) :=
              mul_le_mul_of_nonneg_left hR2le hε.le
            rw [div_lt_iff₀ hsα, div_mul_eq_mul_div,
              lt_div_iff₀ (by linarith : (0 : ℝ) < 4 * S0)]
            linarith [hd3, h5]
        have hrw : Real.sqrt (α : ℝ)⁻¹ = (Real.sqrt (α : ℝ))⁻¹ := Real.sqrt_inv (α : ℝ)
        calc δ * ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α‖ ≤ δ * (S0 * Real.sqrt (α :
            ℝ)⁻¹) :=
              mul_le_mul_of_nonneg_left hRnorm hδ0.le
          _ = S0 * (δ / Real.sqrt (α : ℝ)) := by rw [hrw]; field_simp
          _ < S0 * (ε / (4 * S0)) := mul_lt_mul_of_pos_left hkey hS00
          _ = ε / 4 := by field_simp
      have hsplit := norm_sub_moorePenrose_le (T := K) (spectralReg hs φ
          (hφ.exists_bound_on_spectrum hs)) (α := α) hy hz
      linarith
  · intro ν hν
    obtain ⟨hν0, hνle⟩ := hν
    have hν1 : (0 : ℝ) < ν + 1 := by linarith
    obtain ⟨cA, hcA0, hcA⟩ :=
      discrepancy_param_ge hs hK hφ hQ hτraw aRule hDP ν ⟨hν0, hνle⟩
    set C1 := (τ + Cr) ^ (ν / (ν + 1)) * B ^ ((1 : ℝ) / (ν + 1)) with hC1def
    set C2 := Real.sqrt (Cφ * CF) * cA ^ (-(1 : ℝ) / 2) with hC2def
    have hC10 : (0 : ℝ) ≤ C1 :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hB0 _)
    have hC20 : (0 : ℝ) ≤ C2 :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hcA0.le _)
    refine ⟨max 1 (C1 + C2), le_max_left _ _, ?_⟩
    intro ρ hρ x hx δ hδ z hzx hzn
    obtain ⟨α, hαval⟩ : ∃ α : Set.Ioi (0 : ℝ), (α : ℝ) = fα δ z :=
      ⟨⟨_, Set.mem_Ioi.2 (hfα0 δ z)⟩, rfl⟩
    have hαlow : cA * (δ / ρ) ^ (2 / (ν + 1)) ≤ (α : ℝ) := by
      rw [hαval, ← hred ⟨δ, hδ⟩]; exact hcA ρ hρ x hx δ hδ z hzx hzn
    have hpar : aRule.param ⟨δ, hδ⟩ z = α := Subtype.ext hαval.symm
    rw [hpar]
    have hα : (0 : ℝ) < (α : ℝ) := α.2
    have ht : (0 : ℝ) < δ / ρ := div_pos hδ hρ
    have hrho := rpow_split_rate hρ hν1
    have key1 : δ * (δ / ρ) ^ (-(1 : ℝ) / (ν + 1)) =
        δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1)) := by
      have h1 : (δ / ρ) ^ (-(1 : ℝ) / (ν + 1))
          = δ ^ (-(1 : ℝ) / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1)) := by
        rw [Real.div_rpow hδ.le hρ.le, div_eq_mul_inv]
        congr 1
        rw [show (-(1 : ℝ) / (ν + 1)) = -((1 : ℝ) / (ν + 1)) by ring, Real.rpow_neg hρ.le,
          inv_inv]
      rw [h1, ← mul_assoc]
      congr 1
      nth_rewrite 1 [← Real.rpow_one δ]
      rw [← Real.rpow_add hδ]
      congr 1
      field_simp
      ring
    have hxperp : x ∈ (K.toLinearMap.ker)ᗮ := sourceSet_subset_orthogonal_ker hs hν0 hρ hx
    have hxmem : K x ∈ mpDomain K := Submodule.mem_sup_left ⟨x, rfl⟩
    have hmp : moorePenrose K ⟨K x, hxmem⟩ = x :=
      moorePenrose_apply_apply_of_mem_orthogonal hxperp
    have hymem : (K x : F) ∈ mpDomain K := Submodule.mem_sup_left ⟨x, rfl⟩
    obtain ⟨w, hwρ, hw⟩ := (mem_sourceSet_iff _ _ _ _ _).1 hx
    have hwn : ‖w‖ ≤ ρ := hwρ
    obtain ⟨hresle, -⟩ := hfα1 δ z ⟨hδ, hzn⟩
    have hnoise : ‖(K x - z) - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α (K x -
        z))‖ ≤ Cr * δ := by
      refine (hresid (K x - z) α).trans ?_
      have hle : ‖K x - z‖ ≤ δ := by rw [norm_sub_rev]; exact hzx
      exact mul_le_mul_of_nonneg_left hle hCr0
    have hAres : ‖K x - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α (K x))‖ ≤ (τ +
        Cr) * δ := by
      have he : K x - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α (K x))
          = (z - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z))
            + ((K x - z) - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α (K x - z))) := by
        have hlin : spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α (K x)
            = spectralReg hs φ (hφ.exists_bound_on_spectrum
                hs) α z + spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α (K x - z) := by
          rw [← map_add]; congr 1; abel
        rw [hlin, map_add]; abel
      rw [he]
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖z - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z)‖ ≤ τ * δ := by
        rw [hthetaeq' z α, hαval]; exact hresle
      linarith
    obtain ⟨ξ, hξB, hkey0⟩ := exists_norm_le_and_sub_eq_absRpow (α := α) hs hφ hB1 hBub hν0
      hymem (hw.trans hmp.symm)
    rw [hmp] at hkey0
    have hkey : x - spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α (K
        x) = hs.absRpow ν hν0.le ξ := hkey0
    have hξn : ‖ξ‖ ≤ B * ρ := hξB.trans (mul_le_mul_of_nonneg_left hwn hB0)
    have hnu1 : ‖hs.absRpow (ν + 1) (by linarith : (0:ℝ) ≤ ν + 1) ξ‖
        = ‖K x - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α (K x))‖ := by
      rw [hs.absRpow_congr (show ν + 1 = 1 + ν by ring) (by linarith) (by linarith),
        hs.absRpow_add one_pos hν0,
        ContinuousLinearMap.comp_apply, hs.norm_absRpow_one_apply_eq_norm_map, ← hkey, map_sub]
    have hexp : 1 - ν / (ν + 1) = 1 / (ν + 1) := by field_simp; ring
    have hinterp := hs.norm_absRpow_le_rpow_mul_rpow hν0.le (by linarith : ν < ν + 1) ξ
    rw [hexp, hnu1] at hinterp
    have hA : ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α (K x) - x‖
        ≤ C1 * (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))) := by
      have hrev : ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α (K
          x) - x‖ = ‖hs.absRpow ν hν0.le ξ‖ := by
        rw [← hkey, norm_sub_rev]
      rw [hrev]
      refine hinterp.trans ?_
      have h1 : ‖K x - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α (K x))‖ ^ (ν / (ν +
          1))
          ≤ ((τ + Cr) * δ) ^ (ν / (ν + 1)) :=
        Real.rpow_le_rpow (norm_nonneg _) hAres (by positivity)
      have h2 : ‖ξ‖ ^ (1 / (ν + 1)) ≤ (B * ρ) ^ ((1 : ℝ) / (ν + 1)) :=
        Real.rpow_le_rpow (norm_nonneg _) hξn (by positivity)
      have h3 : ((τ + Cr) * δ) ^ (ν / (ν + 1)) * (B * ρ) ^ ((1 : ℝ) / (ν + 1))
          = C1 * (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))) := by
        rw [Real.mul_rpow (by linarith) hδ.le, Real.mul_rpow hB0 hρ.le, hC1def]
        ring
      calc ‖K x - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α (K x))‖ ^ (ν / (ν +
          1)) * ‖ξ‖ ^ (1 / (ν + 1))
          ≤ ((τ + Cr) * δ) ^ (ν / (ν + 1)) * (B * ρ) ^ ((1 : ℝ) / (ν + 1)) :=
            mul_le_mul h1 h2 (Real.rpow_nonneg (norm_nonneg _) _)
              (Real.rpow_nonneg (by positivity) _)
        _ = C1 * (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))) := h3
    have hΦ0 : (0 : ℝ) ≤ ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |φ α lam| :=
      Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _
    have hRnorm : ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α‖ ≤ Real.sqrt (Cφ *
        CF) * Real.sqrt (α : ℝ)⁻¹ :=
      opNorm_spectralReg_le_sqrt hs hφ hCF0.le (hCF.iSup_le α)
    have hsqrtinv :
        Real.sqrt (α : ℝ)⁻¹ ≤ cA ^ (-(1 : ℝ) / 2) * (δ / ρ) ^ (-(1 : ℝ) / (ν + 1)) := by
      have hT : (0 : ℝ) < (δ / ρ) ^ (2 / (ν + 1)) := Real.rpow_pos_of_pos ht _
      have hprod : (0 : ℝ) < cA * (δ / ρ) ^ (2 / (ν + 1)) := by positivity
      have hinv : (α : ℝ)⁻¹ ≤ (cA * (δ / ρ) ^ (2 / (ν + 1)))⁻¹ := inv_anti₀ hprod hαlow
      refine (Real.sqrt_le_sqrt hinv).trans_eq ?_
      rw [mul_inv, Real.sqrt_mul (by positivity)]
      congr 1
      · rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring, Real.rpow_neg hcA0.le,
          ← Real.sqrt_eq_rpow, ← Real.sqrt_inv]
      · have h2 : (((δ / ρ) ^ (2 / (ν + 1)))⁻¹ : ℝ) = (δ / ρ) ^ (-(2 / (ν + 1))) :=
          (Real.rpow_neg ht.le _).symm
        rw [h2, Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
        congr 1
        field_simp
    have hdata : δ * ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α‖ ≤
        C2 * (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))) := by
      calc δ * ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α‖
          ≤ δ * (Real.sqrt (Cφ * CF) * Real.sqrt (α : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left hRnorm hδ.le
        _ ≤ δ * (Real.sqrt (Cφ * CF) *
              (cA ^ (-(1 : ℝ) / 2) * (δ / ρ) ^ (-(1 : ℝ) / (ν + 1)))) := by
            refine mul_le_mul_of_nonneg_left ?_ hδ.le
            exact mul_le_mul_of_nonneg_left hsqrtinv (Real.sqrt_nonneg _)
        _ = C2 * (δ * (δ / ρ) ^ (-(1 : ℝ) / (ν + 1))) := by rw [hC2def]; ring
        _ = C2 * (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))) := by rw [key1]
    have hzy : ‖K x - z‖ ≤ δ := by rw [norm_sub_rev]; exact hzx
    have hsplit := norm_sub_moorePenrose_le (T := K) (spectralReg hs φ
        (hφ.exists_bound_on_spectrum hs)) (α := α) hxmem hzy
    rw [hmp] at hsplit
    have hpos0 : (0 : ℝ) ≤ δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1)) := by positivity
    have hmax : C1 + C2 ≤ max 1 (C1 + C2) := le_max_right _ _
    calc ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α z - x‖
        ≤ δ * ‖spectralReg hs φ (hφ.exists_bound_on_spectrum
            hs) α‖ + ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α (K x) - x‖ := hsplit
      _ ≤ C2 * (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1)))
            + C1 * (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))) := by linarith
      _ = (C1 + C2) * (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))) := by ring
      _ ≤ max 1 (C1 + C2) * (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))) :=
          mul_le_mul_of_nonneg_right hmax hpos0
      _ = max 1 (C1 + C2) * δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1)) := by ring

end AutoIp

end _thm_discrepancy_order_optimal
