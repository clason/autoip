/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_13_regularization._def_regularization
public import AutoIp._part_2_reg._ch_14_order_optimality._def_order_optimal
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_filter
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_qualification
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_equations
import AutoIp._part_2_reg._ch_12_picard._lem_source_in_kerperp
import AutoIp._part_2_reg._ch_13_regularization._lem_error_decomposition
import AutoIp._part_2_reg._ch_13_regularization._thm_apriori_characterisation
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_filter_norm_bound
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_omega_nu
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import AutoIp.Auxiliary.Rpow
import AutoIp._part_2_reg._ch_15_spectral_regularization._thm_apriori_order_optimal.Helpers
import Mathlib.Topology.Order.AtTopBotIxx

section _thm_apriori_order_optimal

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Order optimality for an a priori rule: let `y ∈ Dom(K†)` with `x† = K†y ∈ X_{ν,ρ}` for
`ν, ρ > 0`, let the filter satisfy (F) with constant `C_F` and `ω_ν(α) ≤ C_ν α^{ν/2}` for every
`α > 0`, and let `c (δ/ρ)^{2/(ν+1)} ≤ α(δ) ≤ C (δ/ρ)^{2/(ν+1)}` with `c, C > 0`.
Then `‖x^δ_{α(δ)} − x†‖ ≤ (√(C_φ C_F) c^{-1/2} + C_ν C^{ν/2}) δ^{ν/(ν+1)} ρ^{1/(ν+1)}` for
every `y^δ ∈ B_δ(y)`. The rule need not be a priori, since the bracket is asked at every
datum, and `C_ν > 0` is not required.

It holds for every `K`, `K = 0` included. -/
public theorem norm_spectralReg_sub_moorePenrose_le_apriori (hs : IsSingularSystem K σ v u)
    {φ : Set.Ioi (0 : ℝ) → ℝ → ℝ} {Cφ : ℝ}
    (hφ : IsRegularizingFilter K φ Cφ) {ν ρ CF Cν cl cu : ℝ} (hν : 0 < ν) (hρ : 0 < ρ)
    (hF : HasFilterBound K φ CF)
    (hQ : ∀ α : Set.Ioi (0 : ℝ),
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), lam ^ (ν / 2) * |1 - lam * φ α lam|) ≤
        Cν * (α : ℝ) ^ (ν / 2))
    (a : ParameterChoice F) (hcl : 0 < cl) (hcu : 0 < cu)
    (hrule : ∀ (δ : Set.Ioi (0 : ℝ)) (z : F),
      cl * ((δ : ℝ) / ρ) ^ (2 / (ν + 1)) ≤ a δ z ∧
        a δ z ≤ cu * ((δ : ℝ) / ρ) ^ (2 / (ν + 1)))
    {y : F} (hy : y ∈ mpDomain K) (hx : moorePenrose K ⟨y, hy⟩ ∈ sourceSet hs ν hν ρ hρ)
    {δ : ℝ} (hδ : 0 < δ) {z : F} (hz : ‖y - z‖ ≤ δ) :
    ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) ((a).param ⟨δ, hδ⟩
        z) z - moorePenrose K ⟨y, hy⟩‖ ≤
      (Real.sqrt (Cφ * CF) * cl ^ (-(1 : ℝ) / 2) + Cν * cu ^ (ν / 2)) *
        δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1)) := by
  set α := a.param ⟨δ, hδ⟩ z with hαdef
  have hα : (0 : ℝ) < (α : ℝ) := α.2
  have hαval : (α : ℝ) = a ⟨δ, hδ⟩ z := by rw [hαdef]; rfl
  obtain ⟨hlow, hupp⟩ := hrule ⟨δ, hδ⟩ z
  rw [← hαval] at hlow hupp
  have hν1 : (0 : ℝ) < ν + 1 := by linarith
  have hν1' : (ν : ℝ) + 1 ≠ 0 := hν1.ne'
  have ht : (0 : ℝ) < δ / ρ := div_pos hδ hρ
  have hrho := rpow_split_rate hρ hν1
  have key1 := mul_rpow_neg_rate hδ hρ hν1
  have key2 := rpow_div_mul_rate hδ hρ hν1
  have hΦ0 : (0 : ℝ) ≤ ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |φ α lam| :=
    Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _
  have hFα := hF.iSup_le α
  have hCF0 : (0 : ℝ) ≤ CF := hF.const_pos.le
  have hRnorm : ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α‖ ≤ Real.sqrt (Cφ *
      CF) * Real.sqrt (α : ℝ)⁻¹ :=
    opNorm_spectralReg_le_sqrt hs hφ hCF0 hFα
  have hsqrtinv :
      Real.sqrt (α : ℝ)⁻¹ ≤ cl ^ (-(1 : ℝ) / 2) * (δ / ρ) ^ (-(1 : ℝ) / (ν + 1)) := by
    have hT : (0 : ℝ) < (δ / ρ) ^ (2 / (ν + 1)) := Real.rpow_pos_of_pos ht _
    have hprod : (0 : ℝ) < cl * (δ / ρ) ^ (2 / (ν + 1)) := by positivity
    have hinv : (α : ℝ)⁻¹ ≤ (cl * (δ / ρ) ^ (2 / (ν + 1)))⁻¹ := by
      exact inv_anti₀ hprod hlow
    refine (Real.sqrt_le_sqrt hinv).trans_eq ?_
    rw [mul_inv, Real.sqrt_mul (by positivity)]
    congr 1
    · rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring, Real.rpow_neg hcl.le,
        ← Real.sqrt_eq_rpow, ← Real.sqrt_inv]
    · have h2 : (((δ / ρ) ^ (2 / (ν + 1)))⁻¹ : ℝ) = (δ / ρ) ^ (-(2 / (ν + 1))) :=
        (Real.rpow_neg ht.le _).symm
      rw [h2, Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
      congr 1
      field_simp
  have hdata : δ * ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α‖ ≤
      Real.sqrt (Cφ * CF) * cl ^ (-(1 : ℝ) / 2) *
        (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))) := by
    calc δ * ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α‖
        ≤ δ * (Real.sqrt (Cφ * CF) * Real.sqrt (α : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left hRnorm hδ.le
      _ ≤ δ * (Real.sqrt (Cφ * CF) *
            (cl ^ (-(1 : ℝ) / 2) * (δ / ρ) ^ (-(1 : ℝ) / (ν + 1)))) := by
          refine mul_le_mul_of_nonneg_left ?_ hδ.le
          exact mul_le_mul_of_nonneg_left hsqrtinv (Real.sqrt_nonneg _)
      _ = Real.sqrt (Cφ * CF) * cl ^ (-(1 : ℝ) / 2) *
            (δ * (δ / ρ) ^ (-(1 : ℝ) / (ν + 1))) := by ring
      _ = Real.sqrt (Cφ * CF) * cl ^ (-(1 : ℝ) / 2) *
            (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))) := by rw [key1]
  have hω0 : (0 : ℝ) ≤
      ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), lam ^ (ν / 2) * |1 - lam * φ α lam| :=
    Real.iSup_nonneg fun lam => Real.iSup_nonneg fun h =>
      mul_nonneg (Real.rpow_nonneg h.1.le _) (abs_nonneg _)
  have hQα := hQ α
  have hCν0 : (0 : ℝ) ≤ Cν := by
    by_contra hcon
    push Not at hcon
    have : Cν * (α : ℝ) ^ (ν / 2) < 0 :=
      mul_neg_of_neg_of_pos hcon (Real.rpow_pos_of_pos hα _)
    linarith
  have hαu : (α : ℝ) ^ (ν / 2) ≤ cu ^ (ν / 2) * (δ / ρ) ^ (ν / (ν + 1)) := by
    have h1 : (α : ℝ) ^ (ν / 2) ≤ (cu * (δ / ρ) ^ (2 / (ν + 1))) ^ (ν / 2) :=
      Real.rpow_le_rpow hα.le hupp (by positivity)
    rw [Real.mul_rpow hcu.le (Real.rpow_nonneg ht.le _), ← Real.rpow_mul ht.le,
      show 2 / (ν + 1) * (ν / 2) = ν / (ν + 1) by
        field_simp] at h1
    exact h1
  have happrox : ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y - moorePenrose K ⟨y, hy⟩‖ ≤
      Cν * cu ^ (ν / 2) * (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))) := by
    obtain ⟨hb, -⟩ := norm_spectralReg_sub_moorePenrose_le (α := α) hs hφ hν hρ hy hx
    refine hb.trans ?_
    calc (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), lam ^ (ν / 2) * |1 - lam * φ α lam|) * ρ
        ≤ (Cν * (α : ℝ) ^ (ν / 2)) * ρ := mul_le_mul_of_nonneg_right hQα hρ.le
      _ ≤ (Cν * (cu ^ (ν / 2) * (δ / ρ) ^ (ν / (ν + 1)))) * ρ := by
          refine mul_le_mul_of_nonneg_right ?_ hρ.le
          exact mul_le_mul_of_nonneg_left hαu hCν0
      _ = Cν * cu ^ (ν / 2) * ((δ / ρ) ^ (ν / (ν + 1)) * ρ) := by ring
      _ = Cν * cu ^ (ν / 2) * (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))) := by rw [key2]
  have hsplit := norm_sub_moorePenrose_le (T := K) (spectralReg hs φ (hφ.exists_bound_on_spectrum
      hs)) (α := α) hy hz
  have hgoal : (Real.sqrt (Cφ * CF) * cl ^ (-(1 : ℝ) / 2) + Cν * cu ^ (ν / 2)) *
      δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1)) =
      Real.sqrt (Cφ * CF) * cl ^ (-(1 : ℝ) / 2) *
        (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))) +
      Cν * cu ^ (ν / 2) * (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))) := by ring
  rw [hgoal]
  linarith

/-- The closing clause: for a filter satisfying (F) and an a priori rule with
`c (δ/ρ)^{2/(ν+1)} ≤ α(δ) ≤ C (δ/ρ)^{2/(ν+1)}`, `(R_α, α)` is a convergent regularization
method. Neither the source condition, nor the bound `ω_ν(α) ≤ C_ν α^{ν/2}`, nor `C > 0` is
required. The hypothesis that `{R_α}` is a regularization of `K†` holds for every regularizing
filter.

It holds for every `K`, `K = 0` included. -/
public
theorem isRegularizationMethod_apriori (hs : IsSingularSystem K σ v u) {φ : Set.Ioi (0 : ℝ) → ℝ →
    ℝ} {Cφ : ℝ}
    (hφ : IsRegularizingFilter K φ Cφ)
    (hreg : IsRegularization K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs)))
    {ν ρ CF cl cu : ℝ} (hν : 0 < ν) (hρ : 0 < ρ)
    (hF : HasFilterBound K φ CF)
    (a : ParameterChoice F) (ha : a.IsAPriori) (hcl : 0 < cl)
    (hrule : ∀ (δ : Set.Ioi (0 : ℝ)) (z : F),
      cl * ((δ : ℝ) / ρ) ^ (2 / (ν + 1)) ≤ a δ z ∧
        a δ z ≤ cu * ((δ : ℝ) / ρ) ^ (2 / (ν + 1))) :
    IsRegularizationMethod K (fun α w => spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α
        w) a := by
  have hν1 : (0 : ℝ) < ν + 1 := by linarith
  have hCF0 : (0 : ℝ) ≤ CF := hF.const_pos.le
  have hrpow : ∀ t : ℝ, 0 < t →
      Tendsto (fun δ : ℝ => (δ / ρ) ^ t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro t ht
    have hdiv : Tendsto (fun δ : ℝ => δ / ρ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := (tendsto_id.div_const ρ).mono_left
        (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi (0 : ℝ)))
      simpa using h
    have hc : ContinuousAt (fun s : ℝ => s ^ t) 0 :=
      Real.continuousAt_rpow_const 0 _ (Or.inr ht.le)
    have h0 : Tendsto (fun s : ℝ => s ^ t) (𝓝 (0 : ℝ)) (𝓝 0) := by
      have h := hc.tendsto
      rwa [Real.zero_rpow ht.ne'] at h
    exact h0.comp hdiv
  have hcoe : Tendsto ((↑) : Set.Ioi (0 : ℝ) → ℝ) atBot (𝓝[>] (0 : ℝ)) :=
    (map_coe_Ioi_atBot (0 : ℝ)).le
  refine isRegularizationMethod_of_apriori hreg ha ?_ ?_
  · intro y
    refine squeeze_zero' (g := fun δ : Set.Ioi (0 : ℝ) => cu * ((δ : ℝ) / ρ) ^ (2 / (ν + 1)))
      (.of_forall fun δ => (a.pos δ y).le) (.of_forall fun δ => (hrule δ y).2) ?_
    simpa using ((hrpow (2 / (ν + 1)) (by positivity)).comp hcoe).const_mul cu
  · intro y
    set C : ℝ := Real.sqrt (Cφ * CF) * cl ^ (-(1 : ℝ) / 2) with hC
    have hC0 : (0 : ℝ) ≤ C := by
      rw [hC]; positivity
    have hbound : ∀ (δ : ℝ) (hδ : 0 < δ),
        δ * ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) ((a).param ⟨δ, hδ⟩ y)‖
          ≤ C * (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))) := by
      intro δ hδ
      set α := a.param ⟨δ, hδ⟩ y with hαdef
      have hα : (0 : ℝ) < (α : ℝ) := α.2
      have hαval : (α : ℝ) = a ⟨δ, hδ⟩ y := by rw [hαdef]; rfl
      obtain ⟨hlow, -⟩ := hrule ⟨δ, hδ⟩ y
      rw [← hαval] at hlow
      have ht : (0 : ℝ) < δ / ρ := div_pos hδ hρ
      have hRnorm : ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α‖ ≤ Real.sqrt (Cφ *
          CF) * Real.sqrt (α : ℝ)⁻¹ :=
        opNorm_spectralReg_le_sqrt hs hφ hCF0 (hF.iSup_le α)
      have hsqrtinv :
          Real.sqrt (α : ℝ)⁻¹ ≤ cl ^ (-(1 : ℝ) / 2) * (δ / ρ) ^ (-(1 : ℝ) / (ν + 1)) := by
        have hT : (0 : ℝ) < (δ / ρ) ^ (2 / (ν + 1)) := Real.rpow_pos_of_pos ht _
        have hprod : (0 : ℝ) < cl * (δ / ρ) ^ (2 / (ν + 1)) := by positivity
        have hinv : (α : ℝ)⁻¹ ≤ (cl * (δ / ρ) ^ (2 / (ν + 1)))⁻¹ := inv_anti₀ hprod hlow
        refine (Real.sqrt_le_sqrt hinv).trans_eq ?_
        rw [mul_inv, Real.sqrt_mul (by positivity)]
        congr 1
        · rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring, Real.rpow_neg hcl.le,
            ← Real.sqrt_eq_rpow, ← Real.sqrt_inv]
        · have h2 : (((δ / ρ) ^ (2 / (ν + 1)))⁻¹ : ℝ) = (δ / ρ) ^ (-(2 / (ν + 1))) :=
            (Real.rpow_neg ht.le _).symm
          rw [h2, Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
          congr 1
          field_simp
      have key1 : δ * (δ / ρ) ^ (-(1 : ℝ) / (ν + 1)) =
          δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1)) := by
        have h1 : (δ / ρ) ^ (-(1 : ℝ) / (ν + 1))
            = δ ^ (-(1 : ℝ) / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1)) := by
          rw [Real.div_rpow hδ.le hρ.le, div_eq_mul_inv]
          congr 1
          rw [show (-(1 : ℝ) / (ν + 1)) = -((1 : ℝ) / (ν + 1)) by ring,
            Real.rpow_neg hρ.le, inv_inv]
        rw [h1, ← mul_assoc]
        congr 1
        nth_rewrite 1 [← Real.rpow_one δ]
        rw [← Real.rpow_add hδ]
        congr 1
        field_simp
        ring
      have hs1 : (0 : ℝ) ≤ Real.sqrt (Cφ * CF) := Real.sqrt_nonneg _
      calc δ * ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α‖
          ≤ δ * (Real.sqrt (Cφ * CF) * Real.sqrt (α : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left hRnorm hδ.le
        _ ≤ δ * (Real.sqrt (Cφ * CF) *
              (cl ^ (-(1 : ℝ) / 2) * (δ / ρ) ^ (-(1 : ℝ) / (ν + 1)))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hsqrtinv hs1) hδ.le
        _ = C * (δ * (δ / ρ) ^ (-(1 : ℝ) / (ν + 1))) := by rw [hC]; ring
        _ = C * (δ ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))) := by rw [key1]
    refine squeeze_zero' (g := fun δ : Set.Ioi (0 : ℝ) =>
      C * ((δ : ℝ) ^ (ν / (ν + 1)) * ρ ^ ((1 : ℝ) / (ν + 1))))
      (.of_forall fun δ => mul_nonneg δ.2.le (norm_nonneg _))
      (.of_forall fun δ => hbound (δ : ℝ) δ.2) ?_
    · have hd : Tendsto (fun δ : ℝ => δ ^ (ν / (ν + 1))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have hc : ContinuousAt (fun s : ℝ => s ^ (ν / (ν + 1))) 0 :=
          Real.continuousAt_rpow_const 0 _ (Or.inr (by positivity))
        have h0 : Tendsto (fun s : ℝ => s ^ (ν / (ν + 1))) (𝓝 (0 : ℝ)) (𝓝 0) := by
          have h := hc.tendsto
          rwa [Real.zero_rpow (by positivity : ν / (ν + 1) ≠ 0)] at h
        exact h0.mono_left nhdsWithin_le_nhds
      simpa using (((hd.comp hcoe).mul_const (ρ ^ ((1 : ℝ) / (ν + 1)))).const_mul C)

/-- The "in particular" clause: under the hypotheses of the
rate bound, `(R_α, α)` is order optimal for `ν` and `ρ`,
with constant `max 1 (√(C_φ C_F) c^{-1/2} + C_ν C^{ν/2})`.

It holds for every `K`, `K = 0` included. -/
public theorem isOrderOptimal_apriori (hs : IsSingularSystem K σ v u) {φ : Set.Ioi (0 : ℝ) → ℝ →
    ℝ} {Cφ : ℝ}
    (hφ : IsRegularizingFilter K φ Cφ) {ν ρ CF Cν cl cu : ℝ} (hν : 0 < ν) (hρ : 0 < ρ)
    (hF : HasFilterBound K φ CF)
    (hQ : ∀ α : Set.Ioi (0 : ℝ),
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), lam ^ (ν / 2) * |1 - lam * φ α lam|) ≤
        Cν * (α : ℝ) ^ (ν / 2))
    (a : ParameterChoice F) (hcl : 0 < cl) (hcu : 0 < cu)
    (hrule : ∀ (δ : Set.Ioi (0 : ℝ)) (z : F),
      cl * ((δ : ℝ) / ρ) ^ (2 / (ν + 1)) ≤ a δ z ∧
        a δ z ≤ cu * ((δ : ℝ) / ρ) ^ (2 / (ν + 1))) :
    IsOrderOptimal K (fun α w => spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α w) a hs ν ρ
      (max 1 (Real.sqrt (Cφ * CF) * cl ^ (-(1 : ℝ) / 2) + Cν * cu ^ (ν / 2))) := by
  set c₀ := Real.sqrt (Cφ * CF) * cl ^ (-(1 : ℝ) / 2) + Cν * cu ^ (ν / 2) with hc₀
  have hmp : ∀ x ∈ sourceSet hs ν hν ρ hρ, moorePenrose K ⟨K x, Submodule.mem_sup_left ⟨x,
      rfl⟩⟩ = x := by
    intro x hx
    have hxk : x ∈ (K.toLinearMap.ker)ᗮ := sourceSet_subset_orthogonal_ker hs hν hρ hx
    rw [moorePenrose_apply_apply,
      (Submodule.starProjection_apply_eq_zero_iff _).mpr hxk, sub_zero]
  refine ⟨hν, hρ, le_max_left _ _, ?_⟩
  intro x hx δ hδ
  rw [worstCaseError_le_iff K _ a (K x) (Submodule.mem_sup_left ⟨x, rfl⟩) δ hδ]
  intro z hz
  have hzd : ‖K x - z‖ ≤ δ := by
    rw [← dist_eq_norm]
    exact Metric.mem_closedBall'.mp hz
  have hy : K x ∈ mpDomain K := Submodule.mem_sup_left ⟨x, rfl⟩
  have hx' : moorePenrose K ⟨K x, Submodule.mem_sup_left ⟨x,
      rfl⟩⟩ ∈ sourceSet hs ν hν ρ hρ := by rw [hmp x hx]; exact hx
  have hres := norm_spectralReg_sub_moorePenrose_le_apriori hs hφ hν hρ hF hQ a hcl hcu
    hrule hy hx' hδ hzd
  rw [hmp x hx] at hres
  have hδn : (0 : ℝ) ≤ δ ^ (ν / (ν + 1)) := Real.rpow_nonneg hδ.le _
  have hρn : (0 : ℝ) ≤ ρ ^ ((1 : ℝ) / (ν + 1)) := Real.rpow_nonneg hρ.le _
  rw [hmp x hx, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal (hres.trans ?_)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right 1 c₀) hδn) hρn

end AutoIp

end _thm_apriori_order_optimal
