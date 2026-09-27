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
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Algebra.Order.Algebra

namespace AutoIp

open Filter Topology

/-- There is `t₀ ∈ (0, 1)` such that for `t ∈ (0, t₀]` every `α ∈ (0, κ]` with
`Θ_{φ^log_p}(α) = t` satisfies `φ^log_p(α) ≤ (log (1/t))^(-p)`. -/
public theorem exists_logIndex_le_log_inv_rpow {κ p : ℝ} (hkpos : 0 < κ) (hp : 0 < p) :
    ∃ t₀ ∈ Set.Ioo (0 : ℝ) 1, ∀ t : ℝ, 0 < t → t ≤ t₀ → ∀ α : ℝ, 0 < α → α ≤ κ →
      thetaIndex (logIndex κ p hp) α = t → logIndex κ p hp α ≤ Real.log (1 / t) ^ (-p) := by
  have hk0 : (0 : ℝ) ≤ κ := hkpos.le
  have hep : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  obtain ⟨n, hndef⟩ : ∃ n : ℕ, n = ⌈4 * p⌉₊ + 1 := ⟨_, rfl⟩
  have hn : 0 < n := by rw [hndef]; exact Nat.succ_pos _
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hn4p : 4 * p + 1 ≤ (n : ℝ) := by
    have h := Nat.le_ceil (4 * p)
    rw [hndef]
    push_cast
    linarith
  have hnn : (0:ℝ) < (n:ℝ) ^ n := by positivity
  have hekpos : (0:ℝ) < Real.exp 1 * κ := by positivity
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = (n:ℝ) ^ n / (Real.exp 1 * κ) := ⟨_, rfl⟩
  have hM0 : (0:ℝ) < M := by rw [hMdef]; positivity
  obtain ⟨t₀, ht₀def⟩ : ∃ t₀ : ℝ, t₀ = min (1/2)
      (min (Real.sqrt κ) (Real.sqrt (Real.exp 1 * κ * Real.exp (-M)))) := ⟨_, rfl⟩
  have ht₀pos : (0:ℝ) < t₀ := by
    rw [ht₀def]
    refine lt_min (by norm_num) (lt_min (Real.sqrt_pos.mpr hkpos) ?_)
    exact Real.sqrt_pos.mpr (by positivity)
  have ht₀half : t₀ ≤ 1/2 := by rw [ht₀def]; exact min_le_left _ _
  have ht₀sk : t₀ ≤ Real.sqrt κ := by
    rw [ht₀def]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have ht₀sM : t₀ ≤ Real.sqrt (Real.exp 1 * κ * Real.exp (-M)) := by
    rw [ht₀def]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hlog1 : ∀ s : ℝ, 0 < s → s ≤ κ → 1 ≤ Real.log (Real.exp 1 * κ / s) :=
    fun _ hs hsk => one_le_log_exp_mul_div hs hsk
  have hvalk : ∀ s : ℝ, 0 < s → logIndex κ p hp s = Real.log (Real.exp 1 * κ / s) ^ (-p) := by
    intro s hs
    exact logIndex_of_pos hs κ hp
  have hkey : ∀ t : ℝ, 0 < t → t ≤ t₀ → ∀ α : ℝ, 0 < α → α ≤ κ →
      thetaIndex (logIndex κ p hp) α = t → logIndex κ p hp α ≤ Real.log (1 / t) ^ (-p) := by
    intro t ht0 htt0 α hα0 hακ hΘ
    have ht2pos : (0:ℝ) < t ^ 2 := by positivity
    have htκ : t ^ 2 ≤ κ := by
      have h := htt0.trans ht₀sk
      nlinarith [Real.sq_sqrt hk0, Real.sqrt_nonneg κ]
    have hnn2 : (0:ℝ) ≤ Real.exp 1 * κ * Real.exp (-M) := by positivity
    have htM : t ^ 2 ≤ Real.exp 1 * κ * Real.exp (-M) := by
      have h := htt0.trans ht₀sM
      nlinarith [Real.sq_sqrt hnn2, Real.sqrt_nonneg (Real.exp 1 * κ * Real.exp (-M))]
    obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = Real.log (Real.exp 1 * κ / t ^ 2) := ⟨_, rfl⟩
    have hu1 : 1 ≤ u := by rw [hudef]; exact hlog1 _ ht2pos htκ
    have hu0 : (0:ℝ) < u := by linarith
    have huM : M ≤ u := by
      have h1 : Real.exp M ≤ Real.exp 1 * κ / t ^ 2 := by
        rw [le_div_iff₀ ht2pos]
        calc Real.exp M * t ^ 2
            ≤ Real.exp M * (Real.exp 1 * κ * Real.exp (-M)) :=
              mul_le_mul_of_nonneg_left htM (Real.exp_pos M).le
          _ = Real.exp 1 * κ := by
              rw [show Real.exp M * (Real.exp 1 * κ * Real.exp (-M))
                    = Real.exp M * Real.exp (-M) * (Real.exp 1 * κ) by ring,
                ← Real.exp_add]
              simp
      rw [hudef]
      calc M = Real.log (Real.exp M) := (Real.log_exp M).symm
        _ ≤ _ := Real.log_le_log (Real.exp_pos M) h1
    have ht2eq : t ^ 2 = Real.exp 1 * κ * Real.exp (-u) := by
      rw [hudef, Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
    have hexpu : Real.exp (-u) * u ^ (4 * p) ≤ Real.exp 1 * κ := by
      have h1 : u ^ (4 * p) * u ≤ u ^ (n : ℕ) := by
        rw [← Real.rpow_natCast u n]
        calc u ^ (4 * p) * u = u ^ (4 * p + 1) := by
              rw [Real.rpow_add hu0, Real.rpow_one]
          _ ≤ u ^ ((n:ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hu1 hn4p
      have h2 : u ^ (n:ℕ) ≤ (n:ℝ) ^ (n:ℕ) * Real.exp u := by
        have h := pow_le_pow_div_mul_exp (a := 1) one_pos hn hu0.le
        simpa using h
      have he : (0:ℝ) < Real.exp (-u) := Real.exp_pos _
      have hne : Real.exp u ≠ 0 := (Real.exp_pos u).ne'
      have h3 : Real.exp (-u) * (u ^ (4 * p) * u) ≤ (n:ℝ) ^ (n:ℕ) := by
        calc Real.exp (-u) * (u ^ (4 * p) * u)
            ≤ Real.exp (-u) * ((n:ℝ) ^ (n:ℕ) * Real.exp u) :=
              mul_le_mul_of_nonneg_left (h1.trans h2) he.le
          _ = (n:ℝ) ^ (n:ℕ) := by
              rw [Real.exp_neg]
              field_simp
      have h4 : Real.exp (-u) * u ^ (4 * p) ≤ (n:ℝ) ^ (n:ℕ) / u := by
        rw [le_div_iff₀ hu0]
        calc Real.exp (-u) * u ^ (4 * p) * u
            = Real.exp (-u) * (u ^ (4 * p) * u) := by ring
          _ ≤ _ := h3
      refine h4.trans ?_
      rw [div_le_iff₀ hu0]
      have h5 : (n:ℝ) ^ n ≤ u * (Real.exp 1 * κ) := by
        rw [hMdef, div_le_iff₀ hekpos] at huM
        exact huM
      nlinarith
    have hlogα : 1 ≤ Real.log (Real.exp 1 * κ / α) := hlog1 α hα0 hακ
    have hvalα : logIndex κ p hp α = Real.log (Real.exp 1 * κ / α) ^ (-p) := hvalk α hα0
    have hφα1 : logIndex κ p hp α ≤ 1 := by
      rw [hvalα]
      exact Real.rpow_le_one_of_one_le_of_nonpos hlogα (by linarith)
    have hφαpos : (0:ℝ) < logIndex κ p hp α := by
      rw [hvalα]
      exact Real.rpow_pos_of_pos (by linarith) _
    have hΘ' : Real.sqrt α * logIndex κ p hp α = t := by rw [← thetaIndex_apply]; exact hΘ
    have hsq : t ≤ Real.sqrt α := by
      have h := mul_nonneg (Real.sqrt_nonneg α) (sub_nonneg.mpr hφα1)
      nlinarith [hΘ']
    have hαt2 : t ^ 2 ≤ α := by
      nlinarith [Real.sq_sqrt hα0.le, Real.sqrt_nonneg α]
    have hφt2 : logIndex κ p hp (t ^ 2) = u ^ (-p) := by
      rw [hvalk _ ht2pos, hudef]
    have hφge : logIndex κ p hp (t ^ 2) ≤ logIndex κ p hp α :=
      (isIndexFunction_logIndex hp).strictMonoOn.monotoneOn
        ⟨ht2pos.le, htκ⟩ ⟨hα0.le, hακ⟩ hαt2
    have hupneg : (0:ℝ) < u ^ (-p) := Real.rpow_pos_of_pos hu0 _
    have hsqrtle : Real.sqrt α * u ^ (-p) ≤ t := by
      rw [← hΘ']
      exact mul_le_mul_of_nonneg_left (by rw [← hφt2]; exact hφge) (Real.sqrt_nonneg α)
    have hαu : α * (u ^ (-p)) ^ 2 ≤ t ^ 2 := by
      have hnn3 : (0:ℝ) ≤ Real.sqrt α * u ^ (-p) :=
        mul_nonneg (Real.sqrt_nonneg α) hupneg.le
      have h := mul_self_le_mul_self hnn3 hsqrtle
      have heq : (Real.sqrt α * u ^ (-p)) * (Real.sqrt α * u ^ (-p))
          = α * (u ^ (-p)) ^ 2 := by
        rw [show (Real.sqrt α * u ^ (-p)) * (Real.sqrt α * u ^ (-p))
            = Real.sqrt α ^ 2 * (u ^ (-p)) ^ 2 by ring, Real.sq_sqrt hα0.le]
      rw [heq] at h
      calc α * (u ^ (-p)) ^ 2 ≤ t * t := h
        _ = t ^ 2 := by ring
    have hsqeq : (u ^ (-p)) ^ 2 * u ^ (2 * p) = 1 := by
      rw [pow_two, ← Real.rpow_add hu0, ← Real.rpow_add hu0,
        show -p + -p + 2 * p = 0 by ring, Real.rpow_zero]
    have hup2 : (0:ℝ) < u ^ (2 * p) := Real.rpow_pos_of_pos hu0 _
    have hαβ : α ≤ t ^ 2 * u ^ (2 * p) := by
      have h := mul_le_mul_of_nonneg_right hαu hup2.le
      rwa [mul_assoc, hsqeq, mul_one] at h
    have hsq2 : (u ^ (2 * p)) ^ 2 = u ^ (4 * p) := by
      rw [pow_two, ← Real.rpow_add hu0]
      congr 1
      ring
    have hgsq : (t * u ^ (2 * p)) ^ 2 ≤ (Real.exp 1 * κ) ^ 2 := by
      rw [mul_pow, hsq2, ht2eq]
      calc Real.exp 1 * κ * Real.exp (-u) * u ^ (4 * p)
          = (Real.exp 1 * κ) * (Real.exp (-u) * u ^ (4 * p)) := by ring
        _ ≤ (Real.exp 1 * κ) * (Real.exp 1 * κ) :=
            mul_le_mul_of_nonneg_left hexpu hekpos.le
        _ = (Real.exp 1 * κ) ^ 2 := by ring
    have hg : t * u ^ (2 * p) ≤ Real.exp 1 * κ := by
      have hA : (0:ℝ) ≤ t * u ^ (2 * p) := mul_nonneg ht0.le hup2.le
      exact le_of_pow_le_pow_left₀ two_ne_zero hekpos.le hgsq
    have hαfin : α ≤ Real.exp 1 * κ * t := by
      have h := mul_le_mul_of_nonneg_left hg ht0.le
      calc α ≤ t ^ 2 * u ^ (2 * p) := hαβ
        _ = t * (t * u ^ (2 * p)) := by ring
        _ ≤ t * (Real.exp 1 * κ) := h
        _ = Real.exp 1 * κ * t := by ring
    have hlt : (0:ℝ) < Real.log (1 / t) := by
      refine Real.log_pos ?_
      rw [lt_div_iff₀ ht0]
      linarith
    have hcmp : Real.log (1 / t) ≤ Real.log (Real.exp 1 * κ / α) := by
      refine Real.log_le_log (by positivity) ?_
      rw [div_le_div_iff₀ ht0 hα0]
      linarith
    rw [hvalα]
    exact Real.rpow_le_rpow_of_nonpos hlt hcmp (by linarith)
  exact ⟨t₀, ⟨ht₀pos, by linarith⟩, hkey⟩

end AutoIp
