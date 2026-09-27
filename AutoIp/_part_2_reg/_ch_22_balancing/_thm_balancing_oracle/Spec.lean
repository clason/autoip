/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_filter
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
public import AutoIp._part_2_reg._ch_19_general_source_conditions._def_general_source
public import AutoIp._part_2_reg._ch_22_balancing._def_balancing
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_qualification
import AutoIp.Auxiliary.Geometric
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_filter_norm_bound
import AutoIp._part_2_reg._ch_19_general_source_conditions._lem_general_omega
import AutoIp._part_2_reg._ch_22_balancing._lem_balancing_le_star
import AutoIp._part_2_reg._ch_22_balancing._lem_balancing_nonempty

section _thm_balancing_oracle

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Oracle inequality for the balancing principle: in the setting of the lemma that the balancing
index does not overshoot, if some `i_* ≤ N` has `ωⱼ ≤ Δⱼ` for every `j ≥ i_*` and the bias is
non-increasing along the grid, `ω_φ(αⱼ) ≤ ω_φ(αᵢ)` for `i ≤ j ≤ N`, then
`‖x_{i₊} - x†‖ ≤ 6√q min_{0 ≤ i ≤ N} (ω_φ(αᵢ) ρ + Δᵢ)`.

The least such `i_*`, which the node names, exists once some `i_*` does; the Lean assumes only that
one does. -/
public theorem balancing_oracle (hs : IsSingularSystem K σ v u) {flt : Set.Ioi (0 : ℝ) → ℝ →
    ℝ} {Cflt CF : ℝ}
    (hflt : IsRegularizingFilter K flt Cflt)
    (hF : HasFilterBound K flt CF)
    {φ : ℝ → ℝ} {ρ : ℝ} (hφ : IsIndexFunction (‖K‖ ^ 2) φ) (hρ : 0 < ρ)
    {y : F} (hy : y ∈ mpDomain K)
    (hx : moorePenrose K ⟨y, hy⟩ ∈ sourceSetIndex hs φ (hφ.exists_bound_on_spectrum hs) ρ hρ)
    {δ : ℝ} (hδ : 0 ≤ δ) {z : F} (hz : ‖y - z‖ ≤ δ)
    {N : ℕ} {grid : ℕ → Set.Ioi (0 : ℝ)} {q : ℝ} (hq : 1 < q)
    (hgeom : ∀ i, i + 1 ≤ N → (grid i : ℝ) = q * (grid (i + 1) : ℝ))
    (hmono : ∀ i j, i ≤ j → j ≤ N →
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), φ lam * |1 - lam * flt (grid j) lam|) ≤
        (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), φ lam * |1 - lam * flt (grid i) lam|))
    (hex : ∃ i ≤ N, ∀ j, i ≤ j → j ≤ N →
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), φ lam * |1 - lam * flt (grid j) lam|) * ρ ≤
        Real.sqrt (Cflt * CF) * δ * (grid j : ℝ) ^ (-(1 : ℝ) / 2)) :
    ‖spectralReg hs flt (hflt.exists_bound_on_spectrum hs)
          (grid (balancingIndex (spectralReg hs flt (hflt.exists_bound_on_spectrum hs)) (Real.sqrt
              (Cflt * CF)) δ (mul_nonneg (Real.sqrt_nonneg _) hδ) N grid z)) z -
        moorePenrose K ⟨y, hy⟩‖ ≤
      6 * Real.sqrt q *
        (Finset.range (N + 1)).inf' Finset.nonempty_range_add_one (fun i =>
          (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), φ lam * |1 - lam * flt (grid i) lam|) * ρ +
            Real.sqrt (Cflt * CF) * δ * (grid i : ℝ) ^ (-(1 : ℝ) / 2)) := by
  classical
  set S : Set ℕ := {i | i ≤ N ∧ ∀ j, i ≤ j → j ≤ N →
    (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), φ lam * |1 - lam * flt (grid j) lam|) * ρ ≤
      Real.sqrt (Cflt * CF) * δ * (grid j : ℝ) ^ (-(1 : ℝ) / 2)} with hSdef
  have hSne : S.Nonempty := by
    obtain ⟨i, hiN, hi⟩ := hex
    exact ⟨i, hiN, hi⟩
  set istar : ℕ := sInf S with histardef
  have hmemS : istar ∈ S := Nat.sInf_mem hSne
  have histar : istar ≤ N := hmemS.1
  have hstar := hmemS.2
  have hleast : ∀ i, (∀ j, i ≤ j → j ≤ N →
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), φ lam * |1 - lam * flt (grid j) lam|) * ρ ≤
        Real.sqrt (Cflt * CF) * δ * (grid j : ℝ) ^ (-(1 : ℝ) / 2)) → istar ≤ i := by
    intro i hi
    rcases le_or_gt i N with hiN | hiN
    · exact Nat.sInf_le ⟨hiN, hi⟩
    · exact le_trans histar hiN.le
  have hCR0 : (0 : ℝ) ≤ Real.sqrt (Cflt * CF) := Real.sqrt_nonneg _
  have hq0 : (0 : ℝ) < q := by linarith
  have hsq0 : (0 : ℝ) < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hsqne : Real.sqrt q ≠ 0 := ne_of_gt hsq0
  have hq1 : (1 : ℝ) ≤ Real.sqrt q := by
    have h := Real.sqrt_le_sqrt hq.le
    simpa using h
  have hCF0 : (0 : ℝ) ≤ CF := hF.const_pos.le
  have hrp : ∀ t : ℝ, 0 ≤ t → t ^ (-(1 : ℝ) / 2) = (Real.sqrt t)⁻¹ := fun t ht => by
    rw [Real.sqrt_eq_rpow, neg_div, Real.rpow_neg ht]
  have hΔ : ∀ i j, i ≤ j → j ≤ N → (grid i : ℝ) ^ (-(1 : ℝ) / 2) ≤ (grid j : ℝ) ^ (-(1 : ℝ) / 2) :=
    fun i j hij hjN => rpow_neg_half_le_of_geometric hq hgeom hij hjN
  have hdata : ∀ i, i ≤ N →
      ‖spectralReg hs flt (hflt.exists_bound_on_spectrum hs) (grid
          i) z - spectralReg hs flt (hflt.exists_bound_on_spectrum hs) (grid i) y‖
        ≤ Real.sqrt (Cflt * CF) * δ * (grid i : ℝ) ^ (-(1 : ℝ) / 2) :=
    fun i _ => norm_spectralReg_sub_le_mul_rpow (α := grid i) hs hflt hF hz
  have herr : ∀ i, i ≤ N → ‖spectralReg hs flt (hflt.exists_bound_on_spectrum hs) (grid
      i) z - moorePenrose K ⟨y, hy⟩‖ ≤
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), φ lam * |1 - lam * flt (grid i) lam|) * ρ
        + Real.sqrt (Cflt * CF) * δ * (grid i : ℝ) ^ (-(1 : ℝ) / 2) := by
    intro i hi
    have h1 := norm_spectralReg_sub_moorePenrose_le_iSup (α := grid i) hs hflt hφ hρ hy hx
    have h2 := hdata i hi
    have h3 := norm_sub_le_norm_sub_add_norm_sub (spectralReg hs flt
        (hflt.exists_bound_on_spectrum hs) (grid
            i) z) (spectralReg hs flt (hflt.exists_bound_on_spectrum hs)
      (grid i) y)
      (moorePenrose K ⟨y, hy⟩)
    linarith
  have hωnn : ∀ i, (0 : ℝ) ≤
      ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), φ lam * |1 - lam * flt (grid i) lam| :=
    fun i => Real.iSup_nonneg fun lam => Real.iSup_nonneg fun h =>
      mul_nonneg (hφ.nonneg lam ⟨h.1.le, h.2⟩) (abs_nonneg _)
  obtain ⟨hipN, hipcond⟩ := balancingIndex_spec (spectralReg hs flt
      (hflt.exists_bound_on_spectrum hs)) hCR0 hδ N z
  have hiple :=
    balancingIndex_le_of_bias_le hs hflt hF hφ hρ hy hx hδ hz hq hgeom histar hstar
  set ip := balancingIndex (spectralReg hs flt (hflt.exists_bound_on_spectrum hs)) (Real.sqrt
      (Cflt * CF)) δ (mul_nonneg (Real.sqrt_nonneg _) hδ) N grid z with hipdef
  -- Step 1 of the node: the selected error is at most `6 Δ_{i_*}`.
  have hstep1 : ‖spectralReg hs flt (hflt.exists_bound_on_spectrum hs) (grid
      ip) z - moorePenrose K ⟨y, hy⟩‖ ≤
      6 * (Real.sqrt (Cflt * CF) * δ * (grid istar : ℝ) ^ (-(1 : ℝ) / 2)) := by
    have h1 := hipcond istar hiple histar
    have h2 := herr istar histar
    have h3 := hstar istar le_rfl histar
    have h4 := norm_sub_le_norm_sub_add_norm_sub (spectralReg hs flt
        (hflt.exists_bound_on_spectrum hs) (grid
            ip) z) (spectralReg hs flt (hflt.exists_bound_on_spectrum hs)
      (grid istar) z)
      (moorePenrose K ⟨y, hy⟩)
    linarith
  -- Step 2 of the node: `Δ_{i_*} ≤ √q e_i` for every `i`.
  have hstep2 : ∀ i, i ≤ N → Real.sqrt (Cflt * CF) * δ * (grid istar : ℝ) ^ (-(1 : ℝ) / 2) ≤
      Real.sqrt q * ((⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
            φ lam * |1 - lam * flt (grid i) lam|) * ρ +
          Real.sqrt (Cflt * CF) * δ * (grid i : ℝ) ^ (-(1 : ℝ) / 2)) := by
    intro i hiN
    have hdi : (0 : ℝ) ≤ Real.sqrt (Cflt * CF) * δ * (grid i : ℝ) ^ (-(1 : ℝ) / 2) :=
      mul_nonneg (mul_nonneg hCR0 hδ) (Real.rpow_nonneg (grid i).2.le _)
    have hwi : (0 : ℝ) ≤ (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
        φ lam * |1 - lam * flt (grid i) lam|) * ρ := mul_nonneg (hωnn i) hρ.le
    by_cases hcase : istar ≤ i
    · have h5 : Real.sqrt (Cflt * CF) * δ * (grid istar : ℝ) ^ (-(1 : ℝ) / 2)
          ≤ Real.sqrt (Cflt * CF) * δ * (grid i : ℝ) ^ (-(1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left (hΔ istar i hcase hiN) (mul_nonneg hCR0 hδ)
      nlinarith [mul_nonneg (sub_nonneg.mpr hq1) (add_nonneg hwi hdi)]
    · obtain ⟨m, hm⟩ : ∃ m, istar = m + 1 := ⟨istar - 1, by omega⟩
      have him : i ≤ m := by omega
      have hmN : m ≤ N := by omega
      have hnot : ¬ (∀ j, m ≤ j → j ≤ N →
          (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), φ lam * |1 - lam * flt (grid j) lam|) * ρ ≤
            Real.sqrt (Cflt * CF) * δ * (grid j : ℝ) ^ (-(1 : ℝ) / 2)) := by
        intro hall
        have h6 := hleast m hall
        omega
      push Not at hnot
      obtain ⟨j, hmj, hjN, hjgt⟩ := hnot
      have hjm : j = m := by
        by_contra hne
        have hjs : istar ≤ j := by omega
        exact absurd (hstar j hjs hjN) (not_le.mpr hjgt)
      rw [hjm] at hjgt
      have hmi := mul_le_mul_of_nonneg_right (hmono i m him hmN) hρ.le
      have hgm : (grid m : ℝ) = q * (grid istar : ℝ) := by rw [hm]; exact hgeom m (by omega)
      have hΔeq : Real.sqrt (Cflt * CF) * δ * (grid istar : ℝ) ^ (-(1 : ℝ) / 2)
          = Real.sqrt q * (Real.sqrt (Cflt * CF) * δ * (grid m : ℝ) ^ (-(1 : ℝ) / 2)) := by
        rw [hgm, Real.mul_rpow hq0.le (grid istar).2.le, hrp q hq0.le]
        field_simp
      rw [hΔeq]
      refine mul_le_mul_of_nonneg_left ?_ hsq0.le
      linarith
  obtain ⟨i₀, hi₀mem, hi₀eq⟩ :
      ∃ i₀, i₀ ∈ Finset.range (N + 1) ∧
        (Finset.range (N + 1)).inf' Finset.nonempty_range_add_one (fun i =>
            (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), φ lam * |1 - lam * flt (grid i) lam|) * ρ +
              Real.sqrt (Cflt * CF) * δ * (grid i : ℝ) ^ (-(1 : ℝ) / 2)) =
          (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), φ lam * |1 - lam * flt (grid i₀) lam|) * ρ +
            Real.sqrt (Cflt * CF) * δ * (grid i₀ : ℝ) ^ (-(1 : ℝ) / 2) :=
    Finset.exists_mem_eq_inf' _ _
  have hi₀N : i₀ ≤ N := by
    have h := Finset.mem_range.mp hi₀mem
    omega
  have hfin : Real.sqrt (Cflt * CF) * δ * (grid istar : ℝ) ^ (-(1 : ℝ) / 2) ≤
      Real.sqrt q * (Finset.range (N + 1)).inf' Finset.nonempty_range_add_one (fun i =>
        (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), φ lam * |1 - lam * flt (grid i) lam|) * ρ +
          Real.sqrt (Cflt * CF) * δ * (grid i : ℝ) ^ (-(1 : ℝ) / 2)) := by
    rw [hi₀eq]
    exact hstep2 i₀ hi₀N
  linarith

end AutoIp

end _thm_balancing_oracle
