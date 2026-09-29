/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_12_picard._def_source_set
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_filter
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
public import AutoIp._part_2_reg._ch_19_general_source_conditions._def_general_qualification
public import AutoIp._part_2_reg._ch_22_balancing._def_balancing
import AutoIp.Auxiliary.Geometric
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_filter_norm_bound
import AutoIp._part_2_reg._ch_19_general_source_conditions._lem_general_omega
import AutoIp._part_2_reg._ch_19_general_source_conditions._lem_holder_is_index
import AutoIp._part_2_reg._ch_22_balancing._lem_balancing_nonempty
public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_qualification
import AutoIp._part_2_reg._ch_22_balancing._lem_balancing_le_star

section _cor_balancing_adaptive

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Adaptive order optimality: for `x† ∈ X_{ν,ρ}`, a grid with every `αᵢ ≤ κ` and an index
`i` with `αᵢ ∈ [c (δ/ρ)^(2/(ν+1)), C (δ/ρ)^(2/(ν+1))]`,
`‖x_{i₊} - x†‖ ≤ 6√q (C_R c^(-1/2) + C_ν C^(ν/2)) δ^(ν/(ν+1)) ρ^(1/(ν+1))`, with
`C_R = √(C_φ C_F)`. The index `i₊` is formed without `ν` or `ρ`.

The hypothesis `ν ∈ (0,ν₀]` is taken as (Q_ν) with constant `C_ν`, which is what `C_ν`
refers to. -/
public theorem balancing_orderOptimal (hs : IsSingularSystem K σ v u) {flt : Set.Ioi (0 : ℝ) → ℝ
    → ℝ}
    {Cflt CF Cν : ℝ} (hflt : IsRegularizingFilter K flt Cflt)
    (hF : HasFilterBound K flt CF)
    {ν ρ : ℝ} (hν : 0 < ν) (hρ : 0 < ρ)
    (hQ : HasQualification K flt (fun t => t ^ (ν / 2)) Cν)
    {y : F} (hy : y ∈ mpDomain K) (hx : moorePenrose K ⟨y, hy⟩ ∈ sourceSet hs ν hν ρ hρ)
    {δ : ℝ} (hδ : 0 < δ) {z : F} (hz : ‖y - z‖ ≤ δ)
    {N : ℕ} {grid : ℕ → Set.Ioi (0 : ℝ)} {q : ℝ} (hq : 1 < q)
    (hκ : ∀ i ≤ N, (grid i : ℝ) ≤ ‖K‖ ^ 2)
    (hgeom : ∀ i, i + 1 ≤ N → (grid i : ℝ) = q * (grid (i + 1) : ℝ))
    {cl cu : ℝ} (hcl : 0 < cl) (hcu : 0 < cu)
    (hgrid : ∃ i ≤ N, cl * (δ / ρ) ^ (2 / (ν + 1)) ≤ (grid i : ℝ) ∧
      (grid i : ℝ) ≤ cu * (δ / ρ) ^ (2 / (ν + 1))) :
    ‖spectralReg hs flt (hflt.exists_bound_on_spectrum hs)
          (grid (balancingIndex (spectralReg hs flt (hflt.exists_bound_on_spectrum hs)) (Real.sqrt
              (Cflt * CF)) δ (mul_nonneg (Real.sqrt_nonneg _) hδ.le) N grid z)) z -
        moorePenrose K ⟨y, hy⟩‖ ≤
      6 * Real.sqrt q *
          (Real.sqrt (Cflt * CF) * cl ^ (-(1 : ℝ) / 2) + Cν * cu ^ (ν / 2)) *
        δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1)) := by
  -- `i₀` is the *oracle* index: the grid point whose scale brackets the a priori optimal
  -- `(δ/ρ) ^ (2/(ν+1))`.  `hA` bounds the propagated data term there and `hB` bounds the
  -- approximation term at every index at or beyond it -- the two halves of the target rate.
  -- The rule picks `ip` instead, and the proof compares the two.
  obtain ⟨i₀, hi₀N, hi₀l, hi₀u⟩ := hgrid
  have hCR0 : (0 : ℝ) ≤ Real.sqrt (Cflt * CF) := Real.sqrt_nonneg _
  have hq0 : (0 : ℝ) < q := by linarith
  have hsq0 : (0 : ℝ) < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hsqne : Real.sqrt q ≠ 0 := ne_of_gt hsq0
  have hq1 : (1 : ℝ) ≤ Real.sqrt q := by
    have h := Real.sqrt_le_sqrt hq.le
    simpa using h
  have hν1 : (0 : ℝ) < ν + 1 := by linarith
  have hν1' : ν + 1 ≠ 0 := ne_of_gt hν1
  have hCF0 : (0 : ℝ) ≤ CF := hF.const_pos.le
  have hrp : ∀ t : ℝ, 0 ≤ t → t ^ (-(1 : ℝ) / 2) = (Real.sqrt t)⁻¹ := fun t ht => by
    rw [Real.sqrt_eq_rpow, neg_div, Real.rpow_neg ht]
  have hanti : ∀ i j, i ≤ j → j ≤ N → (grid j : ℝ) ≤ (grid i : ℝ) :=
    fun i j hij hjN => as_le_of_geometric hq hgeom hij hjN
  have hΔ : ∀ i j, i ≤ j → j ≤ N → (grid i : ℝ) ^ (-(1 : ℝ) / 2) ≤ (grid j : ℝ) ^ (-(1 : ℝ) / 2) :=
    fun i j hij hjN => rpow_neg_half_le_of_geometric hq hgeom hij hjN
  have hφi : IsIndexFunction (‖K‖ ^ 2) (fun t => t ^ (ν / 2)) := isIndexFunction_rpow hν _
  have hx' : moorePenrose K ⟨y, hy⟩ ∈ sourceSetIndex hs (fun t => t ^ (ν / 2))
      (hφi.exists_bound_on_spectrum hs) ρ hρ := by
    rw [sourceSetIndex_rpow hs hν hρ]; exact hx
  have hCν0 : (0 : ℝ) ≤ Cν := hQ.const_nonneg
  have herr : ∀ i, i ≤ N → ‖spectralReg hs flt (hflt.exists_bound_on_spectrum hs) (grid
      i) z - moorePenrose K ⟨y, hy⟩‖ ≤
      Cν * (grid i : ℝ) ^ (ν / 2) * ρ +
        Real.sqrt (Cflt * CF) * δ * (grid i : ℝ) ^ (-(1 : ℝ) / 2) := by
    intro i hi
    have h1 := norm_spectralReg_sub_moorePenrose_le_bias_add hs hflt hF hφi hρ hy hx' hz (grid i)
    have h2 := mul_le_mul_of_nonneg_right (hQ.omega_le (grid i) (hκ i hi)) hρ.le
    linarith
  have hdr : ∀ e : ℝ, ((δ / ρ) ^ (2 / (ν + 1))) ^ e
      = δ ^ (2 * e / (ν + 1)) / ρ ^ (2 * e / (ν + 1)) := by
    intro e
    have he : 2 / (ν + 1) * e = 2 * e / (ν + 1) := by ring
    rw [← Real.rpow_mul (div_pos hδ hρ).le, he, Real.div_rpow hδ.le hρ.le]
  have key1 : δ * ((δ / ρ) ^ (2 / (ν + 1))) ^ (-(1 : ℝ) / 2)
      = δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1)) := by
    rw [hdr]
    have e1 : 2 * (-(1 : ℝ) / 2) / (ν + 1) = -(1 / (ν + 1)) := by ring
    have e2 : ν / (ν + 1) = 1 - 1 / (ν + 1) := by field_simp; ring
    rw [e1, e2, Real.rpow_neg hδ.le, Real.rpow_neg hρ.le, Real.rpow_sub hδ, Real.rpow_one,
      inv_div_inv]
    ring
  have key2 : ((δ / ρ) ^ (2 / (ν + 1))) ^ (ν / 2) * ρ
      = δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1)) := by
    rw [hdr]
    have e3 : 2 * (ν / 2) / (ν + 1) = ν / (ν + 1) := by ring
    have e4 : (1 : ℝ) / (ν + 1) = 1 - ν / (ν + 1) := by field_simp; ring
    rw [e3, e4, Real.rpow_sub hρ, Real.rpow_one]
    ring
  have hPnn : (0 : ℝ) ≤ δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1)) :=
    mul_nonneg (Real.rpow_nonneg hδ.le _) (Real.rpow_nonneg hρ.le _)
  have hAnn : (0 : ℝ) ≤ Real.sqrt (Cflt * CF) * cl ^ (-(1 : ℝ) / 2) *
      (δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1))) :=
    mul_nonneg (mul_nonneg hCR0 (Real.rpow_nonneg hcl.le _)) hPnn
  have hBnn : (0 : ℝ) ≤ Cν * cu ^ (ν / 2) * (δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1))) :=
    mul_nonneg (mul_nonneg hCν0 (Real.rpow_nonneg hcu.le _)) hPnn
  have hA : Real.sqrt (Cflt * CF) * δ * (grid i₀ : ℝ) ^ (-(1 : ℝ) / 2)
      ≤ Real.sqrt (Cflt * CF) * cl ^ (-(1 : ℝ) / 2) *
        (δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1))) := by
    have hb : (0 : ℝ) < cl * (δ / ρ) ^ (2 / (ν + 1)) :=
      mul_pos hcl (Real.rpow_pos_of_pos (div_pos hδ hρ) _)
    have h1 : (grid i₀ : ℝ) ^ (-(1 : ℝ) / 2) ≤ (cl * (δ / ρ) ^ (2 / (ν + 1))) ^ (-(1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos hb hi₀l (by norm_num)
    have h2 : (cl * (δ / ρ) ^ (2 / (ν + 1))) ^ (-(1 : ℝ) / 2)
        = cl ^ (-(1 : ℝ) / 2) * ((δ / ρ) ^ (2 / (ν + 1))) ^ (-(1 : ℝ) / 2) :=
      Real.mul_rpow hcl.le (Real.rpow_nonneg (div_pos hδ hρ).le _)
    have h3 : (0 : ℝ) ≤ Real.sqrt (Cflt * CF) * δ := mul_nonneg hCR0 hδ.le
    calc Real.sqrt (Cflt * CF) * δ * (grid i₀ : ℝ) ^ (-(1 : ℝ) / 2)
        ≤ Real.sqrt (Cflt * CF) * δ * (cl ^ (-(1 : ℝ) / 2) *
            ((δ / ρ) ^ (2 / (ν + 1))) ^ (-(1 : ℝ) / 2)) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 h3
      _ = Real.sqrt (Cflt * CF) * cl ^ (-(1 : ℝ) / 2) *
            (δ * ((δ / ρ) ^ (2 / (ν + 1))) ^ (-(1 : ℝ) / 2)) := by ring
      _ = Real.sqrt (Cflt * CF) * cl ^ (-(1 : ℝ) / 2) *
            (δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1))) := by rw [key1]
  have hB : ∀ i, i ≤ N → i₀ ≤ i → Cν * (grid i : ℝ) ^ (ν / 2) * ρ
      ≤ Cν * cu ^ (ν / 2) * (δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1))) := by
    intro i hiN hi₀i
    have h1 : (grid i : ℝ) ≤ cu * (δ / ρ) ^ (2 / (ν + 1)) := (hanti i₀ i hi₀i hiN).trans hi₀u
    have h2 : (grid i : ℝ) ^ (ν / 2) ≤ (cu * (δ / ρ) ^ (2 / (ν + 1))) ^ (ν / 2) :=
      Real.rpow_le_rpow (grid i).2.le h1 (by linarith)
    have h3 : (cu * (δ / ρ) ^ (2 / (ν + 1))) ^ (ν / 2)
        = cu ^ (ν / 2) * ((δ / ρ) ^ (2 / (ν + 1))) ^ (ν / 2) :=
      Real.mul_rpow hcu.le (Real.rpow_nonneg (div_pos hδ hρ).le _)
    calc Cν * (grid i : ℝ) ^ (ν / 2) * ρ
        ≤ Cν * (cu ^ (ν / 2) * ((δ / ρ) ^ (2 / (ν + 1))) ^ (ν / 2)) * ρ := by
          rw [← h3]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hCν0) hρ.le
      _ = Cν * cu ^ (ν / 2) * (((δ / ρ) ^ (2 / (ν + 1))) ^ (ν / 2) * ρ) := by ring
      _ = Cν * cu ^ (ν / 2) * (δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1))) := by rw [key2]
  -- Minimality of `ip`, read as failure of the balancing condition below `ip`, is what makes
  -- the second case below work: it is a *lower* bound on a quantity the oracle bounds from
  -- above.
  obtain ⟨hipN, hipcond⟩ := balancingIndex_spec (spectralReg hs flt
      (hflt.exists_bound_on_spectrum hs)) hCR0 hδ.le N z
  have hnotmem : ∀ m : ℕ, m ≤ N →
      m < balancingIndex (spectralReg hs flt (hflt.exists_bound_on_spectrum hs)) (Real.sqrt (Cflt
          * CF)) δ (mul_nonneg (Real.sqrt_nonneg _) hδ.le) N grid z →
      ∃ j, m ≤ j ∧ j ≤ N ∧
        4 * (Real.sqrt (Cflt * CF) * δ * (grid j : ℝ) ^ (-(1 : ℝ) / 2)) <
          ‖spectralReg hs flt (hflt.exists_bound_on_spectrum hs) (grid
              m) z - spectralReg hs flt (hflt.exists_bound_on_spectrum hs) (grid j) z‖ :=
    fun m hmN hlt => exists_gt_of_lt_balancingIndex _ hmN hlt
  have hRHS : 6 * Real.sqrt q *
        (Real.sqrt (Cflt * CF) * cl ^ (-(1 : ℝ) / 2) + Cν * cu ^ (ν / 2)) *
        δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1))
      = 6 * Real.sqrt q * (Real.sqrt (Cflt * CF) * cl ^ (-(1 : ℝ) / 2) *
            (δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1)))
          + Cν * cu ^ (ν / 2) * (δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1)))) := by ring
  rw [hRHS]
  set ip := balancingIndex (spectralReg hs flt (hflt.exists_bound_on_spectrum hs)) (Real.sqrt
      (Cflt * CF)) δ (mul_nonneg (Real.sqrt_nonneg _) hδ.le) N grid z with hipdef
  -- The split is on which side of the oracle the rule landed.  `grid` is antitone, so
  -- `ip ≤ i₀` means the chosen scale is *at least* the oracle scale, and `i₀ < ip` means it
  -- undershot.  The two cases use the balancing condition in opposite directions.
  by_cases hcase : ip ≤ i₀
  · -- The chosen index is at or above the oracle, so the balancing condition at `ip`
    -- applies to `i₀` itself: routing through `R (grid i₀) z` costs the oracle error plus one
    -- balancing term, and `hA`, `hB` bound both by the target rate.
    have h1 := hipcond i₀ hcase hi₀N
    have h2 := herr i₀ hi₀N
    have h3 := hB i₀ hi₀N le_rfl
    have h4 := norm_sub_le_norm_sub_add_norm_sub (spectralReg hs flt
        (hflt.exists_bound_on_spectrum hs) (grid
            ip) z) (spectralReg hs flt (hflt.exists_bound_on_spectrum hs)
      (grid i₀) z)
      (moorePenrose K ⟨y, hy⟩)
    nlinarith [mul_nonneg (sub_nonneg.mpr hq1) (add_nonneg hAnn hBnn), hAnn, hBnn, hA]
  · -- The chosen index undershot the oracle.  Then `m = ip - 1` is still at or beyond the
    -- oracle, and minimality of `ip` says the condition fails at `m`: some `j ≥ m` has
    -- `4 √(Cflt CF) δ (grid j) ^ (-1/2) < ‖R (grid m) z - R (grid j) z‖`.  Both `m` and `j` are
    -- beyond the oracle, so `hB` bounds their approximation terms, and the failure inverts
    -- into an upper bound on the data term at `m` (`hΔmB`).  One geometric step
    -- `grid m = q * grid ip` carries that to `ip`, at the cost of the `√q` in the statement.
    have hcase' : i₀ < ip := by omega
    obtain ⟨m, hm⟩ : ∃ m, ip = m + 1 := ⟨ip - 1, by omega⟩
    have hmN : m ≤ N := by omega
    have hmlt : m < ip := by omega
    have hi₀m : i₀ ≤ m := by omega
    obtain ⟨j, hmj, hjN, hjgt⟩ := hnotmem m hmN hmlt
    have h1 := herr m hmN
    have h2 := herr j hjN
    have h3 := hB m hmN hi₀m
    have h4 := hB j hjN (hi₀m.trans hmj)
    have h5 : Real.sqrt (Cflt * CF) * δ * (grid m : ℝ) ^ (-(1 : ℝ) / 2)
        ≤ Real.sqrt (Cflt * CF) * δ * (grid j : ℝ) ^ (-(1 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left (hΔ m j hmj hjN) (mul_nonneg hCR0 hδ.le)
    have h6 := norm_sub_le_norm_sub_add_norm_sub (spectralReg hs flt
        (hflt.exists_bound_on_spectrum hs) (grid m) z) (moorePenrose K ⟨y, hy⟩)
      (spectralReg hs flt (hflt.exists_bound_on_spectrum hs) (grid j) z)
    rw [norm_sub_rev (moorePenrose K ⟨y, hy⟩)] at h6
    have hΔmB : Real.sqrt (Cflt * CF) * δ * (grid m : ℝ) ^ (-(1 : ℝ) / 2)
        ≤ Cν * cu ^ (ν / 2) * (δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1))) := by linarith
    have hgm : (grid m : ℝ) = q * (grid ip : ℝ) := by rw [hm]; exact hgeom m (by omega)
    have hΔip : Real.sqrt (Cflt * CF) * δ * (grid ip : ℝ) ^ (-(1 : ℝ) / 2)
        = Real.sqrt q * (Real.sqrt (Cflt * CF) * δ * (grid m : ℝ) ^ (-(1 : ℝ) / 2)) := by
      rw [hgm, Real.mul_rpow hq0.le (grid ip).2.le, hrp q hq0.le]
      field_simp
    have h7 := herr ip hipN
    have h8 := hB ip hipN (le_of_lt hcase')
    nlinarith [mul_le_mul_of_nonneg_left hΔmB hsq0.le,
      mul_nonneg (sub_nonneg.mpr hq1) hBnn, mul_nonneg hsq0.le hAnn]

end AutoIp

end _cor_balancing_adaptive
