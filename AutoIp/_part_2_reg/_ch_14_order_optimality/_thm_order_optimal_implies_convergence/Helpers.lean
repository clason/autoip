/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_14_order_optimality._def_order_optimal
import AutoIp._part_1_funcanal._ch_04_orthonormal_series._lem_inner_through_series
import AutoIp._part_1_funcanal._ch_08_svd._lem_svd_companion
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_hom
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_equations
import AutoIp._part_2_reg._ch_11_moore_penrose._thm_mp_inverse
import AutoIp.Auxiliary.Rpow
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound

section

open scoped InnerProductSpace
namespace AutoIp

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Every nonzero `x ∈ Ker(K)ᗮ` is approximated by elements `p(t) ∈ X_{ν, ‖x‖/t^ν} ∩ Ker(K)ᗮ`,
`t > 0`, with `‖K (x - p(t))‖ ≤ t ‖x - p(t)‖`, `‖x - p(t)‖ ≤ ‖x‖` nondecreasing in `t`, and
`inf_{t>0} ‖x - p(t)‖ = 0`. -/
public theorem exists_sourceSet_approximation (hs : IsSingularSystem K σ v u) {ν : ℝ} (hν : 0 < ν)
    {x : E} (hx : x ∈ K.toLinearMap.kerᗮ) (hx0 : 0 < ‖x‖) :
    ∃ p : ℝ → E,
      (∀ t, 0 < t → p t ∈ K.toLinearMap.kerᗮ) ∧
      (∀ (t : ℝ) (ht : 0 < t), p t ∈ sourceSet hs ν hν (‖x‖ / t ^ ν)
        (div_pos hx0 (Real.rpow_pos_of_pos ht ν))) ∧
      (∀ t, 0 < t → ‖K (x - p t)‖ ≤ t * ‖x - p t‖) ∧
      (∀ t₁ t₂, 0 < t₁ → t₁ ≤ t₂ → ‖x - p t₁‖ ≤ ‖x - p t₂‖) ∧
      (∀ t, 0 < t → ‖x - p t‖ ≤ ‖x‖) ∧
      (∀ η, 0 < η → ∃ t, 0 < t ∧ ‖x - p t‖ < η) := by
  classical
  set c : ι → 𝕜 := fun i => (inner 𝕜 (v i) x : 𝕜) with hcdef
  have hcx : HasSum (fun i => c i • v i) x := IsSingularSystem.hasSum_inner_smul hs hx
  have hsumd : Summable (fun i => ‖c i‖ ^ 2) :=
    (hs.orthonormal_left.summable_iff_norm_sq_summable c).1 hcx.summable
  have hnx : ‖x‖ ^ 2 = ∑' i, ‖c i‖ ^ 2 := hs.orthonormal_left.norm_sq_eq_tsum_norm_sq hcx
  set χ : ℝ → ℝ → ℝ := fun t s => if t ^ 2 ≤ s then 1 else 0 with hχdef
  have hbχ : ∀ t : ℝ, ∃ C, ∀ i, |χ t (σ i ^ 2)| ≤ C := fun t =>
    ⟨1, fun i => by simp only [hχdef]; split <;> norm_num⟩
  have hχ0 : ∀ t : ℝ, 0 < t → χ t 0 = 0 := fun t ht => by
    simp only [hχdef]
    exact ite_eq_right (not_le.2 (by positivity))
  have hpt : ∀ t : ℝ, 0 < t →
      HasSum (fun i => ((RCLike.ofReal (χ t (σ i ^ 2)) : 𝕜) * c i) • v i)
        (hs.funCalc (χ t) (hbχ t) x) := by
    intro t ht
    have h := hs.hasSum_funCalc_sub_starProjection (hbχ t) x
    rw [hχ0 t ht] at h
    simpa using h
  have hqt : ∀ t : ℝ, 0 < t →
      HasSum (fun i => ((RCLike.ofReal (1 - χ t (σ i ^ 2)) : 𝕜) * c i) • v i)
        (x - hs.funCalc (χ t) (hbχ t) x) := by
    intro t ht
    have h := hcx.sub (hpt t ht)
    have hfun : (fun i => c i • v i - ((RCLike.ofReal (χ t (σ i ^ 2)) : 𝕜) * c i) • v i)
        = fun i => ((RCLike.ofReal (1 - χ t (σ i ^ 2)) : 𝕜) * c i) • v i := by
      funext i
      rw [← sub_smul]
      congr 1
      push_cast
      ring
    rwa [hfun] at h
  have hnormq : ∀ t : ℝ, 0 < t →
      ‖x - hs.funCalc (χ t) (hbχ t) x‖ ^ 2 = ∑' i, (1 - χ t (σ i ^ 2)) ^ 2 * ‖c i‖ ^ 2 := by
    intro t ht
    rw [hs.orthonormal_left.norm_sq_eq_tsum_norm_sq (hqt t ht)]
    refine tsum_congr fun i => ?_
    rw [norm_mul, RCLike.norm_ofReal, mul_pow, sq_abs]
  have hnormKq : ∀ t : ℝ, 0 < t →
      ‖K (x - hs.funCalc (χ t) (hbχ t) x)‖ ^ 2
        = ∑' i, σ i ^ 2 * ((1 - χ t (σ i ^ 2)) ^ 2 * ‖c i‖ ^ 2) := by
    intro t ht
    rw [IsSingularSystem.norm_map_sq_eq_tsum_of_hasSum hs (hqt t ht)]
    refine tsum_congr fun i => ?_
    rw [norm_mul, RCLike.norm_ofReal, mul_pow, sq_abs]
  have hχle : ∀ (t : ℝ) (s : ℝ), (1 - χ t s) ^ 2 ≤ 1 := by
    intro t s
    simp only [hχdef]
    split <;> norm_num
  have hsumq : ∀ t : ℝ, Summable (fun i => (1 - χ t (σ i ^ 2)) ^ 2 * ‖c i‖ ^ 2) := by
    intro t
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) hsumd
    nlinarith [hχle t (σ i ^ 2), sq_nonneg ‖c i‖, norm_nonneg (c i),
      sq_nonneg (1 - χ t (σ i ^ 2))]
  have hvperp : ∀ i, v i ∈ (LinearMap.ker K.toLinearMap)ᗮ := fun i => by
    rw [← hs.span_left]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)
  have hmemperp : ∀ t : ℝ, 0 < t →
      hs.funCalc (χ t) (hbχ t) x ∈ (LinearMap.ker K.toLinearMap)ᗮ := by
    intro t ht
    rw [Submodule.mem_orthogonal]
    intro z hz
    have h := HasSum.inner_right (𝕜 := 𝕜) (hpt t ht) z
    have hz0 : ∀ i, (inner 𝕜 z (((RCLike.ofReal (χ t (σ i ^ 2)) : 𝕜) * c i) • v i) : 𝕜) = 0 := by
      intro i
      rw [inner_smul_right, (Submodule.mem_orthogonal _ _).1 (hvperp i) z hz, mul_zero]
    simp only [hz0] at h
    exact h.unique hasSum_zero
  refine ⟨fun t => hs.funCalc (χ t) (hbχ t) x, hmemperp, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    set ξ : ℝ → ℝ := fun s => if t ^ 2 ≤ s then (s ^ (ν / 2))⁻¹ else 0 with hξdef
    have htν : (0 : ℝ) < t ^ ν := Real.rpow_pos_of_pos ht _
    have ht2ν := rpow_sq_div_two ht.le ν
    have hξbound : ∀ s : ℝ, 0 ≤ s → |ξ s| ≤ (t ^ ν)⁻¹ := by
      intro s hs0
      simp only [hξdef]
      split
      · next hts =>
        have hsp : (0 : ℝ) < s ^ (ν / 2) :=
          Real.rpow_pos_of_pos (lt_of_lt_of_le (by positivity) hts) _
        rw [abs_of_nonneg (inv_nonneg.2 hsp.le)]
        have hge : t ^ ν ≤ s ^ (ν / 2) := by
          rw [← ht2ν]
          exact Real.rpow_le_rpow (by positivity) hts (by positivity)
        have hinv := one_div_le_one_div_of_le htν hge
        rwa [one_div, one_div] at hinv
      · simpa using (inv_nonneg.2 htν.le)
    have hbξIcc : ∃ C, ∀ s ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |ξ s| ≤ C :=
      ⟨(t ^ ν)⁻¹, fun s hs => hξbound s hs.1⟩
    have hbξ : ∃ C, ∀ i, |ξ (σ i ^ 2)| ≤ C :=
      ⟨(t ^ ν)⁻¹, fun i => hξbound _ (by positivity)⟩
    have hξ0 : ξ 0 = 0 := ite_eq_right (not_le.2 (by positivity))
    have hbabs : ∃ C, ∀ i, |(fun s : ℝ => s ^ (ν / 2)) (σ i ^ 2)| ≤ C :=
      hs.exists_bound_rpow_sq (by positivity)
    have hcomp : hs.absRpow ν hν.le (hs.funCalc ξ hbξ x) = hs.funCalc (χ t) (hbχ t) x := by
      have hcong : hs.funCalc ((fun s : ℝ => s ^ (ν / 2)) * ξ)
          (exists_forall_abs_mul_sq_le hbabs hbξ) = hs.funCalc (χ t) (hbχ t) := by
        refine hs.funCalc_congr _ _ fun s hs => ?_
        simp only [Pi.mul_apply, hξdef, hχdef]
        split
        · next hts =>
          have hsp : (0 : ℝ) < s ^ (ν / 2) :=
            Real.rpow_pos_of_pos (lt_of_lt_of_le (by positivity) hts) _
          rw [mul_inv_cancel₀ hsp.ne']
        · rw [mul_zero]
      have h2 : hs.funCalc (χ t) (hbχ t)
          = hs.funCalc (fun s : ℝ => s ^ (ν / 2)) hbabs ∘L hs.funCalc ξ hbξ := by
        rw [← hcong, hs.funCalc_mul' hbabs hbξ]
      rw [hs.absRpow_def ν hν.le hbabs, h2, ContinuousLinearMap.comp_apply]
    have hnormw : ‖hs.funCalc ξ hbξ x‖ ^ 2 = ∑' i, ξ (σ i ^ 2) ^ 2 * ‖c i‖ ^ 2 := by
      have h := hs.hasSum_funCalc_sub_starProjection hbξ x
      rw [hξ0] at h
      simp only [RCLike.ofReal_zero, zero_smul, sub_zero] at h
      rw [hs.orthonormal_left.norm_sq_eq_tsum_norm_sq h]
      refine tsum_congr fun i => ?_
      rw [norm_mul, RCLike.norm_ofReal, mul_pow, sq_abs]
    have hle : ‖hs.funCalc ξ hbξ x‖ ^ 2 ≤ (‖x‖ / t ^ ν) ^ 2 := by
      have hbnd : ∀ i, ξ (σ i ^ 2) ^ 2 * ‖c i‖ ^ 2 ≤ ((t ^ ν)⁻¹) ^ 2 * ‖c i‖ ^ 2 := by
        intro i
        have h1 := hξbound (σ i ^ 2) (by positivity)
        have h2 : ξ (σ i ^ 2) ^ 2 ≤ ((t ^ ν)⁻¹) ^ 2 := by
          nlinarith [abs_nonneg (ξ (σ i ^ 2)), sq_abs (ξ (σ i ^ 2)),
            inv_nonneg.2 htν.le]
        nlinarith [sq_nonneg ‖c i‖, norm_nonneg (c i)]
      have hsum2 : Summable (fun i => ((t ^ ν)⁻¹) ^ 2 * ‖c i‖ ^ 2) := hsumd.mul_left _
      have hsum1 : Summable (fun i => ξ (σ i ^ 2) ^ 2 * ‖c i‖ ^ 2) :=
        Summable.of_nonneg_of_le (fun i => by positivity) hbnd hsum2
      calc ‖hs.funCalc ξ hbξ x‖ ^ 2 = ∑' i, ξ (σ i ^ 2) ^ 2 * ‖c i‖ ^ 2 := hnormw
        _ ≤ ∑' i, ((t ^ ν)⁻¹) ^ 2 * ‖c i‖ ^ 2 := Summable.tsum_le_tsum hbnd hsum1 hsum2
        _ = ((t ^ ν)⁻¹) ^ 2 * ‖x‖ ^ 2 := by rw [tsum_mul_left, ← hnx]
        _ = (‖x‖ / t ^ ν) ^ 2 := by rw [div_pow, inv_pow]; ring
    rw [mem_sourceSet_iff]
    refine ⟨hs.funCalc ξ hbξ x, ?_, hcomp⟩
    have hnn : (0 : ℝ) ≤ ‖x‖ / t ^ ν := by positivity
    exact le_of_pow_le_pow_left₀ two_ne_zero hnn hle
  · intro t ht
    have hb : ‖K (x - hs.funCalc (χ t) (hbχ t) x)‖ ^ 2
        ≤ (t * ‖x - hs.funCalc (χ t) (hbχ t) x‖) ^ 2 := by
      rw [hnormKq t ht, mul_pow, hnormq t ht, ← tsum_mul_left]
      refine Summable.tsum_le_tsum (fun i => ?_) ?_ ((hsumq t).mul_left _)
      · have hpt2 : σ i ^ 2 * ((1 - χ t (σ i ^ 2)) ^ 2 * ‖c i‖ ^ 2)
            ≤ t ^ 2 * ((1 - χ t (σ i ^ 2)) ^ 2 * ‖c i‖ ^ 2) := by
          rcases le_or_gt (t ^ 2) (σ i ^ 2) with hcase | hcase
          · have : χ t (σ i ^ 2) = 1 := ite_eq_left hcase
            rw [this]
            norm_num
          · have hnn : (0 : ℝ) ≤ (1 - χ t (σ i ^ 2)) ^ 2 * ‖c i‖ ^ 2 := by positivity
            nlinarith
        exact hpt2
      · refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
          ((hsumq t).mul_left (t ^ 2))
        rcases le_or_gt (t ^ 2) (σ i ^ 2) with hcase | hcase
        · have : χ t (σ i ^ 2) = 1 := ite_eq_left hcase
          rw [this]; norm_num
        · have hnn : (0 : ℝ) ≤ (1 - χ t (σ i ^ 2)) ^ 2 * ‖c i‖ ^ 2 := by positivity
          nlinarith
    exact le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg ht.le (norm_nonneg _)) hb
  · intro t₁ t₂ ht₁ ht₁₂
    have ht₂ : 0 < t₂ := lt_of_lt_of_le ht₁ ht₁₂
    have hsq : ‖x - hs.funCalc (χ t₁) (hbχ t₁) x‖ ^ 2 ≤ ‖x - hs.funCalc (χ t₂) (hbχ t₂) x‖ ^ 2 := by
      rw [hnormq t₁ ht₁, hnormq t₂ ht₂]
      refine Summable.tsum_le_tsum (fun i => ?_) (hsumq t₁) (hsumq t₂)
      have hmono : (1 - χ t₁ (σ i ^ 2)) ^ 2 ≤ (1 - χ t₂ (σ i ^ 2)) ^ 2 := by
        simp only [hχdef]
        rcases le_or_gt (t₁ ^ 2) (σ i ^ 2) with h1 | h1
        · rw [ite_eq_left h1]; norm_num; positivity
        · rw [ite_eq_right (not_le.2 h1),
            ite_eq_right (not_le.2 (lt_of_lt_of_le h1 (by nlinarith)))]
      nlinarith [sq_nonneg ‖c i‖, norm_nonneg (c i)]
    exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hsq
  · intro t ht
    have hsq : ‖x - hs.funCalc (χ t) (hbχ t) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [hnormq t ht, hnx]
      refine Summable.tsum_le_tsum (fun i => ?_) (hsumq t) hsumd
      nlinarith [hχle t (σ i ^ 2), sq_nonneg ‖c i‖, norm_nonneg (c i),
        sq_nonneg (1 - χ t (σ i ^ 2))]
    exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hsq
  · intro η hη
    obtain ⟨S, hS⟩ : ∃ S : Finset ι, (∑' i : { j // j ∉ S }, ‖c i‖ ^ 2) < η ^ 2 := by
      have h := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero (fun i => ‖c i‖ ^ 2))).2
        (η ^ 2) (by positivity)
      simp only [Filter.eventually_atTop] at h
      obtain ⟨S, hS⟩ := h
      exact ⟨S, hS S le_rfl⟩
    set t : ℝ := if h : S.Nonempty then S.inf' h σ else 1 with htdef
    have ht : 0 < t := by
      rw [htdef]
      split
      · next h => exact (Finset.lt_inf'_iff h).2 fun i _ => hs.pos i
      · exact one_pos
    have hmemS : ∀ i ∈ S, t ≤ σ i := by
      intro i hi
      have hne : S.Nonempty := ⟨i, hi⟩
      rw [htdef, dite_eq_left hne]
      exact Finset.inf'_le _ hi
    refine ⟨t, ht, ?_⟩
    have hzero : ∀ i ∈ S, (1 - χ t (σ i ^ 2)) ^ 2 * ‖c i‖ ^ 2 = 0 := by
      intro i hi
      have : t ^ 2 ≤ σ i ^ 2 := by nlinarith [hmemS i hi, ht.le, (hs.pos i).le]
      simp only [hχdef, ite_eq_left this]
      norm_num
    have hsplit := (hsumq t).sum_add_tsum_subtype_compl S
    rw [Finset.sum_eq_zero hzero, zero_add] at hsplit
    have hcmp : (∑' i : { j // j ∉ S }, (1 - χ t (σ (i : ι) ^ 2)) ^ 2 * ‖c (i : ι)‖ ^ 2)
        ≤ ∑' i : { j // j ∉ S }, ‖c (i : ι)‖ ^ 2 := by
      refine Summable.tsum_le_tsum (fun i => ?_) ((hsumq t).subtype _) (hsumd.subtype _)
      nlinarith [hχle t (σ (i : ι) ^ 2), sq_nonneg ‖c (i : ι)‖, norm_nonneg (c (i : ι)),
        sq_nonneg (1 - χ t (σ (i : ι) ^ 2))]
    have hfin : ‖x - hs.funCalc (χ t) (hbχ t) x‖ ^ 2 < η ^ 2 := by
      rw [hnormq t ht, ← hsplit]
      exact lt_of_le_of_lt hcmp hS
    by_contra hcon
    push Not at hcon
    nlinarith [hcon, hη.le, hfin]

end AutoIp

end
