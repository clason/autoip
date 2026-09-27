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
import AutoIp._part_2_reg._ch_14_order_optimality._thm_order_optimal_implies_convergence.Helpers

section _thm_order_optimal_implies_convergence

section

namespace AutoIp

open Filter Topology
open scoped ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Let `K` have dense range, `{R_α} ⊆ L(Y,X)`, `α` a parameter choice rule and `τ₀ ≥ 1`.
If for every `τ > τ₀` the pair `(R_α, α_τ)`, `α_τ(δ, y^δ) := α(τδ, y^δ)`, is order optimal
for a fixed `ν > 0` and all `ρ > 0` with one constant `c`, then `(R_α, α_τ)` is a
convergent regularization method for every `τ > τ₀`. In place of compactness of `K` the
Lean takes a singular system of `K`, and it does not assume the range
infinite-dimensional. The positivity `0 < τ` is an argument because `α_τ` needs it. -/
public theorem isRegularizationMethod_of_orderOptimal (hs : IsSingularSystem K σ v u)
    (hdense : Dense (K.toLinearMap.range : Set F))
    (R : Set.Ioi (0 : ℝ) → F →L[𝕜] E) (a : ParameterChoice F) {ν : ℝ}
    {τ₀ c : ℝ} (hτ₀ : 1 ≤ τ₀)
    (hoo : ∀ τ > τ₀, ∀ ρ > (0 : ℝ), ∀ hτ : 0 < τ,
      IsOrderOptimal K (fun α z => R α z) (a.scale τ hτ) hs ν ρ c)
    {τ : ℝ} (hτ : τ₀ < τ) (hτ0 : 0 < τ) :
    IsRegularizationMethod K (fun α z => R α z) (a.scale τ hτ0) := by
  have hν : (0 : ℝ) < ν := (hoo τ hτ 1 one_pos hτ0).nu_pos
  have hc : (1 : ℝ) ≤ c := (hoo τ hτ 1 one_pos hτ0).one_le_const
  have hν1 : (0 : ℝ) < ν + 1 := by linarith
  have hνne : ν ≠ 0 := ne_of_gt hν
  have hν1ne : ν + 1 ≠ 0 := ne_of_gt hν1
  have hθ : (0 : ℝ) < ν / (ν + 1) := div_pos hν hν1
  have hθ1 : ν / (ν + 1) ≤ 1 := by rw [div_le_one hν1]; linarith
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
  intro y hy ε hε
  have hxdperp : moorePenrose K ⟨y, hy⟩ ∈ (LinearMap.ker K.toLinearMap)ᗮ :=
    moorePenrose_mem_orthogonal_ker ⟨_, hy⟩
  have hmemcl : y ∈ (LinearMap.range K.toLinearMap).topologicalClosure := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top.1 hdense]
    trivial
  have hKxd : K (moorePenrose K ⟨y, hy⟩) = y := by
    rw [apply_moorePenrose ⟨_, hy⟩]
    exact Submodule.starProjection_eq_self_iff.2 hmemcl
  have hmpK : ∀ w : E, w ∈ (LinearMap.ker K.toLinearMap)ᗮ → moorePenrose K ⟨K w,
      Submodule.mem_sup_left ⟨w, rfl⟩⟩ = w := by
    exact fun w hw => moorePenrose_apply_apply_of_mem_orthogonal hw
  by_cases hcase : ∃ w : E, hs.absRpow ν hν.le w = moorePenrose K ⟨y, hy⟩
  · obtain ⟨w, hw⟩ := hcase
    have hρ : (0 : ℝ) < ‖w‖ + 1 := by positivity
    have hmem : moorePenrose K ⟨y, hy⟩ ∈ sourceSet hs ν hν (‖w‖ + 1) hρ := by
      rw [mem_sourceSet_iff]
      exact ⟨w, by linarith, hw⟩
    have hoo' := (hoo τ hτ (‖w‖ + 1) hρ hτ0).worstCaseError_le
    have hApos : (0 : ℝ) < (‖w‖ + 1) ^ (1 / (ν + 1)) := Real.rpow_pos_of_pos hρ _
    have hA : (0 : ℝ) < c * (‖w‖ + 1) ^ (1 / (ν + 1)) := mul_pos hc0 hApos
    have hAne : c * (‖w‖ + 1) ^ (1 / (ν + 1)) ≠ 0 := ne_of_gt hA
    have hε2A : (0 : ℝ) < ε / (2 * (c * (‖w‖ + 1) ^ (1 / (ν + 1)))) :=
      div_pos hε (by linarith)
    refine ⟨(ε / (2 * (c * (‖w‖ + 1) ^ (1 / (ν + 1))))) ^ ((ν + 1) / ν),
      Real.rpow_pos_of_pos hε2A _, ?_⟩
    intro δ hδ z hz
    have hδ0 : 0 < δ := hδ.1
    have hbound := hoo' (moorePenrose K ⟨y, hy⟩) hmem δ hδ0
    rw [worstCaseError_congr K (fun α z => R α z) (a.scale τ hτ0) hKxd
      (Submodule.mem_sup_left ⟨moorePenrose K ⟨y, hy⟩, rfl⟩) hy δ hδ0] at hbound
    have hzball : z ∈ Metric.closedBall y δ := by
      rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
      exact hz
    have hstep : ‖R ((a.scale τ hτ0).param ⟨δ, hδ0⟩ z) z - moorePenrose K ⟨y, hy⟩‖ₑ
        ≤ worstCaseError K (fun α w' => R α w') (a.scale τ hτ0) y hy δ hδ0 := by
      have h := le_iSup₂ (α := ℝ≥0∞)
        (f := fun w' (_ : w' ∈ Metric.closedBall y δ) =>
          ‖(R ((a.scale τ hτ0).param ⟨δ, hδ0⟩ w')) w'
            - moorePenrose K ⟨y, hy⟩‖ₑ) z hzball
      simpa [worstCaseError] using h
    have hnn : (0 : ℝ) ≤ c * δ ^ (ν / (ν + 1)) * (‖w‖ + 1) ^ (1 / (ν + 1)) :=
      mul_nonneg (mul_nonneg hc0.le (Real.rpow_nonneg hδ0.le _)) hApos.le
    have hreal :=
      (ENNReal.ofReal_le_ofReal_iff hnn).1 ((ofReal_norm _).trans_le (hstep.trans hbound))
    refine lt_of_le_of_lt hreal ?_
    have hkey : δ ^ (ν / (ν + 1)) < ε / (2 * (c * (‖w‖ + 1) ^ (1 / (ν + 1)))) := by
      have h1 : ((ε / (2 * (c * (‖w‖ + 1) ^ (1 / (ν + 1))))) ^ ((ν + 1) / ν))
          ^ (ν / (ν + 1)) = ε / (2 * (c * (‖w‖ + 1) ^ (1 / (ν + 1)))) := by
        rw [← Real.rpow_mul hε2A.le,
          show (ν + 1) / ν * (ν / (ν + 1)) = 1 by field_simp]
        exact Real.rpow_one _
      calc δ ^ (ν / (ν + 1))
          < ((ε / (2 * (c * (‖w‖ + 1) ^ (1 / (ν + 1))))) ^ ((ν + 1) / ν)) ^ (ν / (ν + 1)) :=
            Real.rpow_lt_rpow hδ0.le hδ.2 hθ
        _ = _ := h1
    have heq : c * δ ^ (ν / (ν + 1)) * (‖w‖ + 1) ^ (1 / (ν + 1))
        = (c * (‖w‖ + 1) ^ (1 / (ν + 1))) * δ ^ (ν / (ν + 1)) := by ring
    rw [heq]
    calc (c * (‖w‖ + 1) ^ (1 / (ν + 1))) * δ ^ (ν / (ν + 1))
        < (c * (‖w‖ + 1) ^ (1 / (ν + 1))) * (ε / (2 * (c * (‖w‖ + 1) ^ (1 / (ν + 1))))) :=
          mul_lt_mul_of_pos_left hkey hA
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  · have hxd0 : moorePenrose K ⟨y, hy⟩ ≠ 0 := fun h0 => hcase ⟨0, by rw [map_zero, h0]⟩
    have hxdnorm : 0 < ‖moorePenrose K ⟨y, hy⟩‖ := norm_pos_iff.2 hxd0
    obtain ⟨p, hpperp, hpsrc, hpcontr, hpmono, hpbdd, hpvan⟩ :=
      exists_sourceSet_approximation hs hν hxdperp hxdnorm
    have hsum0 : (0 : ℝ) < τ + τ₀ := by linarith
    have hsumne : τ + τ₀ ≠ 0 := ne_of_gt hsum0
    have hq0 : (0 : ℝ) < (τ - τ₀) / (τ + τ₀) := div_pos (by linarith) hsum0
    have hq1 : (τ - τ₀) / (τ + τ₀) < 1 := by rw [div_lt_one hsum0]; linarith
    have hτ'0 : (0 : ℝ) < (τ + τ₀) / 2 := by linarith
    have hτ'τ₀ : τ₀ < (τ + τ₀) / 2 := by linarith
    have hxn : (0 : ℝ) < ‖moorePenrose K ⟨y, hy⟩‖ ^ (1 / (ν + 1)) :=
      Real.rpow_pos_of_pos hxdnorm _
    have hB0 : (0 : ℝ) < c * ‖moorePenrose K ⟨y, hy⟩‖ ^ (1 / (ν + 1)) := mul_pos hc0 hxn
    have hBne : (c * ‖moorePenrose K ⟨y, hy⟩‖ ^ (1 / (ν + 1)) : ℝ) ≠ 0 := ne_of_gt hB0
    have hXpos : (0 : ℝ) <
        (ε / (8 * (c * ‖moorePenrose K ⟨y, hy⟩‖ ^ (1 / (ν + 1))))) ^ ((ν + 1) / ν) :=
      Real.rpow_pos_of_pos (div_pos hε (by linarith)) _
    have hη0 : (0 : ℝ) < min (ε / 4)
        ((τ - τ₀) / (τ + τ₀) *
          (ε / (8 * (c * ‖moorePenrose K ⟨y, hy⟩‖ ^ (1 / (ν + 1))))) ^ ((ν + 1) / ν) / 4) :=
      lt_min (by linarith) (div_pos (mul_pos hq0 hXpos) (by norm_num))
    set η : ℝ := min (ε / 4)
      ((τ - τ₀) / (τ + τ₀) *
        (ε / (8 * (c * ‖moorePenrose K ⟨y, hy⟩‖ ^ (1 / (ν + 1))))) ^ ((ν + 1) / ν) / 4) with hηdef
    have hηε : η ≤ ε / 4 := min_le_left _ _
    have hηq : 4 * η / ((τ - τ₀) / (τ + τ₀))
        ≤ (ε / (8 * (c * ‖moorePenrose K ⟨y, hy⟩‖ ^ (1 / (ν + 1))))) ^ ((ν + 1) / ν) := by
      have h := min_le_right (ε / 4)
        ((τ - τ₀) / (τ + τ₀) *
          (ε / (8 * (c * ‖moorePenrose K ⟨y, hy⟩‖ ^ (1 / (ν + 1))))) ^ ((ν + 1) / ν) / 4)
      rw [← hηdef] at h
      rw [div_le_iff₀ hq0]
      nlinarith
    obtain ⟨s', hs'0, hs'⟩ := hpvan η hη0
    have hs0 : (0 : ℝ) < s' / 2 := by linarith
    have hs2 : ‖moorePenrose K ⟨y, hy⟩ - p (2 * (s' / 2))‖ < η := by
      rw [show 2 * (s' / 2) = s' by ring]; exact hs'
    have hgpos : ∀ t : ℝ, 0 < t → 0 < ‖K (moorePenrose K ⟨y, hy⟩ - p t)‖ := by
      intro t ht
      rw [norm_pos_iff]
      intro h0
      have hmem1 : moorePenrose K ⟨y, hy⟩ - p t ∈ LinearMap.ker K.toLinearMap := h0
      have hmem2 : moorePenrose K ⟨y, hy⟩ - p t ∈ (LinearMap.ker K.toLinearMap)ᗮ :=
        Submodule.sub_mem _ hxdperp (hpperp t ht)
      have hmem' : moorePenrose K ⟨y, hy⟩ - p t ∈
          LinearMap.ker K.toLinearMap ⊓ (LinearMap.ker K.toLinearMap)ᗮ := ⟨hmem1, hmem2⟩
      rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot, sub_eq_zero] at hmem'
      obtain ⟨w, -, hw⟩ := (mem_sourceSet_iff _ _ _ _ _).1 (hpsrc t ht)
      exact hcase ⟨w, by rw [hw, ← hmem']⟩
    refine ⟨‖K (moorePenrose K ⟨y, hy⟩ - p (s' / 2))‖ / ((τ - τ₀) / (τ + τ₀)),
      div_pos (hgpos _ hs0) hq0, ?_⟩
    intro δ hδ z hz
    have hδ0 : 0 < δ := hδ.1
    have hδs : (τ - τ₀) / (τ + τ₀) * δ < ‖K (moorePenrose K ⟨y, hy⟩ - p (s' / 2))‖ := by
      have h := hδ.2
      rw [lt_div_iff₀ hq0] at h
      linarith
    have hSne : {t : ℝ | 0 < t ∧ (τ - τ₀) / (τ + τ₀) * δ <
        ‖K (moorePenrose K ⟨y, hy⟩ - p t)‖}.Nonempty := ⟨s' / 2, hs0, hδs⟩
    have hSbdd : BddBelow {t : ℝ | 0 < t ∧ (τ - τ₀) / (τ + τ₀) * δ <
        ‖K (moorePenrose K ⟨y, hy⟩ - p t)‖} := ⟨0, fun t ht => ht.1.le⟩
    set T : ℝ := sInf {t : ℝ | 0 < t ∧ (τ - τ₀) / (τ + τ₀) * δ <
      ‖K (moorePenrose K ⟨y, hy⟩ - p t)‖} with hTdef
    have hTlb : ∀ t ∈ {t : ℝ | 0 < t ∧ (τ - τ₀) / (τ + τ₀) * δ <
        ‖K (moorePenrose K ⟨y, hy⟩ - p
            t)‖}, (τ - τ₀) / (τ + τ₀) * δ / ‖moorePenrose K ⟨y, hy⟩‖ ≤ t := by
      intro t ht
      have h1 : (τ - τ₀) / (τ + τ₀) * δ < ‖K (moorePenrose K ⟨y, hy⟩ - p t)‖ := ht.2
      have h2 : ‖K (moorePenrose K ⟨y, hy⟩ - p t)‖ ≤ t * ‖moorePenrose K ⟨y, hy⟩ - p t‖ :=
        hpcontr t ht.1
      have h3 : ‖moorePenrose K ⟨y, hy⟩ - p t‖ ≤ ‖moorePenrose K ⟨y, hy⟩‖ := hpbdd t ht.1
      rw [div_le_iff₀ hxdnorm]
      nlinarith [ht.1.le, norm_nonneg (moorePenrose K ⟨y, hy⟩ - p t)]
    have hlbpos : (0 : ℝ) < (τ - τ₀) / (τ + τ₀) * δ / ‖moorePenrose K ⟨y, hy⟩‖ :=
      div_pos (mul_pos hq0 hδ0) hxdnorm
    have hT0 : 0 < T := lt_of_lt_of_le hlbpos (le_csInf hSne hTlb)
    have hTs : T ≤ s' / 2 := csInf_le hSbdd ⟨hs0, hδs⟩
    have ht0 : (0 : ℝ) < T / 2 := by linarith
    have htT : T / 2 < T := by linarith
    have hP1 : ‖K (moorePenrose K ⟨y, hy⟩ - p (T / 2))‖ ≤ (τ - τ₀) / (τ + τ₀) * δ := by
      by_contra hcon
      push Not at hcon
      exact absurd (csInf_le hSbdd ⟨ht0, hcon⟩) (not_le.2 htT)
    have hP3 : ‖moorePenrose K ⟨y, hy⟩ - p (T / 2)‖ < η := by
      have h := hpmono (T / 2) (2 * (s' / 2)) ht0 (by linarith)
      linarith
    have hP2 : δ / (T / 2) ≤ 4 * η / ((τ - τ₀) / (τ + τ₀)) := by
      obtain ⟨t'', ht''S, ht''lt⟩ := exists_lt_of_csInf_lt hSne (show T < 2 * T by linarith)
      have h1 : (τ - τ₀) / (τ + τ₀) * δ < ‖K (moorePenrose K ⟨y, hy⟩ - p t'')‖ := ht''S.2
      have h2 : ‖K (moorePenrose K ⟨y, hy⟩ - p t'')‖ ≤ t'' * ‖moorePenrose K ⟨y, hy⟩ - p t''‖ :=
        hpcontr t'' ht''S.1
      have h3 : ‖moorePenrose K ⟨y, hy⟩ - p t''‖ ≤ ‖moorePenrose K ⟨y, hy⟩ - p (2 * T)‖ :=
        hpmono t'' (2 * T) ht''S.1 ht''lt.le
      have h4 : ‖moorePenrose K ⟨y, hy⟩ - p (2 * T)‖ < η := by
        have h := hpmono (2 * T) (2 * (s' / 2)) (by linarith) (by linarith)
        linarith
      have hAA : t'' * ‖moorePenrose K ⟨y, hy⟩ - p t''‖
          ≤ (2 * T) * ‖moorePenrose K ⟨y, hy⟩ - p (2 * T)‖ :=
        mul_le_mul ht''lt.le h3 (norm_nonneg _) (by linarith)
      have hBB : (2 * T) * ‖moorePenrose K ⟨y, hy⟩ - p (2 * T)‖ ≤ (2 * T) * η :=
        mul_le_mul_of_nonneg_left h4.le (by linarith)
      have h5 : (τ - τ₀) / (τ + τ₀) * δ < (2 * T) * η := by linarith
      have hfin : δ ≤ 4 * η / ((τ - τ₀) / (τ + τ₀)) * (T / 2) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hq0]
        nlinarith
      rw [div_le_iff₀ ht0]
      exact hfin
    have htν : (0 : ℝ) < (T / 2) ^ ν := Real.rpow_pos_of_pos ht0 _
    have hρ0 : (0 : ℝ) < ‖moorePenrose K ⟨y, hy⟩‖ / (T / 2) ^ ν := div_pos hxdnorm htν
    have hoo' := (hoo ((τ + τ₀) / 2) hτ'τ₀ (‖moorePenrose K ⟨y, hy⟩‖ / (T / 2) ^ ν) hρ0
      hτ'0).worstCaseError_le
    have hdt0 : (0 : ℝ) < (1 + (τ - τ₀) / (τ + τ₀)) * δ := mul_pos (by linarith) hδ0
    have hbound := hoo' (p (T / 2)) (hpsrc (T / 2) ht0)
      ((1 + (τ - τ₀) / (τ + τ₀)) * δ) hdt0
    have hyK : y - K (p (T / 2)) = K (moorePenrose K ⟨y, hy⟩ - p (T / 2)) := by
      rw [map_sub, hKxd]
    have hzball : z ∈ Metric.closedBall (K (p (T / 2)))
        ((1 + (τ - τ₀) / (τ + τ₀)) * δ) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have he : (z - y) + (y - K (p (T / 2))) = z - K (p (T / 2)) := by abel
      have h1 : ‖z - K (p (T / 2))‖ ≤ ‖z - y‖ + ‖y - K (p (T / 2))‖ := by
        calc ‖z - K (p (T / 2))‖ = ‖(z - y) + (y - K (p (T / 2)))‖ := by rw [he]
          _ ≤ _ := norm_add_le _ _
      rw [hyK] at h1
      have h2 : ‖z - y‖ ≤ δ := by rwa [norm_sub_rev]
      have h3 : (1 + (τ - τ₀) / (τ + τ₀)) * δ = δ + (τ - τ₀) / (τ + τ₀) * δ := by ring
      rw [h3]
      linarith [hP1]
    have hstep :
          ‖R ((a.scale ((τ + τ₀) / 2) hτ'0).param ⟨(1 + (τ - τ₀) / (τ + τ₀)) * δ, hdt0⟩ z) z
            - moorePenrose K ⟨K (p (T / 2)), Submodule.mem_sup_left ⟨p (T / 2), rfl⟩⟩‖ₑ
        ≤ worstCaseError K (fun α w' => R α w') (a.scale ((τ + τ₀) / 2) hτ'0)
            (K (p (T / 2))) (Submodule.mem_sup_left ⟨p (T / 2), rfl⟩)
            ((1 + (τ - τ₀) / (τ + τ₀)) * δ) hdt0 := by
      have h := le_iSup₂ (α := ℝ≥0∞)
        (f := fun w' (_ : w' ∈ Metric.closedBall (K (p (T / 2)))
            ((1 + (τ - τ₀) / (τ + τ₀)) * δ)) =>
            ‖(R ((a.scale ((τ + τ₀) / 2) hτ'0).param ⟨(1 + (τ - τ₀) / (τ + τ₀)) * δ, hdt0⟩ w')) w'
              - moorePenrose K ⟨K (p (T / 2)), Submodule.mem_sup_left ⟨p (T / 2), rfl⟩⟩‖ₑ) z hzball
      simpa [worstCaseError] using h
    have hρpowpos : (0 : ℝ) < (‖moorePenrose K ⟨y, hy⟩‖ / (T / 2) ^ ν) ^ (1 / (ν + 1)) :=
      Real.rpow_pos_of_pos hρ0 _
    have hnn : (0 : ℝ) ≤ c * ((1 + (τ - τ₀) / (τ + τ₀)) * δ) ^ (ν / (ν + 1)) *
        (‖moorePenrose K ⟨y, hy⟩‖ / (T / 2) ^ ν) ^ (1 / (ν + 1)) :=
      mul_nonneg (mul_nonneg hc0.le (Real.rpow_nonneg hdt0.le _)) hρpowpos.le
    have hreal :=
      (ENNReal.ofReal_le_ofReal_iff hnn).1 ((ofReal_norm _).trans_le (hstep.trans hbound))
    rw [hmpK (p (T / 2)) (hpperp (T / 2) ht0)] at hreal
    have hpareq : (τ + τ₀) / 2 * ((1 + (τ - τ₀) / (τ + τ₀)) * δ) = τ * δ := by
      field_simp
      ring
    have hparval : (a.scale ((τ + τ₀) / 2) hτ'0) ⟨(1 + (τ - τ₀) / (τ + τ₀)) * δ, hdt0⟩ z
        = (a.scale τ hτ0) ⟨δ, hδ0⟩ z := by
      simp only [ParameterChoice.scale_apply]
      exact congrArg (fun d : Set.Ioi (0 : ℝ) => a d z) (Subtype.ext hpareq)
    rw [(a.scale ((τ + τ₀) / 2) hτ'0).param_congr hparval] at hreal
    have hfinal : ‖R ((a.scale τ hτ0).param ⟨δ, hδ0⟩ z) z - moorePenrose K ⟨y, hy⟩‖
        ≤ c * ((1 + (τ - τ₀) / (τ + τ₀)) * δ) ^ (ν / (ν + 1)) *
            (‖moorePenrose K ⟨y, hy⟩‖ / (T / 2) ^ ν) ^ (1 / (ν + 1))
          + ‖moorePenrose K ⟨y, hy⟩ - p (T / 2)‖ := by
      have he : R ((a.scale τ hτ0).param ⟨δ, hδ0⟩ z) z - moorePenrose K ⟨y, hy⟩
          = (R ((a.scale τ hτ0).param ⟨δ, hδ0⟩ z) z - p (T / 2))
            - (moorePenrose K ⟨y, hy⟩ - p (T / 2)) := by abel
      rw [he]
      have hnorm := norm_sub_le (R ((a.scale τ hτ0).param ⟨δ, hδ0⟩ z) z - p (T / 2))
        (moorePenrose K ⟨y, hy⟩ - p (T / 2))
      linarith
    have htθ : (0 : ℝ) < (T / 2) ^ (ν / (ν + 1)) := Real.rpow_pos_of_pos ht0 _
    have htθne : ((T / 2) ^ (ν / (ν + 1)) : ℝ) ≠ 0 := ne_of_gt htθ
    have hρpow : (‖moorePenrose K ⟨y, hy⟩‖ / (T / 2) ^ ν) ^ (1 / (ν + 1))
        = ‖moorePenrose K ⟨y, hy⟩‖ ^ (1 / (ν + 1)) / (T / 2) ^ (ν / (ν + 1)) := by
      rw [Real.div_rpow (norm_nonneg _) htν.le, ← Real.rpow_mul ht0.le,
        show ν * (1 / (ν + 1)) = ν / (ν + 1) by field_simp]
    have hdtpow : ((1 + (τ - τ₀) / (τ + τ₀)) * δ) ^ (ν / (ν + 1))
        ≤ 2 * δ ^ (ν / (ν + 1)) := by
      rw [Real.mul_rpow (by linarith) hδ0.le]
      have h1 : (1 + (τ - τ₀) / (τ + τ₀)) ^ (ν / (ν + 1)) ≤ (2 : ℝ) ^ (ν / (ν + 1)) :=
        Real.rpow_le_rpow (by linarith) (by linarith) hθ.le
      have h2 : (2 : ℝ) ^ (ν / (ν + 1)) ≤ 2 := by
        calc (2 : ℝ) ^ (ν / (ν + 1)) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1
          _ = 2 := Real.rpow_one 2
      have h3 : (0 : ℝ) ≤ δ ^ (ν / (ν + 1)) := Real.rpow_nonneg hδ0.le _
      exact mul_le_mul_of_nonneg_right (le_trans h1 h2) h3
    have hnum : c * ((1 + (τ - τ₀) / (τ + τ₀)) * δ) ^ (ν / (ν + 1)) *
          (‖moorePenrose K ⟨y, hy⟩‖ / (T / 2) ^ ν) ^ (1 / (ν + 1))
        ≤ 2 * (c * ‖moorePenrose K ⟨y, hy⟩‖ ^ (1 / (ν + 1))) * (δ / (T / 2)) ^ (ν / (ν + 1)) := by
      rw [hρpow, Real.div_rpow hδ0.le ht0.le]
      calc c * ((1 + (τ - τ₀) / (τ + τ₀)) * δ) ^ (ν / (ν + 1)) *
              (‖moorePenrose K ⟨y, hy⟩‖ ^ (1 / (ν + 1)) / (T / 2) ^ (ν / (ν + 1)))
          = (c * ‖moorePenrose K ⟨y, hy⟩‖ ^ (1 / (ν + 1)) / (T / 2) ^ (ν / (ν + 1))) *
              ((1 + (τ - τ₀) / (τ + τ₀)) * δ) ^ (ν / (ν + 1)) := by ring
        _ ≤ (c * ‖moorePenrose K ⟨y, hy⟩‖ ^ (1 / (ν + 1)) / (T / 2) ^ (ν / (ν + 1))) *
              (2 * δ ^ (ν / (ν + 1))) :=
            mul_le_mul_of_nonneg_left hdtpow
              (div_nonneg (mul_nonneg hc0.le hxn.le) htθ.le)
        _ = 2 * (c * ‖moorePenrose K ⟨y, hy⟩‖ ^ (1 / (ν + 1))) *
              (δ ^ (ν / (ν + 1)) / (T / 2) ^ (ν / (ν + 1))) := by ring
    have hlast : (δ / (T / 2)) ^ (ν / (ν + 1))
        ≤ (4 * η / ((τ - τ₀) / (τ + τ₀))) ^ (ν / (ν + 1)) :=
      Real.rpow_le_rpow (div_nonneg hδ0.le ht0.le) hP2 hθ.le
    have hηpow : 2 * (c * ‖moorePenrose K ⟨y, hy⟩‖ ^ (1 / (ν + 1))) *
        (4 * η / ((τ - τ₀) / (τ + τ₀))) ^ (ν / (ν + 1)) ≤ ε / 4 := by
      have h1 : (4 * η / ((τ - τ₀) / (τ + τ₀))) ^ (ν / (ν + 1))
          ≤ ((ε / (8 * (c * ‖moorePenrose K ⟨y, hy⟩‖ ^ (1 / (ν + 1))))) ^ ((ν + 1) / ν))
              ^ (ν / (ν + 1)) :=
        Real.rpow_le_rpow (div_nonneg (by linarith [hη0]) hq0.le) hηq hθ.le
      have h2 : ((ε / (8 * (c * ‖moorePenrose K ⟨y, hy⟩‖ ^ (1 / (ν + 1))))) ^ ((ν + 1) / ν))
            ^ (ν / (ν + 1)) = ε / (8 * (c * ‖moorePenrose K ⟨y, hy⟩‖ ^ (1 / (ν + 1)))) := by
        rw [← Real.rpow_mul (div_pos hε (by linarith)).le,
          show (ν + 1) / ν * (ν / (ν + 1)) = 1 by field_simp]
        exact Real.rpow_one _
      rw [h2] at h1
      have h3 : 2 * (c * ‖moorePenrose K ⟨y, hy⟩‖ ^ (1 / (ν + 1))) *
          (ε / (8 * (c * ‖moorePenrose K ⟨y, hy⟩‖ ^ (1 / (ν + 1))))) = ε / 4 := by
        field_simp
        ring
      calc 2 * (c * ‖moorePenrose K ⟨y, hy⟩‖ ^ (1 / (ν + 1))) *
              (4 * η / ((τ - τ₀) / (τ + τ₀))) ^ (ν / (ν + 1))
          ≤ 2 * (c * ‖moorePenrose K ⟨y, hy⟩‖ ^ (1 / (ν + 1))) *
              (ε / (8 * (c * ‖moorePenrose K ⟨y, hy⟩‖ ^ (1 / (ν + 1))))) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = ε / 4 := h3
    have hbig : c * ((1 + (τ - τ₀) / (τ + τ₀)) * δ) ^ (ν / (ν + 1)) *
        (‖moorePenrose K ⟨y, hy⟩‖ / (T / 2) ^ ν) ^ (1 / (ν + 1)) ≤ ε / 4 := by
      calc _ ≤ 2 * (c * ‖moorePenrose K ⟨y, hy⟩‖ ^ (1 / (ν + 1))) *
                (δ / (T / 2)) ^ (ν / (ν + 1)) := hnum
        _ ≤ 2 * (c * ‖moorePenrose K ⟨y, hy⟩‖ ^ (1 / (ν + 1))) *
                (4 * η / ((τ - τ₀) / (τ + τ₀))) ^ (ν / (ν + 1)) :=
            mul_le_mul_of_nonneg_left hlast (by linarith)
        _ ≤ ε / 4 := hηpow
    linarith

end AutoIp

end

end _thm_order_optimal_implies_convergence
