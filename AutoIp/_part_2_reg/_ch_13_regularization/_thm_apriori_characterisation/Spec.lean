/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_13_regularization._def_parameter_choice
public import AutoIp._part_2_reg._ch_13_regularization._def_regularization
import AutoIp._part_2_reg._ch_11_moore_penrose._thm_mp_inverse
import AutoIp._part_2_reg._ch_13_regularization._lem_error_decomposition
import Mathlib.Topology.Order.AtTopBotIxx

section _thm_apriori_characterisation

namespace AutoIp

open Filter Topology
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- (i): for a regularization `{R_α}` of `T†` and an a priori rule `α` with `α(δ) → 0` and
`δ ‖R_{α(δ)}‖ → 0` as `δ → 0`, `(R_α, α)` is a convergent regularization method. The two
limits are stated at every datum `y`, on which an a priori rule does not depend. -/
public theorem isRegularizationMethod_of_apriori {T : E →L[𝕜] F} {R : Set.Ioi (0 : ℝ) → F →L[𝕜] E}
    (hR : IsRegularization T R) {a : ParameterChoice F} (ha : a.IsAPriori)
    (h0 : ∀ y : F, Tendsto (fun δ : Set.Ioi (0 : ℝ) => a δ y) atBot (𝓝 0))
    (hdata : ∀ y : F,
      Tendsto (fun δ : Set.Ioi (0 : ℝ) => (δ : ℝ) * ‖R (a.param δ y)‖) atBot (𝓝 0)) :
    IsRegularizationMethod T (fun α w => R α w) a := by
  intro y hy ε hε
  have hmap : Tendsto (fun δ : Set.Ioi (0 : ℝ) => a δ y) atBot (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (h0 y)
      (Eventually.of_forall fun δ => a.pos δ y)
  have happ : Tendsto (fun δ : Set.Ioi (0 : ℝ) =>
      ‖R (a.param δ y) y - moorePenrose T ⟨y, hy⟩‖) atBot (𝓝 0) := by
    have hparam : Tendsto (fun δ : Set.Ioi (0 : ℝ) => a.param δ y) atBot atBot := by
      have hcomap : comap ((↑) : Set.Ioi (0 : ℝ) → ℝ) (𝓝[>] (0 : ℝ)) = atBot :=
        comap_coe_Ioi_nhdsGT (0 : ℝ)
      nth_rewrite 2 [← hcomap]
      exact tendsto_comap_iff.2 hmap
    have hc : Tendsto (fun δ : Set.Ioi (0 : ℝ) => R (a.param δ y) y) atBot
        (𝓝 (moorePenrose T ⟨y, hy⟩)) := (hR y hy).comp hparam
    have := (hc.sub (tendsto_const_nhds (x := moorePenrose T ⟨y, hy⟩))).norm
    simpa using this
  have hsum : Tendsto (fun δ : Set.Ioi (0 : ℝ) =>
      (δ : ℝ) * ‖R (a.param δ y)‖ + ‖R (a.param δ y) y - moorePenrose T ⟨y, hy⟩‖) atBot (𝓝 0) := by
    simpa using (hdata y).add happ
  have hev : ∀ᶠ δ : Set.Ioi (0 : ℝ) in atBot,
      (δ : ℝ) * ‖R (a.param δ y)‖ + ‖R (a.param δ y) y - moorePenrose T ⟨y, hy⟩‖ < ε :=
    hsum.eventually (gt_mem_nhds hε)
  obtain ⟨δ₀, hb⟩ := eventually_atBot.1 hev
  refine ⟨(δ₀ : ℝ), δ₀.2, ?_⟩
  intro δ hδ z hzy
  have hlt := hb ⟨δ, hδ.1⟩ (le_of_lt hδ.2)
  rw [a.param_congr (ha ⟨δ, hδ.1⟩ z y)]
  exact lt_of_le_of_lt (norm_sub_moorePenrose_le R hy hzy) hlt

/-- (ii), second assertion: if `(R_α, α)` is a convergent regularization method, then
`‖R_{α(δ,y)} y − T†y‖ → 0` as `δ → 0` for every `y ∈ Dom(T†)`. The rule need not be a priori
and `{R_α}` need not be a regularization of `T†`. -/
public theorem tendsto_norm_sub_moorePenrose_of_isRegularizationMethod {T : E →L[𝕜] F}
    {R : Set.Ioi (0 : ℝ) → F →L[𝕜] E} {a : ParameterChoice F}
    (hmethod : IsRegularizationMethod T (fun α w => R α w) a) :
    ∀ y, ∀ hy : y ∈ mpDomain T,
      Tendsto (fun δ : Set.Ioi (0 : ℝ) => ‖R (a.param δ y) y - moorePenrose T ⟨y, hy⟩‖)
        atBot (𝓝 0) := by
  intro y hy
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ₀, hδ₀, hb⟩ := hmethod y hy ε hε
  rw [eventually_atBot]
  refine ⟨⟨δ₀ / 2, Set.mem_Ioi.2 (half_pos hδ₀)⟩, ?_⟩
  intro δ hδle
  have hδlt : (δ : ℝ) < δ₀ := lt_of_le_of_lt hδle (by simpa using half_lt_self hδ₀)
  have := hb (δ : ℝ) ⟨δ.2, hδlt⟩ y (by simpa using (le_of_lt δ.2))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  exact this

/-- (ii): for an a priori rule `α` such that `(R_α, α)` is a convergent regularization method,
`δ ‖R_{α(δ)}‖ → 0` and `‖R_{α(δ)} y − T†y‖ → 0` as `δ → 0` for every `y ∈ Dom(T†)`. The
family `{R_α}` need not be a regularization of `T†`, and the first limit is stated at every
datum `y`, on which the rule does not depend. -/
public theorem tendsto_of_isAPriori_of_isRegularizationMethod {T : E →L[𝕜] F}
    {R : Set.Ioi (0 : ℝ) → F →L[𝕜] E} {a : ParameterChoice F} (ha : a.IsAPriori)
    (hmethod : IsRegularizationMethod T (fun α w => R α w) a) :
    (∀ y : F,
        Tendsto (fun δ : Set.Ioi (0 : ℝ) => (δ : ℝ) * ‖R (a.param δ y)‖) atBot (𝓝 0)) ∧
      ∀ y, ∀ hy : y ∈ mpDomain T,
        Tendsto (fun δ : Set.Ioi (0 : ℝ) => ‖R (a.param δ y) y - moorePenrose T ⟨y, hy⟩‖)
          atBot (𝓝 0) := by
  have hzero : (0 : F) ∈ mpDomain T := Submodule.zero_mem _
  have hmp0 : moorePenrose T ⟨(0 : F), hzero⟩ = 0 := moorePenrose_zero
  constructor
  · intro y
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ₀, hδ₀, hb⟩ := hmethod 0 hzero (ε / 2) (by linarith)
    rw [eventually_atBot]
    refine ⟨⟨δ₀ / 2, Set.mem_Ioi.2 (half_pos hδ₀)⟩, ?_⟩
    intro δ hδle
    have hδpos : (0 : ℝ) < (δ : ℝ) := δ.2
    have hδlt : (δ : ℝ) < δ₀ := lt_of_le_of_lt hδle (by simpa using half_lt_self hδ₀)
    have key : ∀ z : F, ‖z‖ ≤ (δ : ℝ) → ‖R (a.param δ y) z‖ ≤ ε / 2 := by
      intro z hzn
      have h1 := hb (δ : ℝ) ⟨hδpos, hδlt⟩ z (by simpa using hzn)
      rw [a.param_congr (ha _ z y), hmp0] at h1
      simpa using h1.le
    have hop : ‖R (a.param δ y)‖ ≤ (ε / 2) / δ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
      intro w
      rcases eq_or_ne w 0 with rfl | hw
      · simp
      · have hwn : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
        have htpos : (0 : ℝ) < δ / ‖w‖ := by positivity
        have hznorm : ‖((δ / ‖w‖ : ℝ) : 𝕜) • w‖ = δ := by
          rw [norm_smul, RCLike.norm_ofReal, abs_of_pos htpos]
          field_simp
        have hk := key (((δ / ‖w‖ : ℝ) : 𝕜) • w) hznorm.le
        rw [map_smul, norm_smul, RCLike.norm_ofReal, abs_of_pos htpos] at hk
        rw [div_mul_eq_mul_div, div_le_iff₀ hwn] at hk
        rw [div_mul_eq_mul_div, le_div_iff₀ hδpos]
        linarith
      
    have hfin : δ * ‖R (a.param δ y)‖ ≤ ε / 2 := by
      have h2 := mul_le_mul_of_nonneg_left hop hδpos.le
      have h3 : δ * ((ε / 2) / δ) = ε / 2 := by field_simp
      linarith
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
    linarith
  · exact tendsto_norm_sub_moorePenrose_of_isRegularizationMethod hmethod

end AutoIp

end _thm_apriori_characterisation
