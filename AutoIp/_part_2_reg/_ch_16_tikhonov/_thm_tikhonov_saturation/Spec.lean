/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_14_order_optimality._def_worst_case_error
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_standard_filters
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import AutoIp._part_1_funcanal._ch_08_svd._cor_sigma_null
import AutoIp._part_2_reg._ch_11_moore_penrose._cor_normal_equation
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_spectral_residual_form
import AutoIp._part_2_reg._ch_16_tikhonov._lem_tikhonov_normal

section _thm_tikhonov_saturation

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Tikhonov saturates at `δ^(2/3)`: let `K` be compact with infinite-dimensional range and
`y ∈ Ran(K)`. If an a priori rule `α` has `α(δ) → 0` and
`sup_{y^δ ∈ B_δ(y)} ‖x^δ_{α(δ)} - x†‖ δ^(-2/3) → 0` as `δ → 0`, then `x† = 0`.

The closing remark of the node, that the qualification of Tikhonov is exactly `2`, is stated with
the qualification of Tikhonov regularization and is not restated here. -/
public theorem tikhonov_saturation (hs : IsSingularSystem K σ v u) (hKc : IsCompactOperator K)
    (hinf : ¬ FiniteDimensional 𝕜 K.toLinearMap.range)
    {y : F} (hy : y ∈ K.toLinearMap.range)
    (a : ParameterChoice F) (ha : a.IsAPriori)
    (h0 : ∀ z : F, Tendsto (fun δ : Set.Ioi (0 : ℝ) => a δ z) atBot (𝓝 0))
    (hsat : Tendsto
      (fun δ : Set.Ioi (0 : ℝ) =>
        worstCaseError K (fun α w => spectralReg hs tikhonovFilter
            (tikhonovFilter_exists_bound_on_spectrum hs) α w) a y
          (Submodule.mem_sup_left hy) (δ : ℝ) δ.2 *
        ENNReal.ofReal ((δ : ℝ) ^ (-(2 : ℝ) / 3))) atBot (𝓝 0)) :
    moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩ = 0 := by
  classical
  by_contra hne
  have hxn : 0 < ‖moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩‖ := norm_pos_iff.mpr hne
  have hκ0 : (0 : ℝ) ≤ ‖K‖ ^ 2 := by positivity
  have hymem : y ∈ mpDomain K := Submodule.mem_sup_left hy
  have hK1 : ∀ (δ : Set.Ioi (0 : ℝ)), ∀ z : F, z ∈ Metric.closedBall y (δ : ℝ) →
      ‖spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum
          hs) ((a).param δ y) z
          - moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩‖ₑ
        ≤ worstCaseError K (fun α w => spectralReg hs tikhonovFilter
            (tikhonovFilter_exists_bound_on_spectrum hs) α w) a y
        (Submodule.mem_sup_left hy) (δ : ℝ) δ.2 := by
    intro δ z hz
    have h := le_worstCaseError K (fun α z => spectralReg hs tikhonovFilter
        (tikhonovFilter_exists_bound_on_spectrum hs) α z) a y
      (Submodule.mem_sup_left hy) δ.2 hz
    rw [a.param_congr (ha δ z y)] at h
    exact h
  have hstep1 : ∀ δ : Set.Ioi (0 : ℝ),
      (a.param δ y : ℝ) * ‖moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩‖
        ≤ (‖K‖ ^ 2 + (a.param δ y : ℝ)) *
          ‖spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) (a.param δ
              y) y
            - moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩‖ := by
    intro δ
    set α := a.param δ y with hαdef
    have hα0 : (0 : ℝ) < (α : ℝ) := α.2
    set A : E →L[𝕜] E := ContinuousLinearMap.adjoint K ∘L K
        + (RCLike.ofReal (α : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E with hAdef
    have hAR : A (spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) α
        y) = ContinuousLinearMap.adjoint K y :=
      (tikhonov_iff_normal hs y _).mp rfl
    have hnormal : (ContinuousLinearMap.adjoint K ∘L K) (moorePenrose K ⟨y,
        Submodule.mem_sup_left hy⟩)
        = ContinuousLinearMap.adjoint K y :=
      isLeastSquares_iff_adjoint_comp_self_apply_eq.mp (moorePenrose_isMinimumNorm
        ⟨_, hymem⟩).isLeastSquares
    have hAx : A (moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩)
        = ContinuousLinearMap.adjoint K y
          + (RCLike.ofReal (α : ℝ) : 𝕜) • moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩ := by
      rw [hAdef]
      simp only [add_apply, smul_apply,
        ContinuousLinearMap.id_apply]
      rw [hnormal]
    have hsubeq : A (spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) α
        y - moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩)
        = -((RCLike.ofReal (α : ℝ) : 𝕜) • moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩) := by
      rw [map_sub, hAR, hAx]; abel
    have hAnorm : ‖A‖ ≤ ‖K‖ ^ 2 + (α : ℝ) := by
      refine le_trans (norm_add_le _ _) ?_
      have h1 : ‖ContinuousLinearMap.adjoint K ∘L K‖ ≤ ‖K‖ ^ 2 := by
        rw [ContinuousLinearMap.norm_adjoint_comp_self, sq]
      have h2 : ‖(RCLike.ofReal (α : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E‖ ≤ (α : ℝ) := by
        rw [norm_smul, RCLike.norm_ofReal, abs_of_pos hα0]
        calc (α : ℝ) * ‖ContinuousLinearMap.id 𝕜 E‖ ≤ (α : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le hα0.le
          _ = (α : ℝ) := mul_one (α : ℝ)
      linarith
    have hkey := A.le_opNorm (spectralReg hs tikhonovFilter
        (tikhonovFilter_exists_bound_on_spectrum hs) α y - moorePenrose K ⟨y,
            Submodule.mem_sup_left hy⟩)
    rw [hsubeq, norm_neg, norm_smul, RCLike.norm_ofReal, abs_of_pos hα0] at hkey
    nlinarith [hkey, hAnorm,
      norm_nonneg (spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) α y
          - moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩), hxn]
  have hsmall : ∀ ε : ℝ, 0 < ε → ∃ i : ι, σ i < ε :=
    fun ε hε => hs.exists_lt_of_not_finiteDimensional_range hKc hinf hε
  have hev1 : ∀ᶠ δ : Set.Ioi (0 : ℝ) in atBot, (a.param δ y : ℝ) < 1 :=
    (h0 y).eventually (gt_mem_nhds one_pos)
  have hev2 : ∀ᶠ δ : Set.Ioi (0 : ℝ) in atBot,
      worstCaseError K (fun α w => spectralReg hs tikhonovFilter
          (tikhonovFilter_exists_bound_on_spectrum hs) α w) a y
        (Submodule.mem_sup_left hy) (δ : ℝ) δ.2 *
        ENNReal.ofReal ((δ : ℝ) ^ (-(2 : ℝ) / 3))
        < ENNReal.ofReal (‖moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩‖ / (‖K‖ ^ 2 + 2)) :=
    hsat.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr (by positivity)))
  have hev3 : ∀ᶠ δ : Set.Ioi (0 : ℝ) in atBot,
      worstCaseError K (fun α w => spectralReg hs tikhonovFilter
          (tikhonovFilter_exists_bound_on_spectrum hs) α w) a y
        (Submodule.mem_sup_left hy) (δ : ℝ) δ.2 *
        ENNReal.ofReal ((δ : ℝ) ^ (-(2 : ℝ) / 3)) < ENNReal.ofReal (1 / 8) :=
    hsat.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr (by norm_num)))
  obtain ⟨δ₀, hsub⟩ := eventually_atBot.1 ((hev1.and hev2).and hev3)
  have hδ₀ : (0 : ℝ) < (δ₀ : ℝ) := δ₀.2
  obtain ⟨i, hi⟩ := hsmall (min 1 (δ₀ : ℝ)) (lt_min one_pos hδ₀)
  have hs0 : 0 < σ i := hs.pos i
  have hs1 : σ i < 1 := lt_of_lt_of_le hi (min_le_left _ _)
  have hsδ : σ i < (δ₀ : ℝ) := lt_of_lt_of_le hi (min_le_right _ _)
  have hδ0 : (0 : ℝ) < σ i ^ 3 := by positivity
  have hδlt : σ i ^ 3 < (δ₀ : ℝ) := by
    have hc : σ i ^ 3 ≤ σ i := by nlinarith [hs0, hs1, mul_pos hs0 hs0]
    linarith
  obtain ⟨⟨hA1, hA2⟩, hA3⟩ := hsub ⟨σ i ^ 3, hδ0⟩ hδlt.le
  set δ : ℝ := σ i ^ 3 with hδdef
  set q : Set.Ioi (0 : ℝ) := a.param ⟨δ, hδ0⟩ y with hqdef
  have hq0 : (0 : ℝ) < (q : ℝ) := q.2
  have hrp : δ ^ (-(2 : ℝ) / 3) = (σ i ^ 2)⁻¹ := by
    rw [hδdef, ← Real.rpow_natCast (σ i) 3, ← Real.rpow_mul hs0.le]
    norm_num
  have hrp0 : (0 : ℝ) < δ ^ (-(2 : ℝ) / 3) := by rw [hrp]; positivity
  have hden : (0 : ℝ) < σ i ^ 2 + (q : ℝ) := by positivity
  -- First step: with `δ = σ_i³`, the parameter `q = α(δ)` satisfies `q < σ_i²`.
  have hby :
      ‖spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) q y
        - moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩‖ₑ
      ≤ worstCaseError K (fun α w => spectralReg hs tikhonovFilter
          (tikhonovFilter_exists_bound_on_spectrum hs) α w) a y
        (Submodule.mem_sup_left hy) δ hδ0 := by
    have h := hK1 ⟨δ, hδ0⟩ y (Metric.mem_closedBall_self hδ0.le)
    rwa [← hqdef] at h
  have hmul : ENNReal.ofReal (‖spectralReg hs tikhonovFilter
      (tikhonovFilter_exists_bound_on_spectrum hs) q y - moorePenrose K ⟨y,
          Submodule.mem_sup_left hy⟩‖
        * δ ^ (-(2 : ℝ) / 3))
      < ENNReal.ofReal (‖moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩‖ / (‖K‖ ^ 2 + 2)) := by
    rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
    exact lt_of_le_of_lt (by gcongr) hA2
  have hreal : ‖spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum
      hs) q y - moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩‖ * δ ^ (-(2 : ℝ) / 3)
      < ‖moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩‖ / (‖K‖ ^ 2 + 2) :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hmul
  have hqlt : (q : ℝ) < σ i ^ 2 := by
    have h1 := hstep1 ⟨δ, hδ0⟩
    rw [← hqdef] at h1
    have hr0 : (0 : ℝ) ≤ ‖spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum
        hs) q y - moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩‖ :=
      norm_nonneg _
    have h2 : (q : ℝ) * ‖moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩‖ * δ ^ (-(2 : ℝ) / 3)
        ≤ (‖K‖ ^ 2 + (q : ℝ)) *
          (‖spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) q y -
              moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩‖ * δ ^ (-(2 : ℝ) / 3)) := by
      nlinarith [h1, hrp0]
    have h3 : (‖K‖ ^ 2 + (q : ℝ)) *
        (‖spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) q y -
            moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩‖ * δ ^ (-(2 : ℝ) / 3))
        < (‖K‖ ^ 2 + (q : ℝ)) * (‖moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩‖ / (‖K‖ ^ 2 + 2)) :=
      mul_lt_mul_of_pos_left hreal (by linarith)
    have hden2 : (0 : ℝ) < ‖K‖ ^ 2 + 2 := by positivity
    have h4 : (‖K‖ ^ 2 + (q : ℝ)) * (‖moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩‖ / (‖K‖ ^ 2 +
        2)) < ‖moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩‖ := by
      rw [mul_div_assoc', div_lt_iff₀ hden2]
      nlinarith [hxn, hA1, hq0]
    have h5 : (q : ℝ) * ‖moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩‖ * δ ^ (-(2 : ℝ) /
        3) < ‖moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩‖ := by
      linarith
    rw [hrp] at h5
    have hσ2 : (0 : ℝ) < σ i ^ 2 := by positivity
    have h5' : (q : ℝ) * ‖moorePenrose K ⟨y, Submodule.mem_sup_left
        hy⟩‖ / σ i ^ 2 < ‖moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩‖ := by
      rw [div_eq_mul_inv]; exact h5
    rw [div_lt_iff₀ hσ2] at h5'
    nlinarith [h5', hxn]
  -- Second step: the perturbed datum `y + δ u_i` forces `q ≥ 3σ_i²`.
  set z : F := y + (RCLike.ofReal δ : 𝕜) • u i with hzdef
  have hzy : z - y = (RCLike.ofReal δ : 𝕜) • u i := by rw [hzdef]; abel
  have hzmem : z ∈ Metric.closedBall y δ := by
    rw [Metric.mem_closedBall, dist_eq_norm, hzy, norm_smul, RCLike.norm_ofReal,
      hs.orthonormal_right.1 i, mul_one, abs_of_pos hδ0]
  have hRu : spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) q (u i)
      = (RCLike.ofReal (tikhonovFilter q (σ i ^ 2) * σ i) : 𝕜) • v i := by
    obtain ⟨hsum, -⟩ :=
      hasSum_spectralReg_and_norm_sq (α := q) hs (tikhonovFilter_exists_bound_on_spectrum hs) (u i)
    have hzero : ∀ j : ι, j ≠ i →
        ((RCLike.ofReal (tikhonovFilter q (σ j ^ 2) * σ j) : 𝕜) * inner 𝕜 (u j) (u i)) • v j
          = 0 := by
      intro j hj
      have h : (inner 𝕜 (u j) (u i) : 𝕜) = 0 := by
        simpa [hj] using (orthonormal_iff_ite.mp hs.orthonormal_right j i)
      rw [h, mul_zero, zero_smul]
    have h3 := hsum.unique (hasSum_single i hzero)
    rw [h3]
    have h1 : (inner 𝕜 (u i) (u i) : 𝕜) = 1 := by
      simpa using (orthonormal_iff_ite.mp hs.orthonormal_right i i)
    rw [h1, mul_one]
  have hnormRu : ‖spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) q (u
      i)‖ = σ i / (σ i ^ 2 + (q : ℝ)) := by
    have hnn : (0 : ℝ) ≤ (σ i ^ 2 + (q : ℝ))⁻¹ * σ i :=
      mul_nonneg (inv_nonneg.mpr hden.le) hs0.le
    rw [hRu, norm_smul, RCLike.norm_ofReal, hs.orthonormal_left.1 i, mul_one, tikhonovFilter,
      abs_of_nonneg hnn, inv_mul_eq_div]
  have hRdiff : ‖spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum
      hs) q z - spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) q y‖
      = δ * (σ i / (σ i ^ 2 + (q : ℝ))) := by
    have he : spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum
        hs) q z - spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) q y
        = (RCLike.ofReal δ :
            𝕜) •
              spectralReg hs tikhonovFilter
                (tikhonovFilter_exists_bound_on_spectrum hs) q (u i) := by
      rw [← ContinuousLinearMap.map_smul, ← hzy, map_sub]
    rw [he, norm_smul, RCLike.norm_ofReal, abs_of_pos hδ0, hnormRu]
  have hb1 := hK1 ⟨δ, hδ0⟩ z hzmem
  have hb2 := hK1 ⟨δ, hδ0⟩ y (Metric.mem_closedBall_self hδ0.le)
  rw [← hqdef] at hb1 hb2
  have htri : ‖spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum
      hs) q z - spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) q y‖
      ≤ ‖spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum
          hs) q z - moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩‖
        + ‖spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum
            hs) q y - moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩‖ := by
    have heq : spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum
        hs) q z - spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) q y
        = (spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) q z -
            moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩)
          - (spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) q y -
              moorePenrose K ⟨y, Submodule.mem_sup_left hy⟩) := by abel
    rw [heq]
    exact norm_sub_le _ _
  have hfac : (0 : ℝ) ≤ δ * (σ i / (σ i ^ 2 + (q : ℝ))) :=
    mul_nonneg hδ0.le (div_nonneg hs0.le hden.le)
  have hEnn : ENNReal.ofReal (δ * (σ i / (σ i ^ 2 + (q : ℝ))))
      ≤ worstCaseError K (fun α w => spectralReg hs tikhonovFilter
          (tikhonovFilter_exists_bound_on_spectrum hs) α w) a y
        (Submodule.mem_sup_left hy) δ hδ0
        + worstCaseError K (fun α w => spectralReg hs tikhonovFilter
            (tikhonovFilter_exists_bound_on_spectrum hs) α w) a y
        (Submodule.mem_sup_left hy) δ hδ0 := by
    rw [← hRdiff]
    refine le_trans (ENNReal.ofReal_le_ofReal htri) ?_
    rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ofReal_norm, ofReal_norm]
    exact add_le_add hb1 hb2
  have hEnn2 : ENNReal.ofReal (δ * (σ i / (σ i ^ 2 + (q : ℝ))) * δ ^ (-(2 : ℝ) / 3))
      ≤ ENNReal.ofReal (1 / 4) := by
    rw [ENNReal.ofReal_mul hfac]
    calc ENNReal.ofReal (δ * (σ i / (σ i ^ 2 + (q : ℝ)))) * ENNReal.ofReal (δ ^ (-(2 : ℝ) / 3))
        ≤ (worstCaseError K (fun α w => spectralReg hs tikhonovFilter
            (tikhonovFilter_exists_bound_on_spectrum hs) α w) a y
        (Submodule.mem_sup_left hy) δ hδ0
            + worstCaseError K (fun α w => spectralReg hs tikhonovFilter
                (tikhonovFilter_exists_bound_on_spectrum hs) α w) a y
        (Submodule.mem_sup_left hy) δ hδ0)
          * ENNReal.ofReal (δ ^ (-(2 : ℝ) / 3)) := by gcongr
      _ = worstCaseError K (fun α w => spectralReg hs tikhonovFilter
          (tikhonovFilter_exists_bound_on_spectrum hs) α w) a y
        (Submodule.mem_sup_left hy) δ hδ0
            * ENNReal.ofReal (δ ^ (-(2 : ℝ) / 3))
          + worstCaseError K (fun α w => spectralReg hs tikhonovFilter
              (tikhonovFilter_exists_bound_on_spectrum hs) α w) a y
        (Submodule.mem_sup_left hy) δ hδ0
            * ENNReal.ofReal (δ ^ (-(2 : ℝ) / 3)) := by rw [add_mul]
      _ ≤ ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 8) := add_le_add hA3.le hA3.le
      _ = ENNReal.ofReal (1 / 4) := by
          rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
  have hval : δ * (σ i / (σ i ^ 2 + (q : ℝ))) * δ ^ (-(2 : ℝ) / 3) = σ i ^ 2 / (σ i ^ 2 + (q :
      ℝ)) := by
    rw [hrp, hδdef]
    field_simp
  rw [hval] at hEnn2
  have hfin : σ i ^ 2 / (σ i ^ 2 + (q : ℝ)) ≤ 1 / 4 :=
    (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hEnn2
  rw [div_le_iff₀ hden] at hfin
  nlinarith [hfin, hqlt, hs0, mul_pos hs0 hs0]

end AutoIp

end _thm_tikhonov_saturation
