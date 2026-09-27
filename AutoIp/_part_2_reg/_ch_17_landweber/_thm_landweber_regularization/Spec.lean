/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_standard_filters
public import AutoIp._part_2_reg._ch_17_landweber._def_landweber
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_hom
import AutoIp._part_2_reg._ch_15_spectral_regularization._thm_spectral_is_regularization
import AutoIp._part_2_reg._ch_17_landweber._lem_landweber_closed_form
import AutoIp.Auxiliary.BoundedOnIcc
import Mathlib.Topology.Order.AtTopBotIxx
import AutoIp._part_2_reg._ch_17_landweber._thm_landweber_regularization.Helpers

section _thm_landweber_regularization

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Landweber is a spectral regularization: for `ω ∈ (0,κ⁻¹]`, `xₘ = φₘ(K*K)K* y` with `φₘ`
the Landweber filter at `α = 1/m`, and `Rₘ y → K† y` as `m → ∞` for every `y ∈ Dom(K†)`.

The parameter `α = 1/m` enters as a positive real `α` (or a sequence `α`) with the equation
`α = 1/m` as a hypothesis, for `m > 0`; the value `α 0` is left free.

The step size `ω ∈ (0, κ⁻¹]` is stated as `0 < ω` and `ωκ ≤ 1`, which is the same for `K ≠ 0` and,
unlike the interval, makes no use of `0⁻¹`. It holds for every `K`, `K = 0` included. -/
public
theorem landweber_eq_spectralReg_and_tendsto_moorePenrose (hs : IsSingularSystem K σ v u) {ω : ℝ}
    (hω : 0 < ω ∧ ω * ‖K‖ ^ 2 ≤ 1) :
    (∀ (y : F) (m : ℕ), 0 < m → ∀ α : Set.Ioi (0 : ℝ), (α : ℝ) = 1 / m →
        landweber K ω y m = spectralReg hs (landweberFilter
            ω) (landweberFilter_exists_bound_on_spectrum hs hω) α y) ∧
      ∀ y, ∀ hy : y ∈ mpDomain K, ∀ α : ℕ → Set.Ioi (0 : ℝ),
        (∀ m : ℕ, 0 < m → (α m : ℝ) = 1 / m) →
        Tendsto (fun m : ℕ => spectralReg hs (landweberFilter ω)
            (landweberFilter_exists_bound_on_spectrum hs hω) (α m) y) atTop
          (𝓝 (moorePenrose K ⟨y, hy⟩)) := by
  refine ⟨fun y m hm α hα => ?_, fun y hy α hα => ?_⟩
  · have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hbL : ∃ c, ∀ i, |landweberFilter ω α (σ i ^ 2)| ≤ c :=
      landweberFilter_exists_bound_on_spectrum hs hω α
    have hbgeom : ∃ c, ∀ i,
        |(fun t : ℝ => ∑ n ∈ Finset.range m, (1 - ω * t) ^ n) (σ i ^ 2)| ≤ c :=
      hs.exists_bound_sq (exists_bound_on_Icc_of_continuous (‖K‖ ^ 2)
        (φ := fun t : ℝ => ∑ n ∈ Finset.range m, (1 - ω * t) ^ n) (by fun_prop))
    rw [landweber_eq_sum,
      spectralReg_eq hs (landweberFilter ω)
        (landweberFilter_exists_bound_on_spectrum hs hω) α,
      ContinuousLinearMap.comp_apply]
    have hcongr : hs.funCalc (landweberFilter ω α) hbL
        = hs.funCalc (ω • (fun t : ℝ => ∑ n ∈ Finset.range m, (1 - ω * t) ^ n))
            (exists_forall_abs_smul_sq_le ω hbgeom) := by
      refine hs.funCalc_congr _ _ (fun t ht => ?_)
      rw [landweberFilter_eq_geom K hω hm hα ht]
      rfl
    rw [hcongr, hs.funCalc_smul' ω hbgeom, hs.funCalc_geom_sum ω m hbgeom]
    simp only [smul_apply, FunLike.coe_sum,
      Finset.sum_apply]
  · have hreg := isRegularization_spectralReg hs (landweberFilter_isRegularizingFilter K hω) y hy
    have hcoe : Tendsto (fun m : ℕ => (α m : ℝ)) atTop (𝓝[>] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
        (Eventually.of_forall fun m => (α m).2)
      refine Tendsto.congr' ?_ tendsto_one_div_atTop_nhds_zero_nat
      filter_upwards [eventually_gt_atTop 0] with m hm using (hα m hm).symm
    have hat : Tendsto α atTop atBot := by
      have hcomap : comap ((↑) : Set.Ioi (0 : ℝ) → ℝ) (𝓝[>] (0 : ℝ)) = atBot :=
        comap_coe_Ioi_nhdsGT (0 : ℝ)
      rw [← hcomap]
      exact tendsto_comap_iff.2 hcoe
    exact hreg.comp hat

/-- `xₘ = φₘ(K*K)K* y` for `ω ∈ (0,κ⁻¹]`, with `φₘ` the Landweber filter at `α = 1/m`.

The parameter enters as a positive real `α` with `α = 1/m` as a hypothesis, for `m > 0`.

The step size `ω ∈ (0, κ⁻¹]` is stated as `0 < ω` and `ωκ ≤ 1`, which is the same for `K ≠ 0` and,
unlike the interval, makes no use of `0⁻¹`. It holds for every `K`, `K = 0` included. -/
public theorem landweber_eq_spectralReg (hs : IsSingularSystem K σ v u) {ω : ℝ}
    (hω : 0 < ω ∧ ω * ‖K‖ ^ 2 ≤ 1) (y : F) {m : ℕ} (hm : 0 < m)
    {α : Set.Ioi (0 : ℝ)} (hα : (α : ℝ) = 1 / m) :
    landweber K ω y m = spectralReg hs (landweberFilter
        ω) (landweberFilter_exists_bound_on_spectrum hs hω) α y :=
  (landweber_eq_spectralReg_and_tendsto_moorePenrose hs hω).1 y m hm α hα

/-- `Rₘ y → K† y` as `m → ∞` for every `y ∈ Dom(K†)`, for `ω ∈ (0,κ⁻¹]`.

`Rₘ` is taken at the parameters `α m`, which equal `1/m` for `m > 0`; `α 0` is left free.

The step size `ω ∈ (0, κ⁻¹]` is stated as `0 < ω` and `ωκ ≤ 1`, which is the same for `K ≠ 0` and,
unlike the interval, makes no use of `0⁻¹`. It holds for every `K`, `K = 0` included. -/
public theorem tendsto_landweber_moorePenrose (hs : IsSingularSystem K σ v u) {ω : ℝ}
    (hω : 0 < ω ∧ ω * ‖K‖ ^ 2 ≤ 1) {y : F} (hy : y ∈ mpDomain K)
    (α : ℕ → Set.Ioi (0 : ℝ)) (hα : ∀ m : ℕ, 0 < m → (α m : ℝ) = 1 / m) :
    Tendsto (fun m : ℕ => spectralReg hs (landweberFilter ω)
        (landweberFilter_exists_bound_on_spectrum hs hω) (α m) y) atTop
      (𝓝 (moorePenrose K ⟨y, hy⟩)) :=
  (landweber_eq_spectralReg_and_tendsto_moorePenrose hs hω).2 y hy α hα

end AutoIp

end _thm_landweber_regularization
