/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_16_tikhonov._def_value_functions
public import Mathlib.Analysis.Calculus.Deriv.Basic
import AutoIp._part_2_reg._ch_16_tikhonov._thm_tikhonov_variational
import Mathlib.Analysis.Calculus.Deriv.Slope

section _lem_value_derivative_bounds

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Bounds on the one-sided derivatives, the first chain: for `α > 0` at which the one-sided
derivatives `D⁺j(α)` and `D⁻j(α)` exist, `D⁺j(α) ≤ g(α) ≤ D⁻j(α)`.

`j`, `f` and `g` are functions on `ℝ` that agree with the value functions on `(0,∞)`; their
values elsewhere play no role. It holds for every `K`, `K = 0` included. -/
public theorem tikhonovValue_deriv_bounds (hs : IsSingularSystem K σ v u) (z : F)
    {j f g : ℝ → ℝ}
    (hj : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), j b = tikhonovValue hs z ⟨b, hb⟩)
    (hf : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), f b = tikhonovResidualValue hs z ⟨b, hb⟩)
    (hg : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), g b = tikhonovNormValue hs z ⟨b, hb⟩)
    {α : ℝ} (hα : α ∈ Set.Ioi (0 : ℝ)) {dr dl : ℝ}
    (hdr : HasDerivWithinAt j dr (Set.Ioi α) α)
    (hdl : HasDerivWithinAt j dl (Set.Iio α) α) :
    dr ≤ g α ∧ g α ≤ dl := by
  have hα0 : (0 : ℝ) < α := hα
  have hmin : ∀ (a : ℝ), a ∈ Set.Ioi (0 : ℝ) → ∀ (b : ℝ), b ∈ Set.Ioi (0 : ℝ) →
      f a + a * g a ≤ f b + a * g b := by
    intro a ha b hb
    rw [hf a ha, hf b hb, hg a ha, hg b hb]
    exact tikhonovResidualValue_add_mul_le hs z ⟨b, hb⟩
  have hjfg : ∀ (a : ℝ) (ha : a ∈ Set.Ioi (0 : ℝ)), j a = f a + a * g a := by
    intro a ha
    rw [hj a ha, hf a ha, hg a ha, tikhonovValue_def]
  -- the subgradient inequality `j β ≤ j α + (β - α) g α`
  have key : ∀ (β : ℝ), β ∈ Set.Ioi (0 : ℝ) → j β ≤ j α + (β - α) * g α := by
    intro β hβ
    have h := hmin β hβ α hα
    rw [hjfg β hβ, hjfg α hα]
    nlinarith [h]
  have hdr' := (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hdr
  have hdl' := (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hdl
  have h1 : dr ≤ g α := by
    refine le_of_tendsto hdr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : α < y := hy
    have hyp : y ∈ Set.Ioi (0 : ℝ) := lt_trans hα0 hy'
    have hk := key y hyp
    rw [slope_def_field, div_le_iff₀ (by linarith : (0 : ℝ) < y - α)]
    nlinarith [hk]
  have h2 : g α ≤ dl := by
    refine ge_of_tendsto hdl' ?_
    filter_upwards [Ioo_mem_nhdsLT hα0] with y hy
    have hyp : y ∈ Set.Ioi (0 : ℝ) := hy.1
    have hy' : y < α := hy.2
    have hk := key y hyp
    rw [slope_def_field, le_div_iff_of_neg (by linarith : y - α < 0)]
    nlinarith [hk]
  exact ⟨h1, h2⟩

/-- Bounds on the one-sided derivatives, the second chain: for `α > 0` at which the one-sided
derivatives `D⁺j(α)` and `D⁻j(α)` exist, `j(α) - α D⁻j(α) ≤ f(α) ≤ j(α) - α D⁺j(α)`.

`j`, `f` and `g` are functions on `ℝ` that agree with the value functions on `(0,∞)`; their
values elsewhere play no role. It holds for every `K`, `K = 0` included. -/
public theorem tikhonovResidualValue_bounds_of_deriv (hs : IsSingularSystem K σ v u) (z : F)
    {j f g : ℝ → ℝ}
    (hj : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), j b = tikhonovValue hs z ⟨b, hb⟩)
    (hf : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), f b = tikhonovResidualValue hs z ⟨b, hb⟩)
    (hg : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), g b = tikhonovNormValue hs z ⟨b, hb⟩)
    {α : ℝ} (hα : α ∈ Set.Ioi (0 : ℝ)) {dr dl : ℝ}
    (hdr : HasDerivWithinAt j dr (Set.Ioi α) α)
    (hdl : HasDerivWithinAt j dl (Set.Iio α) α) :
    j α - α * dl ≤ f α ∧ f α ≤ j α - α * dr := by
  have hα0 : (0 : ℝ) < α := hα
  obtain ⟨h1, h2⟩ := tikhonovValue_deriv_bounds hs z hj hf hg hα hdr hdl
  have hfj : f α = j α - α * g α := by
    rw [hj α hα, hf α hα, hg α hα, tikhonovValue_def]; ring
  refine ⟨?_, ?_⟩
  · rw [hfj]; nlinarith [h2, hα0]
  · rw [hfj]; nlinarith [h1, hα0]

end AutoIp

end _lem_value_derivative_bounds
