/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_16_tikhonov._def_value_functions
public import Mathlib.Analysis.Calculus.Deriv.Basic
import AutoIp._part_2_reg._ch_16_tikhonov._thm_tikhonov_variational
import Mathlib.Analysis.Convex.Deriv

section _lem_value_concave

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- The whole node: `j` is concave and nondecreasing on `(0,∞)`, and at every `α > 0` the
one-sided derivatives `D⁺j(α)` and `D⁻j(α)` exist and satisfy `D⁺j(α) ≤ D⁻j(α)`.

`j`, `f` and `g` are functions on `ℝ` that agree with the value functions on `(0,∞)`; their
values elsewhere play no role. It holds for every `K`, `K = 0` included. -/
public theorem tikhonovValue_concaveOn (hs : IsSingularSystem K σ v u) (z : F)
    {j f g : ℝ → ℝ}
    (hj : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), j b = tikhonovValue hs z ⟨b, hb⟩)
    (hf : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), f b = tikhonovResidualValue hs z ⟨b, hb⟩)
    (hg : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), g b = tikhonovNormValue hs z ⟨b, hb⟩) :
    ConcaveOn ℝ (Set.Ioi (0 : ℝ)) j ∧
      MonotoneOn j (Set.Ioi (0 : ℝ)) ∧
      ∀ α > (0 : ℝ), ∃ dr dl : ℝ,
        HasDerivWithinAt j dr (Set.Ioi α) α ∧
          HasDerivWithinAt j dl (Set.Iio α) α ∧ dr ≤ dl := by
  have hmin : ∀ (a : ℝ), a ∈ Set.Ioi (0 : ℝ) → ∀ (b : ℝ), b ∈ Set.Ioi (0 : ℝ) →
      f a + a * g a ≤ f b + a * g b := by
    intro a ha b hb
    rw [hf a ha, hf b hb, hg a ha, hg b hb]
    exact tikhonovResidualValue_add_mul_le hs z ⟨b, hb⟩
  have hjfg : ∀ (a : ℝ) (ha : a ∈ Set.Ioi (0 : ℝ)), j a = f a + a * g a := by
    intro a ha
    rw [hj a ha, hf a ha, hg a ha, tikhonovValue_def]
  have hgn : ∀ (a : ℝ) (ha : a ∈ Set.Ioi (0 : ℝ)), 0 ≤ g a := by
    intro a ha
    rw [hg a ha, tikhonovNormValue_def]
    positivity
  -- `j` is an infimum of the affine functions `α ↦ J_α(x)`, hence concave.
  have hconc : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) j := by
    refine ⟨convex_Ioi 0, ?_⟩
    intro x hx y hy a b ha hb hab
    have hx0 : (0 : ℝ) < x := hx
    have hy0 : (0 : ℝ) < y := hy
    simp only [smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    have hp : (0 : ℝ) < a * x + (1 - a) * y := by
      rcases ha.lt_or_eq with h | h
      · have h3 := mul_pos h hx0
        have h4 := mul_nonneg hb hy0.le
        linarith
      · rw [← h]
        have h5 : (1 : ℝ) - 0 = 1 := by ring
        rw [h5]
        linarith
    have hpm : a * x + (1 - a) * y ∈ Set.Ioi (0 : ℝ) := hp
    have h1 := hmin x hx _ hpm
    have h2 := hmin y hy _ hpm
    rw [hjfg x hx, hjfg y hy, hjfg _ hpm]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
  refine ⟨hconc, ?_, ?_⟩
  · -- `J_{α₁}(x) ≤ J_{α₂}(x)` for `α₁ ≤ α₂`, since `g ≥ 0`.
    intro a ha b hb hab
    have ha0 : (0 : ℝ) < a := ha
    have h1 := hmin a ha b hb
    rw [hjfg a ha, hjfg b hb]
    nlinarith [h1, hgn b hb, hab]
  · -- One-sided derivatives: Mathlib's convex-function derivatives, applied to `-j`.
    intro α hα
    have hint : α ∈ interior (Set.Ioi (0 : ℝ)) := by rwa [interior_Ioi]
    have hcvx : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (-j) := hconc.neg
    have hr := hcvx.hasDerivWithinAt_rightDeriv_of_mem_interior hint
    have hl := hcvx.hasDerivWithinAt_leftDeriv_of_mem_interior hint
    have hrl := hcvx.leftDeriv_le_rightDeriv_of_mem_interior hint
    refine ⟨-(derivWithin (-j) (Set.Ioi α) α), -(derivWithin (-j) (Set.Iio α) α),
      ?_, ?_, by linarith⟩
    · simpa using hr.neg
    · simpa using hl.neg

/-- `j` is nondecreasing on `(0,∞)`.

`j`, `f` and `g` are functions on `ℝ` that agree with the value functions on `(0,∞)`. It holds for
every `K`, `K = 0` included. -/
public theorem tikhonovValue_monotoneOn (hs : IsSingularSystem K σ v u) (z : F)
    {j f g : ℝ → ℝ}
    (hj : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), j b = tikhonovValue hs z ⟨b, hb⟩)
    (hf : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), f b = tikhonovResidualValue hs z ⟨b, hb⟩)
    (hg : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), g b = tikhonovNormValue hs z ⟨b, hb⟩) :
    MonotoneOn j (Set.Ioi (0 : ℝ)) :=
  (tikhonovValue_concaveOn hs z hj hf hg).2.1

/-- At every `α > 0` the one-sided derivatives `D⁺j(α)` and `D⁻j(α)` exist and satisfy
`D⁺j(α) ≤ D⁻j(α)`.

`j`, `f` and `g` are functions on `ℝ` that agree with the value functions on `(0,∞)`. It holds for
every `K`, `K = 0` included. -/
public theorem exists_hasDerivWithinAt_tikhonovValue (hs : IsSingularSystem K σ v u) (z : F)
    {j f g : ℝ → ℝ}
    (hj : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), j b = tikhonovValue hs z ⟨b, hb⟩)
    (hf : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), f b = tikhonovResidualValue hs z ⟨b, hb⟩)
    (hg : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), g b = tikhonovNormValue hs z ⟨b, hb⟩) :
    ∀ α > (0 : ℝ), ∃ dr dl : ℝ,
      HasDerivWithinAt j dr (Set.Ioi α) α ∧
        HasDerivWithinAt j dl (Set.Iio α) α ∧ dr ≤ dl :=
  (tikhonovValue_concaveOn hs z hj hf hg).2.2

end AutoIp

end _lem_value_concave
