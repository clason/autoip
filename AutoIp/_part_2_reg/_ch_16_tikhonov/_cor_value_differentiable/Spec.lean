/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_16_tikhonov._def_value_functions
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import AutoIp._part_2_reg._ch_16_tikhonov._lem_value_concave
import AutoIp._part_2_reg._ch_16_tikhonov._lem_value_derivative_bounds
import Mathlib.Analysis.Calculus.Monotone

section _cor_value_differentiable

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Differentiability of the value function: for almost every `α > 0`, `j` is differentiable
at `α` with `j'(α) = g(α)`.

`j`, `f` and `g` are functions on `ℝ` that agree with the value functions on `(0,∞)`; their
values elsewhere play no role. It holds for every `K`, `K = 0` included. -/
public theorem tikhonovValue_ae_hasDerivAt (hs : IsSingularSystem K σ v u) (z : F)
    {j f g : ℝ → ℝ}
    (hj : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), j b = tikhonovValue hs z ⟨b, hb⟩)
    (hf : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), f b = tikhonovResidualValue hs z ⟨b, hb⟩)
    (hg : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), g b = tikhonovNormValue hs z ⟨b, hb⟩) :
    ∀ᵐ α ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), HasDerivAt j (g α) α := by
  have hmono := tikhonovValue_monotoneOn hs z hj hf hg
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [hmono.ae_differentiableWithinAt_of_mem] with α hα hmem
  have hd : DifferentiableAt ℝ j α := (hα hmem).differentiableAt (isOpen_Ioi.mem_nhds hmem)
  have hda : HasDerivAt j (deriv j α) α := hd.hasDerivAt
  obtain ⟨h1, h2⟩ := tikhonovValue_deriv_bounds hs z hj hf hg hmem
    (hda.hasDerivWithinAt (s := Set.Ioi α)) (hda.hasDerivWithinAt (s := Set.Iio α))
  have hderiv : deriv j α = g α := le_antisymm h1 h2
  rwa [hderiv] at hda

end AutoIp

end _cor_value_differentiable
