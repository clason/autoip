/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_16_tikhonov._def_value_functions
import AutoIp._part_2_reg._ch_16_tikhonov._thm_tikhonov_variational

section _lem_value_monotone

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- The second inequality of the node, `(g(α₁) - g(α₂))(α₁ - α₂) ≤ 0` for all
`α₁, α₂ > 0`, stated as: `g` is antitone on `(0,∞)`.

`f` and `g` are functions on `ℝ` that agree with the value functions on `(0,∞)`; their values
elsewhere play no role. It holds for every `K`, `K = 0` included. -/
public theorem tikhonovNormValue_antitoneOn (hs : IsSingularSystem K σ v u) (z : F)
    {f g : ℝ → ℝ}
    (hf : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), f b = tikhonovResidualValue hs z ⟨b, hb⟩)
    (hg : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), g b = tikhonovNormValue hs z ⟨b, hb⟩) :
    AntitoneOn g (Set.Ioi (0 : ℝ)) := by
  have hmin : ∀ (a : ℝ), a ∈ Set.Ioi (0 : ℝ) → ∀ (b : ℝ), b ∈ Set.Ioi (0 : ℝ) →
      f a + a * g a ≤ f b + a * g b := by
    intro a ha b hb
    rw [hf a ha, hf b hb, hg a ha, hg b hb]
    exact tikhonovResidualValue_add_mul_le hs z ⟨b, hb⟩
  intro a ha b hb hab
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_refl _
  · have h1 := hmin a ha b hb
    have h2 := hmin b hb a ha
    have hba : 0 < b - a := sub_pos.mpr hlt
    have hprod : (b - a) * (g b - g a) ≤ 0 := by
      nlinarith [h1, h2]
    nlinarith [hprod, hba]

/-- The first inequality of the node, `(f(α₁) - f(α₂))(α₁ - α₂) ≥ 0` for all `α₁, α₂ > 0`,
stated as: `f` is monotone on `(0,∞)`.

`f` and `g` are functions on `ℝ` that agree with the value functions on `(0,∞)`; their values
elsewhere play no role. It holds for every `K`, `K = 0` included. -/
public theorem tikhonovResidualValue_monotoneOn (hs : IsSingularSystem K σ v u) (z : F)
    {f g : ℝ → ℝ}
    (hf : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), f b = tikhonovResidualValue hs z ⟨b, hb⟩)
    (hg : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), g b = tikhonovNormValue hs z ⟨b, hb⟩) :
    MonotoneOn f (Set.Ioi (0 : ℝ)) := by
  have hmin : ∀ (a : ℝ), a ∈ Set.Ioi (0 : ℝ) → ∀ (b : ℝ), b ∈ Set.Ioi (0 : ℝ) →
      f a + a * g a ≤ f b + a * g b := by
    intro a ha b hb
    rw [hf a ha, hf b hb, hg a ha, hg b hb]
    exact tikhonovResidualValue_add_mul_le hs z ⟨b, hb⟩
  intro a ha b hb hab
  have ha0 : (0 : ℝ) < a := ha
  have hgle := tikhonovNormValue_antitoneOn hs z hf hg ha hb hab
  nlinarith [hmin a ha b hb, mul_nonneg ha0.le (sub_nonneg.mpr hgle)]

end AutoIp

end _lem_value_monotone
