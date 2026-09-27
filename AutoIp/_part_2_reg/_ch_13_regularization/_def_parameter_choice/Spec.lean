/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose

section _def_parameter_choice

namespace AutoIp

open Filter Topology

/-- A parameter choice rule: a map `α : (0,∞) × Y → (0,∞)`. -/
public structure ParameterChoice (F : Type*) where
  /-- The map `(δ, y^δ) ↦ α(δ, y^δ)`, taking a noise level `δ > 0` and a datum `y^δ ∈ Y`.
  Its codomain is `ℝ`; a further field restricts it to `(0,∞)`. -/
  rule : Set.Ioi (0 : ℝ) → F → ℝ
  /-- The values `α(δ, y^δ)` lie in `(0,∞)`. -/
  pos : ∀ (δ : Set.Ioi (0 : ℝ)) (y : F), 0 < rule δ y

/-- A parameter choice rule is applied as the map `α(δ, y^δ)`, written `a δ y`. -/
public instance {F : Type*} : FunLike (ParameterChoice F) (Set.Ioi (0 : ℝ)) (F → ℝ) where
  coe a := a.rule
  coe_injective a b h := by cases a; cases b; congr

/-- The rule `(δ, y^δ) ↦ α(τδ, y^δ)` for `τ > 0`. The node does not state this rule; later
nodes state their hypotheses with it. -/
public def ParameterChoice.scale {F : Type*} (a : ParameterChoice F) (τ : ℝ) (hτ : 0 < τ) :
    ParameterChoice F where
  rule δ z := a ⟨τ * (δ : ℝ), mul_pos hτ δ.2⟩ z
  pos δ z := a.pos ⟨τ * (δ : ℝ), mul_pos hτ δ.2⟩ z

/-- The rule is *a priori*: `α(δ, y^δ)` depends only on `δ`. -/
@[expose]
public def ParameterChoice.IsAPriori {F : Type*} (a : ParameterChoice F) : Prop :=
  ∀ (δ : Set.Ioi (0 : ℝ)) (y z : F), a δ y = a δ z

/-- The rule is *heuristic*: `α(δ, y^δ)` depends only on `y^δ`. -/
@[expose]
public def ParameterChoice.IsHeuristic {F : Type*} (a : ParameterChoice F) : Prop :=
  ∀ (δ ε : Set.Ioi (0 : ℝ)) (y : F), a δ y = a ε y

/-- The parameter `α(δ, y^δ)` as an element of `(0,∞)`, the index set of the family
`{R_α}_{α>0}`. -/
@[expose]
public def ParameterChoice.param {F : Type*} (a : ParameterChoice F) (δ : Set.Ioi (0 : ℝ)) (z : F) :
    Set.Ioi (0 : ℝ) :=
  ⟨a δ z, a.pos δ z⟩

/-- `(R_α, α)` is a convergent regularization method: for every `y ∈ Dom(T†)`,
`lim_{δ→0} sup_{y^δ ∈ B_δ(y)} ‖R_{α(δ,y^δ)} y^δ − T†y‖ = 0`. The family `{R_α}` is any
family of maps `Y → X`; it is not required to be a regularization of `T†`. -/
@[expose]
public def IsRegularizationMethod {𝕜 : Type*} [RCLike 𝕜] {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] (T : E →L[𝕜] F) (R : Set.Ioi (0 : ℝ) → F → E)
    (a : ParameterChoice F) :
    Prop :=
  ∀ y, ∀ hy : y ∈ mpDomain T, ∀ ε > (0 : ℝ), ∃ δ₀ > (0 : ℝ),
    ∀ δ, ∀ hδ : δ ∈ Set.Ioo (0 : ℝ) δ₀, ∀ z : F, ‖y - z‖ ≤ δ →
      ‖R (a.param ⟨δ, hδ.1⟩ z) z - moorePenrose T ⟨y, hy⟩‖ < ε

end AutoIp

end _def_parameter_choice
