/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_13_regularization._def_parameter_choice.Spec
import all AutoIp._part_2_reg._ch_13_regularization._def_parameter_choice.Spec

namespace AutoIp

variable {F : Type*}

/-- The scaled rule takes the value `α(τδ, y^δ)` at `(δ, y^δ)`. -/
public theorem ParameterChoice.scale_apply (a : ParameterChoice F) {τ : ℝ} (hτ : 0 < τ)
    (δ : Set.Ioi (0 : ℝ)) (z : F) :
    (a.scale τ hτ) δ z = a ⟨τ * (δ : ℝ), mul_pos hτ δ.2⟩ z := by
  unfold ParameterChoice.scale
  rfl

/-- Two rules with equal values at their arguments select equal parameters in `(0,∞)`. -/
public theorem ParameterChoice.param_congr (a : ParameterChoice F) {b : ParameterChoice F}
    {δ ε : Set.Ioi (0 : ℝ)} {y z : F} (h : a δ y = b ε z) : a.param δ y = b.param ε z :=
  Subtype.ext h

end AutoIp
