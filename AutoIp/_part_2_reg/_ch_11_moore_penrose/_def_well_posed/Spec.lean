/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.RCLike.Basic

section _def_well_posed

namespace AutoIp

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The equation `T x = y` is well-posed in the sense of Hadamard: conditions (i)–(iii) hold.
It is ill-posed if this fails. -/
public structure IsWellPosed (T : E →ₗ[𝕜] F) : Prop where
  /-- Condition (i): for every `y ∈ Y` there is `x ∈ X` with `T x = y`. -/
  surjective : ∀ y : F, ∃ x : E, T x = y
  /-- Condition (ii): that `x` is unique. -/
  injective : ∀ x x' : E, T x = T x' → x = x'
  /-- Condition (iii): the solution depends continuously on the datum: for all `x ∈ X` and
all sequences `(xₙ)` in `X` with `T xₙ → T x`, one has `xₙ → x`. -/
  stable : ∀ (x : E) (u : ℕ → E), Filter.Tendsto (fun n => T (u n)) Filter.atTop (nhds (T x)) →
    Filter.Tendsto u Filter.atTop (nhds x)

end AutoIp

end _def_well_posed
