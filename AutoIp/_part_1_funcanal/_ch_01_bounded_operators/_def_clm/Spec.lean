/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
import Cite.Attribute

section _def_clm

attribute [cite] ContinuousLinearMap
attribute [cite] ContinuousLinearMap.opNorm

attribute [cite] SemilinearMapClass.bound_of_continuous
attribute [cite] AddMonoidHomClass.continuous_of_bound

end _def_clm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/- For linear maps, boundedness and continuity coincide. -/
example (T : E →ₗ[𝕜] F) : Continuous T ↔ ∃ C ≥ 0, ∀ x, ‖T x‖ ≤ C * ‖x‖ :=
  ⟨fun h => let ⟨C, hC, hT⟩ := SemilinearMapClass.bound_of_continuous T h; ⟨C, hC.le, hT⟩,
    fun ⟨C, _, hT⟩ => AddMonoidHomClass.continuous_of_bound T C hT⟩
