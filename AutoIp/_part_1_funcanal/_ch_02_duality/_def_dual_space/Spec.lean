/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Analysis.Normed.Operator.Basic -- shake: keep
import Cite.Attribute

section _def_dual_space

attribute [cite] StrongDual

end _def_dual_space

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/- The duality pairing `⟨x, f⟩ := f x` satisfies `|⟨x, f⟩| ≤ ‖x‖ ‖f‖`. -/
example (x : E) (f : StrongDual 𝕜 E) : ‖f x‖ ≤ ‖x‖ * ‖f‖ :=
  (f.le_opNorm x).trans_eq (mul_comm _ _)
