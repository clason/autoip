/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_18_discretization._def_lsq_projection

section _def_dual_lsq_projection

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The dual least-squares projection `xₙ := Tₙ† Qₙ y`, where `Qₙ := P_{Yₙ}` is the
orthogonal projection onto `Y n` and `Tₙ := Qₙ T`.

The conditions the blueprint places on the subspaces (`dim Ran(T)‾ = ∞`,
`Y₁ ⊂ Y₂ ⊂ ⋯ ⊂ Ker(T*)ᗮ` with `dim Yₙ = n` and union dense in `Ker(T*)ᗮ`) are not part of the
definition; the results that use it assume them. Neither are `Xₙ := T* Yₙ` and `Pₙ := P_{Xₙ}`:
those results take a subspace `X n` with the hypothesis `X n = T* (Y n)`. The hypothesis
that `Qₙ y ∈ Dom(Tₙ†)` for every `n` is there because the Moore–Penrose inverse needs it; for nested
`Y n` with `dim Yₙ = n` it holds for every `y ∈ Y`. -/
public noncomputable def dualLsqProjection (T : E →L[𝕜] F) (Y : ℕ → Submodule 𝕜 F)
    [∀ n, (Y n).HasOrthogonalProjection] (y : F)
    (hy : ∀ n, (Y n).starProjection y ∈ mpDomain ((Y n).starProjection ∘L T)) (n : ℕ) : E :=
  moorePenrose ((Y n).starProjection ∘L T) ⟨((Y n).starProjection y), (hy n)⟩

end AutoIp

end _def_dual_lsq_projection
