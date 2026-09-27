/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose

section _def_lsq_projection

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The least-squares projection `xₙ := Tₙ† y`, where `Pₙ := P_{Xₙ}` is the orthogonal
projection onto `X n` and `Tₙ := T Pₙ`.

The conditions the blueprint places on the subspaces (`dim X = ∞`, `X₁ ⊂ X₂ ⊂ ⋯` with
`dim Xₙ = n` and dense union) are not part of the definition; the results that use it assume
them. The hypothesis that `y ∈ Dom(Tₙ†)` for every `n` is there because the Moore–Penrose
inverse needs it; under those conditions it holds for every `y ∈ Y`. -/
public noncomputable def lsqProjection (T : E →L[𝕜] F) (X : ℕ → Submodule 𝕜 E)
    [∀ n, (X n).HasOrthogonalProjection] (y : F)
    (hy : ∀ n, y ∈ mpDomain (T ∘L (X n).starProjection)) (n : ℕ) : E :=
  moorePenrose (T ∘L (X n).starProjection) ⟨y, (hy n)⟩

end AutoIp

end _def_lsq_projection
