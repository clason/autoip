/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_18_discretization._lem_lsq_range_closed.Spec
public import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_domain_dense

namespace AutoIp

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- For nested subspaces `Xₙ` with `dim Xₙ = n`, every `y` lies in `Dom((T Pₙ)†)`, since
`Ran(T Pₙ)` is closed. -/
public theorem mem_mpDomain_lsq (T : E →L[𝕜] F) (X : ℕ → Submodule 𝕜 E)
    [∀ n, (X n).HasOrthogonalProjection] (hmono : Monotone X)
    (hfin : ∀ n, Module.finrank 𝕜 (X n) = n) (y : F) (n : ℕ) :
    y ∈ mpDomain (T ∘L (X n).starProjection) :=
  mem_mpDomain_of_isClosed_range (isClosed_range_lsq T X hmono hfin n) y

/-- For finite-dimensional subspaces `Xₙ`, every `y` lies in `Dom((T Pₙ)†)`. -/
public theorem mem_mpDomain_lsq_of_finiteDimensional (T : E →L[𝕜] F) (X : ℕ → Submodule 𝕜 E)
    [∀ n, (X n).HasOrthogonalProjection] (hfd : ∀ n, FiniteDimensional 𝕜 (X n)) (y : F)
    (n : ℕ) : y ∈ mpDomain (T ∘L (X n).starProjection) := by
  have := hfd n
  have : FiniteDimensional 𝕜
      (LinearMap.range (T ∘L (X n).starProjection).toLinearMap) := by
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.map T.toLinearMap (X n)) ?_
    rintro z ⟨x, rfl⟩
    exact ⟨(X n).starProjection x, (X n).starProjection_apply_mem x, rfl⟩
  exact mem_mpDomain_of_isClosed_range (Submodule.closed_of_finiteDimensional _) y

end AutoIp
