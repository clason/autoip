/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_08_svd._def_singular_system

section _cor_sigma_null

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F}

/-- If `dim ℛ(K) = ∞` then the index set of a singular system of `K` is infinite. This is stated
for a singular system without the ordering conditions and over an arbitrary index type. -/
public theorem IsSingularSystem.infinite_of_not_finiteDimensional_range
    {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F} (hs : IsSingularSystem K σ v u)
    (h : ¬ FiniteDimensional 𝕜 K.toLinearMap.range) : Infinite ι := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  have hfd : FiniteDimensional 𝕜 (Submodule.span 𝕜 (Set.range u)) :=
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range u)
  have hclosed : (Submodule.span 𝕜 (Set.range u)).topologicalClosure
      = Submodule.span 𝕜 (Set.range u) :=
    (Submodule.span 𝕜
      (Set.range u)).closed_of_finiteDimensional.submodule_topologicalClosure_eq
  have hle : LinearMap.range K.toLinearMap ≤ Submodule.span 𝕜 (Set.range u) := by
    have hsub : LinearMap.range K.toLinearMap
        ≤ (LinearMap.range K.toLinearMap).topologicalClosure :=
      Submodule.le_topologicalClosure _
    rwa [← hs.span_right, hclosed] at hsub
  exact h (Submodule.finiteDimensional_of_le hle)

/-- If `dim ℛ(K) = ∞` then the index set `I` of a singular system of `K` is infinite and `σₙ → 0`.
The singular system is any one of `K`, not only the one the singular value decomposition gives. -/
public
theorem IsOrderedSingularSystem.infinite_and_tendsto_zero_of_not_finiteDimensional_range {I : Set ℕ}
    {σ : I → ℝ} {v : I → E} {u : I → F} (hs : IsOrderedSingularSystem K σ v u)
    (h : ¬ FiniteDimensional 𝕜 K.toLinearMap.range) :
    I.Infinite ∧ Filter.Tendsto σ Filter.atTop (nhds 0) := by
  have hI : I.Infinite :=
    Set.infinite_coe_iff.1 (hs.toIsSingularSystem.infinite_of_not_finiteDimensional_range h)
  exact ⟨hI, hs.tendsto_zero hI⟩

end _cor_sigma_null
