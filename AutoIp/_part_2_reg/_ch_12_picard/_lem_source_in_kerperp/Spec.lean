/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_12_picard._def_source_set

section _lem_source_in_kerperp

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- `X_{ν,ρ} ⊆ Ker(K)ᗮ` for all `ν, ρ > 0`. -/
public
theorem sourceSet_subset_orthogonal_ker (hs : IsSingularSystem K σ v u) {ν ρ : ℝ} (hν : 0 < ν)
    (hρ : 0 < ρ) :
    sourceSet hs ν hν ρ hρ ⊆ (K.toLinearMap.kerᗮ : Set E) := by
  have hvU : ∀ i, v i ∈ (LinearMap.ker K.toLinearMap)ᗮ := fun i => by
    rw [← hs.span_left]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)
  intro x hx
  rw [SetLike.mem_coe, ← SetLike.mem_coe]
  rw [mem_sourceSet_iff] at hx
  obtain ⟨w, -, rfl⟩ := hx
  rw [SetLike.mem_coe]
  refine (Submodule.isClosed_orthogonal _).mem_of_tendsto (hs.hasSum_absRpow hν w) ?_
  exact Filter.Eventually.of_forall fun s =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hvU i)

end AutoIp

end _lem_source_in_kerperp
