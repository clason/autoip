/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_domain
import AutoIp._part_2_reg._ch_11_moore_penrose._thm_mp_minnorm

section _lem_mp_domain_dense

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- `Dom(T†)` is dense in `Y`. -/
public theorem dense_domain_moorePenrose [CompleteSpace E] [CompleteSpace F] {T : E →L[𝕜] F} :
    Dense ((moorePenrose T).domain : Set F) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro z hz
  have h1 : z ∈ (LinearMap.range T.toLinearMap)ᗮ :=
    Submodule.orthogonal_le le_sup_left hz
  have h2 : z ∈ (LinearMap.range T.toLinearMap)ᗮᗮ :=
    Submodule.orthogonal_le le_sup_right hz
  exact Submodule.disjoint_def.1
    (Submodule.orthogonal_disjoint (LinearMap.range T.toLinearMap)ᗮ) _ h1 h2

/-- `Dom(T†) = Y` if and only if `Ran(T)` is closed. -/
public theorem mpDomain_eq_top_iff [CompleteSpace F] {T : E →L[𝕜] F} :
    mpDomain T = ⊤ ↔ IsClosed (T.toLinearMap.range : Set F) := by
  constructor
  · intro h
    have hle : (LinearMap.range T.toLinearMap).topologicalClosure ≤
        LinearMap.range T.toLinearMap := by
      intro y hy
      have hmem : y ∈ mpDomain T := by rw [h]; exact Submodule.mem_top
      have h2 := mem_mpDomain_iff.1 hmem
      rwa [Submodule.starProjection_eq_self_iff.2 hy] at h2
    have heq : (LinearMap.range T.toLinearMap).topologicalClosure =
        LinearMap.range T.toLinearMap :=
      le_antisymm hle (LinearMap.range T.toLinearMap).le_topologicalClosure
    rw [← closure_eq_iff_isClosed, ← Submodule.topologicalClosure_coe, heq]
  · intro h
    have : CompleteSpace (LinearMap.range T.toLinearMap) := h.completeSpace_coe
    exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

/-- For `y ∈ Ran(T)ᗮ` one has `T† y = 0`. -/
public theorem moorePenrose_eq_zero_of_mem_orthogonal_range [CompleteSpace E] {T : E →L[𝕜] F}
    {y : F} (hy : y ∈ T.toLinearMap.rangeᗮ) :
    moorePenrose T ⟨y, (Submodule.mem_sup_right hy)⟩ = 0 := by
  exact (moorePenrose_isMinimumNorm _).unique
    (isMinimumNorm_iff.2 ⟨by simpa using hy, Submodule.zero_mem _⟩)

end AutoIp

end _lem_mp_domain_dense
