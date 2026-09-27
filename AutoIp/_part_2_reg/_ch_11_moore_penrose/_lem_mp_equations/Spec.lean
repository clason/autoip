/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
public import Mathlib.Topology.GDelta.MetrizableSpace
import AutoIp._part_2_reg._ch_11_moore_penrose._thm_mp_minnorm

section _lem_mp_equations

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- `Ran(T†) = Ker(T)ᗮ`. -/
public theorem moorePenrose_image_mpDomain {T : E →L[𝕜] F} :
    Set.range (fun y : mpDomain T => moorePenrose T ⟨y, y.2⟩)
      = (T.toLinearMap.kerᗮ : Set E) := by
  ext x
  constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩
    exact moorePenrose_mem_orthogonal_ker ⟨_, hy⟩
  · intro hx
    refine ⟨⟨T x, Submodule.mem_sup_left ⟨x, rfl⟩⟩, ?_⟩
    refine (moorePenrose_isMinimumNorm ⟨_, (Submodule.mem_sup_left ⟨x, rfl⟩)⟩).unique
      (isMinimumNorm_iff.2 ⟨?_, hx⟩)
    simp

/-- (i), `T T† T = T` on `X`. -/
public theorem self_comp_moorePenrose_comp_self {T : E →L[𝕜] F} (x : E) :
    T (moorePenrose T ⟨(T x), (Submodule.mem_sup_left ⟨x, rfl⟩)⟩) = T x := by
  have hmem : T x ∈ mpDomain T := Submodule.mem_sup_left ⟨x, rfl⟩
  obtain ⟨h1, -⟩ := isMinimumNorm_iff.1 (moorePenrose_isMinimumNorm ⟨_, hmem⟩)
  have hmemR : T x - T (moorePenrose T ⟨(T x), (Submodule.mem_sup_left ⟨x,
      rfl⟩)⟩) ∈ LinearMap.range T.toLinearMap :=
    Submodule.sub_mem _ ⟨x, rfl⟩ ⟨moorePenrose T ⟨(T x), (Submodule.mem_sup_left ⟨x, rfl⟩)⟩, rfl⟩
  have h0 : T x - T (moorePenrose T ⟨(T x), (Submodule.mem_sup_left ⟨x, rfl⟩)⟩) = 0 :=
    Submodule.disjoint_def.1
      (Submodule.orthogonal_disjoint (LinearMap.range T.toLinearMap)) _ hmemR h1
  rw [sub_eq_zero] at h0
  exact h0.symm

/-- (ii), `T† T T† = T†` on `Dom(T†)`. -/
public
theorem moorePenrose_comp_self_comp_moorePenrose {T : E →L[𝕜] F} {y : F} (hy : y ∈ mpDomain T) :
    moorePenrose T ⟨(T (moorePenrose T ⟨y, hy⟩)), (Submodule.mem_sup_left ⟨moorePenrose T ⟨y,
        hy⟩, rfl⟩)⟩ = moorePenrose T ⟨y, hy⟩ := by
  have hx : moorePenrose T ⟨y, hy⟩ ∈ (LinearMap.ker T.toLinearMap)ᗮ :=
    moorePenrose_mem_orthogonal_ker ⟨_, hy⟩
  refine (moorePenrose_isMinimumNorm
    ⟨_, Submodule.mem_sup_left ⟨moorePenrose T ⟨y, hy⟩, rfl⟩⟩).unique (isMinimumNorm_iff.2 ⟨?_, hx⟩)
  simp

/-- (iii), `T† T = Id - P_N` on `X`. -/
public theorem moorePenrose_apply_apply {T : E →L[𝕜] F} (x : E) :
    moorePenrose T ⟨(T x), (Submodule.mem_sup_left ⟨x, rfl⟩)⟩ =
      x - T.toLinearMap.ker.starProjection x := by
  have hmem : T x ∈ mpDomain T := Submodule.mem_sup_left ⟨x, rfl⟩
  refine (moorePenrose_isMinimumNorm ⟨_, hmem⟩).unique (isMinimumNorm_iff.2 ⟨?_, ?_⟩)
  · have h0 : T ((LinearMap.ker T.toLinearMap).starProjection x) = 0 :=
      LinearMap.mem_ker.1 (Submodule.starProjection_apply_mem _ _)
    rw [map_sub, h0, sub_zero, sub_self]
    exact Submodule.zero_mem _
  · exact (LinearMap.ker T.toLinearMap).sub_starProjection_mem_orthogonal x

/-- (iv), `T T† = P_R` on `Dom(T†)`. -/
public theorem apply_moorePenrose [CompleteSpace F] {T : E →L[𝕜] F} (y : (moorePenrose T).domain) :
    T (moorePenrose T y) =
      T.toLinearMap.range.topologicalClosure.starProjection (y : F) := by
  obtain ⟨h1, -⟩ := isMinimumNorm_iff.1 (moorePenrose_isMinimumNorm y)
  refine (Submodule.eq_starProjection_of_mem_orthogonal
    ((LinearMap.range T.toLinearMap).le_topologicalClosure ⟨moorePenrose T y, rfl⟩) ?_).symm
  rw [Submodule.orthogonal_closure]
  exact h1

end AutoIp

end _lem_mp_equations
