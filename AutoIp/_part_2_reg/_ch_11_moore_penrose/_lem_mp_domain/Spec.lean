/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose

section _lem_mp_domain

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- For `y ∈ Y`, `y ∈ Dom(T†)` if and only if `P_R y ∈ Ran(T)`. -/
public theorem mem_mpDomain_iff {T : E →L[𝕜] F} {y : F} :
    y ∈ mpDomain T ↔
      T.toLinearMap.range.topologicalClosure.starProjection y ∈
        T.toLinearMap.range := by
  set R := LinearMap.range T.toLinearMap with hRdef
  have hperp : R.topologicalClosureᗮ = Rᗮ := Submodule.orthogonal_closure R
  constructor
  · intro hy
    rw [mpDomain, ← hRdef, Submodule.mem_sup] at hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    have hproj : R.topologicalClosure.starProjection (a + b) = a :=
      Submodule.eq_starProjection_of_mem_orthogonal' (R.le_topologicalClosure ha)
        (by rw [hperp]; exact hb) rfl
    rw [hproj]
    exact ha
  · intro h
    have hb : y - R.topologicalClosure.starProjection y ∈ Rᗮ := by
      rw [← hperp]
      exact Submodule.sub_starProjection_mem_orthogonal y
    have hsum := Submodule.add_mem_sup (S := R) (T := Rᗮ) h hb
    have he : R.topologicalClosure.starProjection y + (y - R.topologicalClosure.starProjection y)
        = y := by abel
    rw [he] at hsum
    exact hsum

end AutoIp

end _lem_mp_domain
