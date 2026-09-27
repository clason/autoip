/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose

section _thm_mp_minnorm

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- (i), the least squares solutions of `T x = y` are exactly the solutions of
`T x = P_R y`. The Lean holds for every `y ∈ Y`, not only `y ∈ Dom(T†)`; existence of a
least squares solution is not stated here and follows from (ii). -/
public theorem isLeastSquares_iff_apply_eq_starProjection [CompleteSpace F] {T : E →L[𝕜] F} {y : F}
    {x : E} :
    IsLeastSquares T y x ↔
      T x = T.toLinearMap.range.topologicalClosure.starProjection y := by
  rw [isLeastSquares_iff_sub_mem_orthogonal_range]
  constructor
  · intro h
    refine (Submodule.eq_starProjection_of_mem_orthogonal
      ((LinearMap.range T.toLinearMap).le_topologicalClosure ⟨x, rfl⟩) ?_).symm
    rw [Submodule.orthogonal_closure]
    exact h
  · intro h
    rw [h, ← Submodule.orthogonal_closure]
    exact Submodule.sub_starProjection_mem_orthogonal y

/-- (ii), for `y ∈ Dom(T†)` the set of all least squares solutions of `T x = y` is
`x† + Ker(T)`, where `x† := T† y`. -/
public theorem setOf_isLeastSquares [CompleteSpace E] {T : E →L[𝕜] F}
    (y : (moorePenrose T).domain) :
    {x : E | IsLeastSquares T (y : F) x} =
      (fun n => moorePenrose T y + n) '' (T.toLinearMap.ker : Set E) := by
  have hmp : y - T (moorePenrose T y) ∈ (LinearMap.range T.toLinearMap)ᗮ :=
    sub_apply_moorePenrose_mem_orthogonal y
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe]
  constructor
  · intro hx
    refine ⟨x - moorePenrose T y, ?_, by abel⟩
    have h0 : T x - T (moorePenrose T y) = 0 :=
      sub_eq_zero.2 (hx.apply_eq (isLeastSquares_iff_sub_mem_orthogonal_range.2 hmp))
    have hk : T (x - moorePenrose T y) = 0 := by rw [map_sub]; exact h0
    exact hk
  · rintro ⟨n, hn, rfl⟩
    rw [isLeastSquares_iff_sub_mem_orthogonal_range]
    have h0 : T n = 0 := hn
    have he : y - T (moorePenrose T y + n) = y - T (moorePenrose T y) := by
      rw [map_add, h0, add_zero]
    rw [he]
    exact hmp

end AutoIp

end _thm_mp_minnorm
