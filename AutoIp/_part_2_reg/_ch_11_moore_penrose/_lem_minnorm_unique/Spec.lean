/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_lsq_minnorm

section _lem_minnorm_unique

namespace AutoIp

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Any two minimum norm solutions of `T x = y` are equal. -/
public theorem IsMinimumNorm.unique {T : E →L[𝕜] F} {y : F} {x x' : E}
    (hx : IsMinimumNorm T y x) (hx' : IsMinimumNorm T y x') : x = x' := by
  obtain ⟨h1, h2⟩ := isMinimumNorm_iff.1 hx
  obtain ⟨h1', h2'⟩ := isMinimumNorm_iff.1 hx'
  have hker : x - x' ∈ LinearMap.ker T.toLinearMap := by
    have hmem : T x - T x' ∈ LinearMap.range T.toLinearMap :=
      Submodule.sub_mem _ ⟨x, rfl⟩ ⟨x', rfl⟩
    have hmem' : T x - T x' ∈ (LinearMap.range T.toLinearMap)ᗮ := by
      have he : T x - T x' = (y - T x') - (y - T x) := by abel
      rw [he]
      exact Submodule.sub_mem _ h1' h1
    have h0 : T x - T x' = 0 := sub_eq_zero.2 (hx.isLeastSquares.apply_eq hx'.isLeastSquares)
    have : T (x - x') = 0 := by rw [map_sub]; exact h0
    exact this
  have hperp : x - x' ∈ (LinearMap.ker T.toLinearMap)ᗮ := Submodule.sub_mem _ h2 h2'
  have := Submodule.disjoint_def.1
    (Submodule.orthogonal_disjoint (LinearMap.ker T.toLinearMap)) _ hker hperp
  rwa [sub_eq_zero] at this

end AutoIp

end _lem_minnorm_unique
