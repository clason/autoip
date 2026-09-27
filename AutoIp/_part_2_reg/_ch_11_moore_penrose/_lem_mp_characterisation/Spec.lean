/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
public import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_domain_dense
import AutoIp._part_2_reg._ch_11_moore_penrose._cor_normal_equation

section _lem_mp_characterisation

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- If `Ran(T)` is closed and `S ∈ L(Y,X)` satisfies `T S T = T`, `S T S = S`, and `S T`,
`T S` self-adjoint, then `S = T†`. The equality is stated pointwise on `Y = Dom(T†)`. -/
public theorem eq_moorePenrose_of_comp_eq_of_isSelfAdjoint {T : E →L[𝕜] F} (S : F →L[𝕜] E)
    (hclosed : IsClosed (T.toLinearMap.range : Set F))
    (h1 : T ∘L S ∘L T = T) (h2 : S ∘L T ∘L S = S)
    (h3 : IsSelfAdjoint (S ∘L T)) (h4 : IsSelfAdjoint (T ∘L S)) :
    ∀ y, S y = moorePenrose T ⟨y, (mem_mpDomain_of_isClosed_range hclosed y)⟩ := by
  have e1 : ∀ x : E, T (S (T x)) = T x := fun x =>
    congrArg (fun A : E →L[𝕜] F => A x) h1
  have e2 : ∀ y : F, S (T (S y)) = S y := fun y =>
    congrArg (fun A : F →L[𝕜] E => A y) h2
  have s3 : ∀ u v : E, ⟪S (T u), v⟫_𝕜 = ⟪u, S (T v)⟫_𝕜 :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 h3
  have s4 : ∀ u v : F, ⟪T (S u), v⟫_𝕜 = ⟪u, T (S v)⟫_𝕜 :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 h4
  intro y
  have hls : IsLeastSquares T y (S y) := by
    rw [isLeastSquares_iff_sub_mem_orthogonal_range, Submodule.mem_orthogonal]
    rintro u ⟨x, rfl⟩
    have key : T (S (y - T (S y))) = 0 := by
      rw [map_sub, e2 y, sub_self, map_zero]
    calc ⟪T x, y - T (S y)⟫_𝕜 = ⟪T (S (T x)), y - T (S y)⟫_𝕜 := by rw [e1]
      _ = ⟪T x, T (S (y - T (S y)))⟫_𝕜 := s4 (T x) (y - T (S y))
      _ = 0 := by rw [key, inner_zero_right]
  have hker : S y ∈ (LinearMap.ker T.toLinearMap)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    have hu0 : T u = 0 := hu
    calc ⟪S y, u⟫_𝕜 = ⟪S (T (S y)), u⟫_𝕜 := by rw [e2]
      _ = ⟪S y, S (T u)⟫_𝕜 := s3 (S y) u
      _ = 0 := by rw [hu0, map_zero, inner_zero_right]
  exact eq_moorePenrose_of_isLeastSquares hls hker

end AutoIp

end _lem_mp_characterisation
