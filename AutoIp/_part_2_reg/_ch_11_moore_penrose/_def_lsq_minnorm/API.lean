/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_lsq_minnorm.Spec
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.InnerProductSpace.Orthogonal

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜]

/-- For orthogonal `a` and `b`, `‖a‖ ≤ ‖a + b‖`. -/
public theorem norm_le_norm_add_of_inner_eq_zero {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] {a b : G} (h : ⟪a, b⟫_𝕜 = 0) : ‖a‖ ≤ ‖a + b‖ := by
  have hsq : ‖a + b‖ * ‖a + b‖ = ‖a‖ * ‖a‖ + ‖b‖ * ‖b‖ :=
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h
  refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
  simp only [pow_two]
  rw [hsq]
  linarith [mul_self_nonneg ‖b‖]

/-- `x` is a least squares solution of `T x = y` if and only if `y - T x ∈ Ran(T)ᗮ`. -/
public theorem isLeastSquares_iff_sub_mem_orthogonal_range {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    {T : E →L[𝕜] F} {y : F} {x : E} :
    IsLeastSquares T y x ↔ y - T x ∈ T.toLinearMap.rangeᗮ := by
  have hmemR : ∀ z : E, T z ∈ LinearMap.range T.toLinearMap := fun z => ⟨z, rfl⟩
  have hbdd : ∀ u : F, BddBelow (Set.range fun w : LinearMap.range T.toLinearMap => ‖u - w‖) := by
    intro u
    refine ⟨0, ?_⟩
    rintro a ⟨b, rfl⟩
    exact norm_nonneg _
  constructor
  · intro h
    rw [Submodule.mem_orthogonal']
    refine (Submodule.norm_eq_iInf_iff_inner_eq_zero _ (hmemR x)).1 ?_
    refine le_antisymm (le_ciInf ?_) ?_
    · rintro ⟨w, z, rfl⟩
      change ‖y - T x‖ ≤ ‖y - T z‖
      rw [norm_sub_rev y (T x), norm_sub_rev y (T z)]
      exact h z
    · exact ciInf_le (hbdd y) (⟨T x, hmemR x⟩ : LinearMap.range T.toLinearMap)
  · intro h z
    have hz : ⟪T z - T x, T x - y⟫_𝕜 = 0 := by
      have h0 : ⟪T z - T x, y - T x⟫_𝕜 = 0 :=
        (Submodule.mem_orthogonal _ _).1 h _ (Submodule.sub_mem _ (hmemR z) (hmemR x))
      have : T x - y = -(y - T x) := by abel
      rw [this, inner_neg_right, h0, neg_zero]
    have he : T z - y = (T x - y) + (T z - T x) := by abel
    rw [he]
    exact norm_le_norm_add_of_inner_eq_zero (by rwa [inner_eq_zero_symm] at hz)

/-- Two least squares solutions `x`, `x'` of `T x = y` satisfy `T x = T x'`. -/
public theorem IsLeastSquares.apply_eq {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {T : E →L[𝕜] F} {y : F} {x x' : E}
    (h : IsLeastSquares T y x) (h' : IsLeastSquares T y x') : T x = T x' := by
  have hmem : T x - T x' ∈ LinearMap.range T.toLinearMap :=
    Submodule.sub_mem _ ⟨x, rfl⟩ ⟨x', rfl⟩
  have hmem' : T x - T x' ∈ (LinearMap.range T.toLinearMap)ᗮ := by
    have he : T x - T x' = (y - T x') - (y - T x) := by abel
    rw [he]
    exact Submodule.sub_mem _ (isLeastSquares_iff_sub_mem_orthogonal_range.1 h')
      (isLeastSquares_iff_sub_mem_orthogonal_range.1 h)
  rw [← sub_eq_zero]
  exact Submodule.disjoint_def.1
    (Submodule.orthogonal_disjoint (LinearMap.range T.toLinearMap)) _ hmem hmem'

/-- `x` is a minimum norm solution of `T x = y` if and only if `y - T x ∈ Ran(T)ᗮ` and
`x ∈ Ker(T)ᗮ`. -/
public theorem isMinimumNorm_iff {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {T : E →L[𝕜] F} {y : F} {x : E} :
    IsMinimumNorm T y x ↔
      y - T x ∈ T.toLinearMap.rangeᗮ ∧ x ∈ T.toLinearMap.kerᗮ := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨isLeastSquares_iff_sub_mem_orthogonal_range.1 h1, ?_⟩
    rw [Submodule.mem_orthogonal']
    have hx0 : ‖x - (0 : E)‖ = ⨅ w : LinearMap.ker T.toLinearMap, ‖x - w‖ := by
      refine le_antisymm (le_ciInf ?_) ?_
      · rintro ⟨w, hw⟩
        rw [sub_zero]
        refine h2 (x - w) ?_
        rw [isLeastSquares_iff_sub_mem_orthogonal_range]
        have hTw : T (x - w) = T x := by
          have : T w = 0 := hw
          rw [map_sub, this, sub_zero]
        rw [hTw]
        exact isLeastSquares_iff_sub_mem_orthogonal_range.1 h1
      · refine ciInf_le ⟨0, ?_⟩ (⟨0, Submodule.zero_mem _⟩ : LinearMap.ker T.toLinearMap)
        rintro a ⟨b, rfl⟩
        exact norm_nonneg _
    have h3 := (Submodule.norm_eq_iInf_iff_inner_eq_zero _ (Submodule.zero_mem _)).1 hx0
    intro u hu
    have := h3 u hu
    rwa [sub_zero] at this
  · rintro ⟨h1, h2⟩
    refine ⟨isLeastSquares_iff_sub_mem_orthogonal_range.2 h1, ?_⟩
    intro z hz
    have hz' := isLeastSquares_iff_sub_mem_orthogonal_range.1 hz
    have hsub : T x - T z = 0 :=
      sub_eq_zero.2 ((isLeastSquares_iff_sub_mem_orthogonal_range.2 h1).apply_eq hz)
    have hzx : z - x ∈ LinearMap.ker T.toLinearMap := by
      have : T (z - x) = 0 := by
        rw [map_sub]
        rw [sub_eq_zero] at hsub ⊢
        exact hsub.symm
      exact this
    have hinner : ⟪x, z - x⟫_𝕜 = 0 := (Submodule.mem_orthogonal' _ _).1 h2 _ hzx
    have hxz : x + (z - x) = z := by abel
    exact hxz ▸ norm_le_norm_add_of_inner_eq_zero hinner

/-- Being a least squares solution unfolds to its defining inequality. -/
public theorem isLeastSquares_def {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {T : E →L[𝕜] F} {y : F} {x : E} :
    IsLeastSquares T y x ↔ ∀ z : E, ‖T x - y‖ ≤ ‖T z - y‖ := Iff.rfl

/-- A least squares solution `x` satisfies `‖T x - y‖ ≤ ‖T z - y‖` for each `z`. -/
public
theorem IsLeastSquares.norm_le_norm {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {T : E →L[𝕜] F} {y : F} {x : E}
    (h : IsLeastSquares T y x)
    (z : E) : ‖T x - y‖ ≤ ‖T z - y‖ := h z

/-- A minimum norm solution of `T x = y` lies in `Ker(T)ᗮ`. -/
public theorem IsMinimumNorm.mem_orthogonal_ker {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    {T : E →L[𝕜] F} {y : F} {x : E}
    (h : IsMinimumNorm T y x) : x ∈ T.toLinearMap.kerᗮ :=
  (isMinimumNorm_iff.1 h).2

/-- A minimum norm solution `x` of `T x = y` has `y - T x ∈ Ran(T)ᗮ`. -/
public theorem IsMinimumNorm.sub_mem_orthogonal_range {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    {T : E →L[𝕜] F} {y : F} {x : E}
    (h : IsMinimumNorm T y x) : y - T x ∈ T.toLinearMap.rangeᗮ :=
  (isMinimumNorm_iff.1 h).1

end AutoIp
