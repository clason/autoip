/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_18_discretization._def_lsq_projection
public import AutoIp._part_2_reg._ch_18_discretization._lem_lsq_range_closed
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_domain_dense

section _lem_lsq_comparison

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The comparison estimate: for `y ∈ Dom(T†)` and every `n`,
`‖T xₙ - T x†‖ ≤ ‖T‖ ‖(Id - Pₙ) x†‖`, where `xₙ` is the least-squares projection.

Only finite dimensionality of each `X n` is assumed; nestedness, `dim Xₙ = n` and density of
the union are not needed. -/
public theorem norm_apply_lsqProjection_sub_le [CompleteSpace F] (T : E →L[𝕜] F)
    (X : ℕ → Submodule 𝕜 E) [∀ n, (X n).HasOrthogonalProjection]
    (hfd : ∀ n, FiniteDimensional 𝕜 (X n))
    {y : F} (hy : y ∈ mpDomain T) (n : ℕ) :
    ‖T (lsqProjection T X y (mem_mpDomain_lsq_of_finiteDimensional T X hfd y) n) -
        T (moorePenrose T ⟨y, hy⟩)‖ ≤
      ‖T‖ * ‖moorePenrose T ⟨y, hy⟩ - (X n).starProjection (moorePenrose T ⟨y, hy⟩)‖ := by
  have hyd : ∀ m, y ∈ mpDomain (T ∘L (X m).starProjection) :=
    mem_mpDomain_lsq_of_finiteDimensional T X hfd y
  classical
  have hres : y - T (moorePenrose T ⟨y, hy⟩) ∈ (LinearMap.range T.toLinearMap)ᗮ :=
    sub_apply_moorePenrose_mem_orthogonal ⟨_, hy⟩
  have := hfd n
  have : FiniteDimensional 𝕜
      (LinearMap.range (T ∘L (X n).starProjection).toLinearMap) := by
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.map T.toLinearMap (X n)) ?_
    rintro z ⟨x, rfl⟩
    exact ⟨(X n).starProjection x, (X n).starProjection_apply_mem x, rfl⟩
  have hclosed : IsClosed
      (LinearMap.range (T ∘L (X n).starProjection).toLinearMap : Set F) :=
    Submodule.closed_of_finiteDimensional _
  have hyn : y ∈ mpDomain (T ∘L (X n).starProjection) := hyd n
  -- `Xₙᗮ ≤ Ker Tₙ`, hence `xₙ ∈ (Ker Tₙ)ᗮ ≤ Xₙᗮᗮ = Xₙ` and `Pₙ xₙ = xₙ`.
  have hkerle : (X n)ᗮ ≤ LinearMap.ker (T ∘L (X n).starProjection).toLinearMap := by
    intro x hx
    have h0 : (X n).starProjection x = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff _).mpr hx
    simp [h0]
  have hxnmem : moorePenrose (T ∘L (X n).starProjection) ⟨y, hyn⟩ ∈ X n := by
    have h1 : moorePenrose (T ∘L (X n).starProjection) ⟨y, hyn⟩ ∈
        (LinearMap.ker (T ∘L (X n).starProjection).toLinearMap)ᗮ :=
      moorePenrose_mem_orthogonal_ker ⟨_, hyn⟩
    have h2 := Submodule.orthogonal_le hkerle h1
    rwa [Submodule.orthogonal_orthogonal] at h2
  have hPxn : (X n).starProjection (moorePenrose (T ∘L (X n).starProjection) ⟨y, hyn⟩)
      = moorePenrose (T ∘L (X n).starProjection) ⟨y, hyn⟩ :=
    Submodule.starProjection_eq_self_iff.2 hxnmem
  -- Pythagoras: every residual splits orthogonally at `T x† = P_R y`.
  have key : ∀ x : E,
      ‖(T ∘L (X n).starProjection) x - y‖ * ‖(T ∘L (X n).starProjection) x - y‖
        = ‖(T ∘L (X n).starProjection) x - T (moorePenrose T ⟨y, hy⟩)‖ *
            ‖(T ∘L (X n).starProjection) x - T (moorePenrose T ⟨y, hy⟩)‖
          + ‖y - T (moorePenrose T ⟨y, hy⟩)‖ * ‖y - T (moorePenrose T ⟨y, hy⟩)‖ := by
    intro x
    have hmemR : (T ∘L (X n).starProjection) x - T (moorePenrose T ⟨y, hy⟩)
        ∈ LinearMap.range T.toLinearMap :=
      Submodule.sub_mem _ ⟨(X n).starProjection x, rfl⟩ ⟨moorePenrose T ⟨y, hy⟩, rfl⟩
    have hin : ⟪(T ∘L (X n).starProjection) x - T (moorePenrose T ⟨y, hy⟩),
        -(y - T (moorePenrose T ⟨y, hy⟩))⟫_𝕜 = 0 := by
      rw [inner_neg_right, (Submodule.mem_orthogonal _ _).1 hres _ hmemR, neg_zero]
    have he : (T ∘L (X n).starProjection) x - y
        = ((T ∘L (X n).starProjection) x - T (moorePenrose T ⟨y, hy⟩))
          + -(y - T (moorePenrose T ⟨y, hy⟩)) := by abel
    rw [he, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hin, norm_neg]
  -- Test the least-squares property of `xₙ` against the competitor `Pₙ x†`.
  have hcmp := (moorePenrose_isMinimumNorm ⟨_, hyn⟩).isLeastSquares
    ((X n).starProjection (moorePenrose T ⟨y, hy⟩))
  have k1 := key (moorePenrose (T ∘L (X n).starProjection) ⟨y, hyn⟩)
  have k2 := key ((X n).starProjection (moorePenrose T ⟨y, hy⟩))
  have hstep :
      ‖(T ∘L (X n).starProjection) (moorePenrose (T ∘L (X n).starProjection) ⟨y, hyn⟩)
          - T (moorePenrose T ⟨y, hy⟩)‖
        ≤ ‖(T ∘L (X n).starProjection) ((X n).starProjection (moorePenrose T ⟨y, hy⟩))
          - T (moorePenrose T ⟨y, hy⟩)‖ := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
    simp only [pow_two]
    nlinarith [hcmp, k1, k2,
      norm_nonneg ((T ∘L (X n).starProjection)
        (moorePenrose (T ∘L (X n).starProjection) ⟨y, hyn⟩) - y),
      norm_nonneg ((T ∘L (X n).starProjection)
        ((X n).starProjection (moorePenrose T ⟨y, hy⟩)) - y)]
  have e1 : (T ∘L (X n).starProjection) (moorePenrose (T ∘L (X n).starProjection) ⟨y, hyn⟩)
      = T (moorePenrose (T ∘L (X n).starProjection) ⟨y, hyn⟩) := by
    simp only [ContinuousLinearMap.comp_apply, hPxn]
  have e2 : (T ∘L (X n).starProjection) ((X n).starProjection (moorePenrose T ⟨y, hy⟩))
      = T ((X n).starProjection (moorePenrose T ⟨y, hy⟩)) := by
    simp only [ContinuousLinearMap.comp_apply,
      Submodule.starProjection_eq_self_iff.2 ((X n).starProjection_apply_mem _)]
  rw [e1, e2] at hstep
  calc ‖T (lsqProjection T X y hyd n) - T (moorePenrose T ⟨y, hy⟩)‖
      = ‖T (moorePenrose (T ∘L (X n).starProjection) ⟨y, hyn⟩) - T (moorePenrose T ⟨y, hy⟩)‖ := by
        rw [lsqProjection_def]
    _ ≤ ‖T ((X n).starProjection (moorePenrose T ⟨y, hy⟩)) - T (moorePenrose T ⟨y, hy⟩)‖ := hstep
    _ = ‖T ((X n).starProjection (moorePenrose T ⟨y, hy⟩) - moorePenrose T ⟨y,
        hy⟩)‖ := by rw [map_sub]
    _ ≤ ‖T‖ * ‖(X n).starProjection (moorePenrose T ⟨y, hy⟩) - moorePenrose T ⟨y,
        hy⟩‖ := T.le_opNorm _
    _ = ‖T‖ * ‖moorePenrose T ⟨y, hy⟩ - (X n).starProjection (moorePenrose T ⟨y, hy⟩)‖ := by
        rw [norm_sub_rev]

/-- The right-hand side `‖T‖ ‖(Id - Pₙ) x†‖` of the comparison estimate tends to `0`, for
nested subspaces `X n` with `closure(⋃ₙ Xₙ) = X` and `y ∈ Dom(T†)`.

The dimensions of the `X n` are not needed. -/
public theorem tendsto_opNorm_mul_norm_sub_starProjection (T : E →L[𝕜] F)
    (X : ℕ → Submodule 𝕜 E) [∀ n, (X n).HasOrthogonalProjection] (hmono : Monotone X)
    (hdenseX : (⨆ n, X n).topologicalClosure = ⊤) {y : F} (hy : y ∈ mpDomain T) :
    Tendsto (fun n => ‖T‖ *
        ‖moorePenrose T ⟨y, hy⟩ - (X n).starProjection (moorePenrose T ⟨y, hy⟩)‖)
      atTop (𝓝 0) := by
  have h := Submodule.starProjection_tendsto_self X hmono (moorePenrose T ⟨y, hy⟩) hdenseX.ge
  have h2 := ((tendsto_const_nhds (x := moorePenrose T ⟨y, hy⟩)).sub h).norm
  simpa using (tendsto_const_nhds (x := ‖T‖)).mul h2

end AutoIp

end _lem_lsq_comparison
