/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
# The zero operator on the line

The spanning conditions of a singular system for the zero operator of `ℝ` with an empty
family of singular vectors.
-/

namespace Witnesses.Zero

/-- The smallest submodule of the line is closed. -/
public theorem topologicalClosure_bot : (⊥ : Submodule ℝ ℝ).topologicalClosure = ⊥ :=
  IsClosed.submodule_topologicalClosure_eq
    (by rw [Submodule.bot_coe]; exact isClosed_singleton)

/-- The closure of the span of an empty family is the smallest submodule. -/
public theorem span_range_eq_bot {ι : Type} [IsEmpty ι] (v : ι → ℝ) :
    (Submodule.span ℝ (Set.range v)).topologicalClosure = ⊥ := by
  rw [Set.range_eq_empty, Submodule.span_empty]
  exact topologicalClosure_bot

/-- The orthogonal complement of the kernel of the zero operator on the line is trivial. -/
public theorem ker_orthogonal_eq_bot :
    (LinearMap.ker ((0 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ))ᗮ = ⊥ := by
  rw [ContinuousLinearMap.toLinearMap_zero, LinearMap.ker_zero,
    Submodule.top_orthogonal_eq_bot]

/-- The closure of the span of an empty family is the orthogonal complement of the kernel of
the zero operator on the line. -/
public theorem span_left {ι : Type} [IsEmpty ι] (v : ι → ℝ) :
    (Submodule.span ℝ (Set.range v)).topologicalClosure =
      (LinearMap.ker ((0 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ))ᗮ := by
  rw [span_range_eq_bot, ker_orthogonal_eq_bot]

/-- The closure of the span of an empty family is the closure of the range of the zero
operator on the line. -/
public theorem span_right {ι : Type} [IsEmpty ι] (u : ι → ℝ) :
    (Submodule.span ℝ (Set.range u)).topologicalClosure =
      (LinearMap.range ((0 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ)).topologicalClosure := by
  rw [span_range_eq_bot, ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero,
    topologicalClosure_bot]

end Witnesses.Zero
