/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The identity of the line

The conditions of a singular system for the identity of `ℝ` with singular vectors all
equal to `1`.
-/

namespace Witnesses.Identity

/-- The identity of the line is not the zero operator. -/
public theorem one_ne_zero' : (1 : ℝ →L[ℝ] ℝ) ≠ 0 := by
  intro h
  exact one_ne_zero (congrArg (fun T : ℝ →L[ℝ] ℝ => T 1) h)

/-- The identity of the line has operator norm one. -/
public theorem norm_one' : ‖(1 : ℝ →L[ℝ] ℝ)‖ = 1 :=
  ContinuousLinearMap.norm_id

/-- A nonempty family with every value `1` spans the line. -/
public theorem span_range_eq_top {ι : Type} [Nonempty ι] (v : ι → ℝ) (hv : ∀ i, v i = 1) :
    Submodule.span ℝ (Set.range v) = ⊤ := by
  have hr : Set.range v = {(1 : ℝ)} := by
    rw [Set.eq_singleton_iff_unique_mem]
    exact ⟨⟨Classical.arbitrary ι, hv _⟩, fun x ⟨i, hi⟩ => hi ▸ hv i⟩
  rw [hr]
  exact Submodule.eq_top_iff'.2 fun x =>
    (mul_one x) ▸ Submodule.smul_mem _ x (Submodule.mem_span_singleton_self _)

/-- The closure of the span of a nonempty family with every value `1` is the orthogonal
complement of the kernel of the identity of the line. -/
public theorem span_left {ι : Type} [Nonempty ι] (v : ι → ℝ) (hv : ∀ i, v i = 1) :
    (Submodule.span ℝ (Set.range v)).topologicalClosure =
      (LinearMap.ker ((1 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ))ᗮ := by
  have hk : LinearMap.ker ((1 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) = ⊥ := LinearMap.ker_id
  rw [span_range_eq_top v hv, hk, Submodule.bot_orthogonal_eq_top]
  exact le_antisymm le_top (Submodule.le_topologicalClosure _)

/-- The closure of the span of a nonempty family with every value `1` is the closure of the
range of the identity of the line. -/
public theorem span_right {ι : Type} [Nonempty ι] (u : ι → ℝ) (hu : ∀ i, u i = 1) :
    (Submodule.span ℝ (Set.range u)).topologicalClosure =
      (LinearMap.range ((1 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ)).topologicalClosure := by
  have hr : LinearMap.range ((1 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) = ⊤ := LinearMap.range_id
  rw [span_range_eq_top u hu, hr]

/-- The identity of the line is its own adjoint. -/
public theorem adjoint_one_apply (x : ℝ) :
    (ContinuousLinearMap.adjoint (1 : ℝ →L[ℝ] ℝ)) x = x := by
  rw [ContinuousLinearMap.one_def, ContinuousLinearMap.adjoint_id]
  rfl

end Witnesses.Identity
