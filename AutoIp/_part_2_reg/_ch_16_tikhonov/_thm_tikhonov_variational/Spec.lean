/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_16_tikhonov._def_value_functions
import AutoIp._part_2_reg._ch_16_tikhonov._lem_tikhonov_normal

section _thm_tikhonov_variational

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Variational characterisation: for `y ∈ Y` and `α > 0`, `x_α = R_α y` is the unique
minimiser over `X` of the Tikhonov functional `J_α(x) = ½‖Kx - y‖² + (α/2)‖x‖²`, stated as:
`x` minimises `J_α` if and only if `x = R_α y`.

It holds for every `K`, `K = 0` included. -/
public theorem tikhonov_isMinimizer_iff (hs : IsSingularSystem K σ v u)
    {α : Set.Ioi (0 : ℝ)} (y : F) (x : E) :
    (∀ w : E, ((1 : ℝ) / 2) * ‖K x - y‖ ^ 2 + ((α : ℝ) / 2) * ‖x‖ ^ 2 ≤
        ((1 : ℝ) / 2) * ‖K w - y‖ ^ 2 + ((α : ℝ) / 2) * ‖w‖ ^ 2) ↔
      x = spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) α y := by
  have hα : (0 : ℝ) < (α : ℝ) := α.2
  set xa := spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) α y with hxa
  have hnormal := (tikhonov_iff_normal hs y xa).mp rfl
  have hn2 : ContinuousLinearMap.adjoint K (K xa) + (RCLike.ofReal (α : ℝ) : 𝕜) • xa
      = ContinuousLinearMap.adjoint K y := by simpa using hnormal
  have hA2 : ContinuousLinearMap.adjoint K (K xa - y)
      = -((RCLike.ofReal (α : ℝ) : 𝕜) • xa) := by
    rw [map_sub, eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, sub_eq_zero]
    exact hn2
  have key : ∀ w : E, ((1 : ℝ) / 2) * ‖K w - y‖ ^ 2 + ((α : ℝ) / 2) * ‖w‖ ^ 2
      = (((1 : ℝ) / 2) * ‖K xa - y‖ ^ 2 + ((α : ℝ) / 2) * ‖xa‖ ^ 2)
        + (((1 : ℝ) / 2) * ‖K (w - xa)‖ ^ 2 + ((α : ℝ) / 2) * ‖w - xa‖ ^ 2) := by
    intro w
    have hcross : (RCLike.re (inner 𝕜 (K (w - xa)) (K xa - y) : 𝕜))
        = -((α : ℝ) * RCLike.re (inner 𝕜 (w - xa) xa : 𝕜)) := by
      rw [← ContinuousLinearMap.adjoint_inner_right, hA2, inner_neg_right, inner_smul_right]
      simp
    have n1 : ‖K w - y‖ ^ 2 = ‖K (w - xa)‖ ^ 2
        + 2 * RCLike.re (inner 𝕜 (K (w - xa)) (K xa - y) : 𝕜) + ‖K xa - y‖ ^ 2 := by
      have e1 : K w - y = K (w - xa) + (K xa - y) := by rw [map_sub]; abel
      rw [e1]; exact norm_add_sq (𝕜 := 𝕜) _ _
    have n2 : ‖w‖ ^ 2 = ‖w - xa‖ ^ 2
        + 2 * RCLike.re (inner 𝕜 (w - xa) xa : 𝕜) + ‖xa‖ ^ 2 := by
      conv_lhs => rw [show w = (w - xa) + xa by abel]
      exact norm_add_sq (𝕜 := 𝕜) _ _
    rw [n1, n2, hcross]
    ring
  constructor
  · intro hmin
    have h1 := hmin xa
    have h2 := key x
    have h3 : ‖x - xa‖ ^ 2 ≤ 0 := by
      nlinarith [sq_nonneg ‖K (x - xa)‖, norm_nonneg (K (x - xa))]
    have h4 : ‖x - xa‖ = 0 := by nlinarith [norm_nonneg (x - xa)]
    exact sub_eq_zero.mp (norm_eq_zero.mp h4)
  · rintro rfl
    intro w
    rw [key w]
    nlinarith [sq_nonneg ‖K (w - xa)‖, sq_nonneg ‖w - xa‖]

end AutoIp

end _thm_tikhonov_variational
