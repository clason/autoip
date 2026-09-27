/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose_bounded
public import AutoIp._part_2_reg._ch_18_discretization._def_dual_lsq_projection
public import AutoIp._part_2_reg._ch_18_discretization._lem_dual_lsq_range_closed
import AutoIp._part_2_reg._ch_18_discretization._thm_dual_lsq_convergence

section _thm_dual_lsq_noisy

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Noisy data and an a priori stopping rule: for `y ∈ Dom(T†)`, if `n(δ) → ∞` and
`δ / μ_{n(δ)} → 0` as `δ → 0`, then `x^δ_{n(δ)} := T_{n(δ)}† Q_{n(δ)} y^δ → x†`, uniformly in `y^δ`
with `‖y - y^δ‖ ≤ δ`; the subspaces `Y n` are nested with `dim Yₙ = n` and
`closure(⋃ₙ Yₙ) = Ker(T*)ᗮ`.

The smallest singular value `μₙ` of `Tₙ` enters through the hypothesis `‖Tₙ†‖ = μₙ⁻¹` for `n > 0`,
which it satisfies by the norm formula for the discrete Moore–Penrose inverse, rather than through a
singular system of `Tₙ`. -/
public theorem dualLsq_noisy_convergence (T : E →L[𝕜] F) (Y : ℕ → Submodule 𝕜 F)
    [∀ n, (Y n).HasOrthogonalProjection]
    (hmono : Monotone Y) (hfin : ∀ n, Module.finrank 𝕜 (Y n) = n)
    (hdenseY : (⨆ n, Y n).topologicalClosure =
      (T.adjoint.toLinearMap.ker)ᗮ)
    {μ : ℕ → ℝ} (hμpos : ∀ n, 0 < n → 0 < μ n)
    (hμ : ∀ n, 0 < n → ‖moorePenroseL (isClosed_range_dualLsq T Y hmono hfin n)‖ = (μ n)⁻¹)
    {y : F} (hy : y ∈ mpDomain T) (nd : ℝ → ℕ)
    (hnd : Tendsto (fun δ => (nd δ : ℝ)) (𝓝[>] (0 : ℝ)) atTop)
    (hratio : Tendsto (fun δ => δ / μ (nd δ)) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ ε > (0 : ℝ), ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo (0 : ℝ) δ₀, ∀ z : F, ‖y - z‖ ≤ δ →
      ‖dualLsqProjection T Y z (mem_mpDomain_dualLsq T Y hmono hfin z) (nd
          δ) - moorePenrose T ⟨y, hy⟩‖ < ε := by
  have hclosed : ∀ n,
      IsClosed (LinearMap.range ((Y n).starProjection ∘L T).toLinearMap : Set F) :=
    isClosed_range_dualLsq T Y hmono hfin
  intro ε hε
  -- The propagated data error: `‖Rₙ(y - z)‖ ≤ δ/μₙ`, using `‖Qₙ‖ ≤ 1`.
  have hdata : ∀ n : ℕ, 0 < n → ∀ (z : F) (δ : ℝ), ‖y - z‖ ≤ δ →
      ‖dualLsqProjection T Y z (mem_mpDomain_dualLsq T Y hmono hfin
          z) n - dualLsqProjection T Y y (mem_mpDomain_dualLsq T Y hmono hfin y) n‖ ≤ δ / μ n := by
    intro n hn z δ hz
    have e1 : dualLsqProjection T Y z (mem_mpDomain_dualLsq T Y hmono hfin z) n
        = moorePenroseL (hclosed n) ((Y n).starProjection z) :=
      by rw [dualLsqProjection_def, moorePenroseL_apply]
    have e2 : dualLsqProjection T Y y (mem_mpDomain_dualLsq T Y hmono hfin y) n
        = moorePenroseL (hclosed n) ((Y n).starProjection y) :=
      by rw [dualLsqProjection_def, moorePenroseL_apply]
    have h1 : dualLsqProjection T Y z (mem_mpDomain_dualLsq T Y hmono hfin
        z) n - dualLsqProjection T Y y (mem_mpDomain_dualLsq T Y hmono hfin y) n
        = moorePenroseL (hclosed n) ((Y n).starProjection (z - y)) := by
      rw [e1, e2, ← map_sub, ← map_sub]
    have hQ : ‖(Y n).starProjection (z - y)‖ ≤ ‖z - y‖ :=
      Submodule.norm_starProjection_apply_le _ _
    have hzy : ‖z - y‖ ≤ δ := by rwa [norm_sub_rev]
    have hpos := hμpos n hn
    rw [h1]
    calc ‖moorePenroseL (hclosed n) ((Y n).starProjection (z - y))‖
        ≤ ‖moorePenroseL (hclosed n)‖ * ‖(Y n).starProjection (z - y)‖ :=
          (moorePenroseL (hclosed n)).le_opNorm _
      _ ≤ ‖moorePenroseL (hclosed n)‖ * δ :=
          mul_le_mul_of_nonneg_left (le_trans hQ hzy) (norm_nonneg _)
      _ = (μ n)⁻¹ * δ := by rw [hμ n hn]
      _ = δ / μ n := by rw [inv_mul_eq_div]
  -- The approximation error.
  have hconv := dualLsq_tendsto T Y hmono hfin hdenseY hy
  rw [Metric.tendsto_atTop] at hconv
  obtain ⟨N, hN⟩ := hconv (ε / 2) (by linarith)
  have hev1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (N : ℝ) ≤ (nd δ : ℝ) := hnd.eventually_ge_atTop _
  have hev2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ / μ (nd δ) < ε / 2 :=
    hratio.eventually_lt_const (by linarith)
  have hev3 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (1 : ℝ) ≤ (nd δ : ℝ) := hnd.eventually_ge_atTop _
  obtain ⟨δ₀, hδ₀, hall⟩ :=
    (nhdsGT_basis (0 : ℝ)).eventually_iff.1 (hev1.and (hev2.and hev3))
  refine ⟨δ₀, hδ₀, fun δ hδ z hz => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hall hδ
  have hn0 : 0 < nd δ := by
    have : 1 ≤ nd δ := by exact_mod_cast h3
    omega
  have hNle : N ≤ nd δ := by exact_mod_cast h1
  have htri := norm_sub_le_norm_sub_add_norm_sub (dualLsqProjection T Y z (mem_mpDomain_dualLsq T
      Y hmono hfin z) (nd δ))
    (dualLsqProjection T Y y (mem_mpDomain_dualLsq T Y hmono hfin y) (nd δ)) (moorePenrose T ⟨y,
        hy⟩)
  have hA := hdata (nd δ) hn0 z δ hz
  have hB : ‖dualLsqProjection T Y y (mem_mpDomain_dualLsq T Y hmono hfin y) (nd
      δ) - moorePenrose T ⟨y, hy⟩‖ < ε / 2 := by
    have := hN (nd δ) hNle
    rwa [dist_eq_norm] at this
  linarith

end AutoIp

end _thm_dual_lsq_noisy
