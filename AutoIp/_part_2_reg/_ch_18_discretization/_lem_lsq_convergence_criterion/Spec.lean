/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_18_discretization._def_lsq_projection
public import AutoIp._part_2_reg._ch_18_discretization._lem_lsq_range_closed
import AutoIp.Auxiliary.FiniteDimensional
import AutoIp._part_1_funcanal._ch_05_weak_convergence._lem_strong_to_weak
import AutoIp._part_1_funcanal._ch_05_weak_convergence._lem_weak_limit_unique
import AutoIp._part_1_funcanal._ch_05_weak_convergence._lem_weak_lsc
import AutoIp._part_1_funcanal._ch_05_weak_convergence._lem_weak_seq_cont
import AutoIp._part_1_funcanal._ch_05_weak_convergence._thm_radon_riesz
import AutoIp._part_1_funcanal._ch_05_weak_convergence._thm_weak_compactness
import AutoIp._part_2_reg._ch_18_discretization._lem_lsq_comparison
import Mathlib.Algebra.Order.Ring.Star

section _lem_lsq_convergence_criterion

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The convergence criterion: for `y ∈ Dom(T†)`, the least-squares projections satisfy
`xₙ → x†` if and only if `limsup ‖xₙ‖ ≤ ‖x†‖`, for nested subspaces `X n` with `dim Xₙ = n`
and `closure(⋃ₙ Xₙ) = X`.

The limsup is taken in `ℝ≥0∞`, so that it is meaningful for an unbounded sequence of norms. -/
public theorem lsq_tendsto_iff (T : E →L[𝕜] F) (X : ℕ → Submodule 𝕜 E)
    [∀ n, (X n).HasOrthogonalProjection] (hmono : Monotone X)
    (hfin : ∀ n, Module.finrank 𝕜 (X n) = n)
    (hdenseX : (⨆ n, X n).topologicalClosure = ⊤)
    {y : F} (hy : y ∈ mpDomain T) :
    Tendsto (fun n => lsqProjection T X y (mem_mpDomain_lsq T X hmono hfin y) n) atTop
        (𝓝 (moorePenrose T ⟨y, hy⟩)) ↔
      limsup (fun n => ‖lsqProjection T X y (mem_mpDomain_lsq T X hmono hfin y) n‖ₑ)
          atTop ≤
        ‖moorePenrose T ⟨y, hy⟩‖ₑ := by
  have hyd : ∀ m, y ∈ mpDomain (T ∘L (X m).starProjection) := mem_mpDomain_lsq T X hmono hfin y
  classical
  have hcomp := norm_apply_lsqProjection_sub_le T X
    (finiteDimensional_of_monotone_finrank hmono hfin) hy
  have hTconv : Tendsto (fun n => ‖T (lsqProjection T X y hyd n) - T (moorePenrose T ⟨y, hy⟩)‖)
      atTop (𝓝 0) := by
    have h0 := tendsto_opNorm_mul_norm_sub_starProjection T X hmono hdenseX hy
    exact squeeze_zero (fun n => norm_nonneg _) hcomp h0
  constructor
  · intro h
    have hn : Tendsto (fun n => ‖lsqProjection T X y hyd n‖ₑ) atTop
        (𝓝 ‖moorePenrose T ⟨y, hy⟩‖ₑ) := by
      simpa only [ofReal_norm] using ENNReal.tendsto_ofReal h.norm
    exact le_of_eq hn.limsup_eq
  · intro hlim
    have hev : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        ‖lsqProjection T X y hyd n‖ ≤ ‖moorePenrose T ⟨y, hy⟩‖ + ε := by
      intro ε hε
      have h1 : ‖moorePenrose T ⟨y, hy⟩‖ₑ
          < ENNReal.ofReal (‖moorePenrose T ⟨y, hy⟩‖ + ε) := by
        rw [← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
        linarith
      have h2 := Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hlim h1)
      filter_upwards [h2] with n hn
      rw [← ofReal_norm] at hn
      have h3 := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hn
      linarith
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ n, ‖lsqProjection T X y hyd n‖ ≤ C := by
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hev 1 one_pos)
      refine ⟨max (‖moorePenrose T ⟨y, hy⟩‖ + 1)
        (((Finset.range N).sup (fun i => ‖lsqProjection T X y hyd i‖₊) : NNReal) : ℝ), fun n => ?_⟩
      rcases le_or_gt N n with h | h
      · exact le_trans (hN n h) (le_max_left _ _)
      · refine le_trans ?_ (le_max_right _ _)
        have hle : ‖lsqProjection T X y hyd n‖₊
            ≤ (Finset.range N).sup (fun i => ‖lsqProjection T X y hyd i‖₊) :=
          Finset.le_sup (f := fun i => ‖lsqProjection T X y hyd i‖₊) (Finset.mem_range.2 h)
        exact_mod_cast hle
    by_contra hcon
    rw [Metric.tendsto_atTop] at hcon
    push Not at hcon
    obtain ⟨ε, hε, hfreq⟩ := hcon
    have hfr : ∃ᶠ n in atTop, ε ≤ dist (lsqProjection T X y hyd n) (moorePenrose T ⟨y, hy⟩) := by
      rw [Filter.frequently_atTop]
      intro N
      obtain ⟨n, hn, hd⟩ := hfreq N
      exact ⟨n, hn, hd⟩
    obtain ⟨φ, hφ, hφprop⟩ := Filter.extraction_of_frequently_atTop hfr
    obtain ⟨ψ, b, hψ, hb⟩ := exists_tendstoWeakly_subseq_of_bounded (𝕜 := 𝕜)
      (fun k => lsqProjection T X y hyd (φ k)) C (fun k => hC _)
    have hχ : StrictMono (fun k => φ (ψ k)) := hφ.comp hψ
    have hχtop : Tendsto (fun k => φ (ψ k)) atTop atTop := hχ.tendsto_atTop
    -- `T b = T x†`: the images converge strongly, and weakly to `T b`.
    have hTb : T b = T (moorePenrose T ⟨y, hy⟩) := by
      have h1 : TendstoWeakly 𝕜
          (fun k => T (lsqProjection T X y hyd (φ (ψ k)))) (T b) := hb.map T
      have h2 : Tendsto (fun k => T (lsqProjection T X y hyd (φ (ψ k)))) atTop
          (𝓝 (T (moorePenrose T ⟨y, hy⟩))) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        exact hTconv.comp hχtop
      exact h1.unique (TendstoWeakly.of_tendsto h2)
    -- `b - x† ∈ Ker T` and `x† ⊥ Ker T`, so Pythagoras applies.
    have hxdperp : moorePenrose T ⟨y, hy⟩ ∈ (LinearMap.ker T.toLinearMap)ᗮ :=
      moorePenrose_mem_orthogonal_ker ⟨_, hy⟩
    have hinner : ⟪b - moorePenrose T ⟨y, hy⟩, moorePenrose T ⟨y, hy⟩⟫_𝕜 = 0 := by
      refine (Submodule.mem_orthogonal _ _).1 hxdperp _ ?_
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, hTb, sub_self]
    have hpyth : ‖b‖ * ‖b‖
        = ‖b - moorePenrose T ⟨y, hy⟩‖ * ‖b - moorePenrose T ⟨y, hy⟩‖
          + ‖moorePenrose T ⟨y, hy⟩‖ * ‖moorePenrose T ⟨y, hy⟩‖ := by
      have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (b - moorePenrose T ⟨y, hy⟩) (moorePenrose T ⟨y, hy⟩) hinner
      simpa using h
    have hbdd_ge : IsBoundedUnder (· ≥ ·) atTop
        (fun k => ‖lsqProjection T X y hyd (φ (ψ k))‖) :=
      ⟨0, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun k => norm_nonneg _)⟩
    have hbdd_le : IsBoundedUnder (· ≤ ·) atTop
        (fun k => ‖lsqProjection T X y hyd (φ (ψ k))‖) :=
      ⟨C, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun k => hC _)⟩
    have hcob_le : IsCoboundedUnder (· ≤ ·) atTop
        (fun k => ‖lsqProjection T X y hyd (φ (ψ k))‖) := by
      refine ⟨0, fun a ha => ?_⟩
      obtain ⟨k, hk⟩ := (Filter.eventually_map.mp ha).exists
      exact le_trans (norm_nonneg _) hk
    have hlimsup : limsup (fun k => ‖lsqProjection T X y hyd (φ (ψ k))‖) atTop
        ≤ ‖moorePenrose T ⟨y, hy⟩‖ := by
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      exact Filter.limsup_le_of_le hcob_le (hχtop.eventually (hev δ hδ))
    -- `‖b‖ ≤ liminf ≤ limsup ≤ ‖x†‖`, and Pythagoras forces `b = x†`.
    have hbnorm : ‖b‖ ≤ ‖moorePenrose T ⟨y, hy⟩‖ :=
      le_trans hb.norm_le_liminf_norm (le_trans (Filter.liminf_le_limsup hbdd_le hbdd_ge) hlimsup)
    have hbeq : b = moorePenrose T ⟨y, hy⟩ := by
      have h1 : ‖b - moorePenrose T ⟨y, hy⟩‖ * ‖b - moorePenrose T ⟨y, hy⟩‖ ≤ 0 := by
        nlinarith [norm_nonneg b, norm_nonneg (moorePenrose T ⟨y, hy⟩)]
      have h2 : ‖b - moorePenrose T ⟨y, hy⟩‖ = 0 := by
        nlinarith [norm_nonneg (b - moorePenrose T ⟨y, hy⟩)]
      rwa [norm_sub_eq_zero_iff] at h2
    -- The norms converge, so Radon--Riesz upgrades to strong convergence.
    have hnormconv : Tendsto (fun k => ‖lsqProjection T X y hyd (φ (ψ k))‖) atTop (𝓝 ‖b‖) := by
      refine tendsto_of_le_liminf_of_limsup_le ?_ ?_ hbdd_le hbdd_ge
      · exact hb.norm_le_liminf_norm
      · rw [hbeq]; exact hlimsup
    have hstrong : Tendsto (fun k => lsqProjection T X y hyd (φ (ψ k))) atTop (𝓝 b) :=
      hb.tendsto_of_tendsto_norm hnormconv
    rw [hbeq, Metric.tendsto_atTop] at hstrong
    obtain ⟨N, hN⟩ := hstrong ε hε
    have h1 := hN N le_rfl
    have h2 := hφprop (ψ N)
    linarith

end AutoIp

end _lem_lsq_convergence_criterion
