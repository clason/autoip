/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose_bounded
public import AutoIp._part_2_reg._ch_18_discretization._def_lsq_projection
public import AutoIp._part_2_reg._ch_18_discretization._lem_lsq_range_closed
import AutoIp.Auxiliary.FiniteDimensional
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_adjoint
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_domain_dense
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_equations
import AutoIp._part_2_reg._ch_18_discretization._lem_lsq_comparison
import AutoIp._part_2_reg._ch_18_discretization._lem_lsq_convergence_criterion

section _thm_lsq_convergence

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Convergence of the least-squares projection: for `y ∈ Dom(T†)` with
`limsup ‖(Tₙ†)* xₙ‖ < ∞`, `xₙ → x†`, for nested subspaces `Xₙ` with `dim Xₙ = n` and
`closure(⋃ₙ Xₙ) = X`.

`Tₙ†` is the bounded Moore–Penrose inverse of `Tₙ = T Pₙ`, whose range is closed, being
finite-dimensional, and the limsup is taken in `ℝ≥0∞`. -/
public theorem lsq_tendsto (T : E →L[𝕜] F) (X : ℕ → Submodule 𝕜 E)
    [∀ n, (X n).HasOrthogonalProjection] (hmono : Monotone X)
    (hfin : ∀ n, Module.finrank 𝕜 (X n) = n)
    (hdenseX : (⨆ n, X n).topologicalClosure = ⊤)
    {y : F} (hy : y ∈ mpDomain T)
    (hbdd : limsup (fun n =>
      ‖(moorePenroseL (isClosed_range_lsq T X hmono hfin n)).adjoint
        (lsqProjection T X y (mem_mpDomain_lsq T X hmono hfin y) n)‖ₑ)
      atTop < ⊤) :
    Tendsto (fun n => lsqProjection T X y (mem_mpDomain_lsq T X hmono hfin y) n) atTop
      (𝓝 (moorePenrose T ⟨y, hy⟩)) := by
  have hyd : ∀ m, y ∈ mpDomain (T ∘L (X m).starProjection) := mem_mpDomain_lsq T X hmono hfin y
  classical
  have hclosed : ∀ n,
      IsClosed (LinearMap.range (T ∘L (X n).starProjection).toLinearMap : Set F) :=
    isClosed_range_lsq T X hmono hfin
  rw [lsq_tendsto_iff T X hmono hfin hdenseX hy]
  have hcomp := norm_apply_lsqProjection_sub_le T X
    (finiteDimensional_of_monotone_finrank hmono hfin) hy
  have hdefect : Tendsto
      (fun n => ‖moorePenrose T ⟨y, hy⟩ - (X n).starProjection (moorePenrose T ⟨y,
          hy⟩)‖) atTop (𝓝 0) := by
    have hmemtop : moorePenrose T ⟨y, hy⟩ ∈ (⨆ m, X m).topologicalClosure := by
      rw [hdenseX]; trivial
    have : ((⨆ m, X m).topologicalClosure).HasOrthogonalProjection := by
      rw [hdenseX]; infer_instance
    have h := Submodule.starProjection_tendsto_closure_iSup X hmono (moorePenrose T ⟨y, hy⟩)
    rw [Submodule.starProjection_eq_self_iff.2 hmemtop] at h
    have h2 : Tendsto (fun m => moorePenrose T ⟨y, hy⟩ - (X m).starProjection (moorePenrose T ⟨y,
        hy⟩))
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := moorePenrose T ⟨y, hy⟩) (f := atTop (α := ℕ))).sub h
    simpa using h2.norm
  have hfd : ∀ m, FiniteDimensional 𝕜 (X m) :=
    finiteDimensional_of_monotone_finrank hmono hfin
  have hadj : ∀ n, ContinuousLinearMap.adjoint (T ∘L (X n).starProjection)
      = (X n).starProjection ∘L ContinuousLinearMap.adjoint T := by
    intro n
    rw [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection (X n))]
  have hadjmem : ∀ n (u : F),
      ContinuousLinearMap.adjoint (T ∘L (X n).starProjection) u ∈ X n := by
    intro n u
    rw [hadj n]
    exact (X n).starProjection_apply_mem _
  have hclosed' : ∀ n, IsClosed
      (LinearMap.range (ContinuousLinearMap.adjoint (T ∘L (X n).starProjection)).toLinearMap
        : Set E) := by
    intro n
    have := hfd n
    have : FiniteDimensional 𝕜
        (LinearMap.range
          (ContinuousLinearMap.adjoint (T ∘L (X n).starProjection)).toLinearMap) := by
      refine Submodule.finiteDimensional_of_le (S₂ := X n) ?_
      rintro z ⟨u, rfl⟩
      exact hadjmem n u
    exact Submodule.closed_of_finiteDimensional _
  -- `xₙ = Tₙ* wₙ` with `wₙ = (Tₙ†)* xₙ`.
  have hrep : ∀ n, ContinuousLinearMap.adjoint (T ∘L (X n).starProjection)
      (ContinuousLinearMap.adjoint (moorePenroseL (hclosed n)) (lsqProjection T X y hyd n))
      = lsqProjection T X y hyd n := by
    intro n
    have hyn : y ∈ mpDomain (T ∘L (X n).starProjection) := by
      rw [mpDomain_eq_top_iff.2 (hclosed n)]; trivial
    have hxn : lsqProjection T X y hyd n
        ∈ (LinearMap.ker (T ∘L (X n).starProjection).toLinearMap)ᗮ := by
      rw [lsqProjection_def]
      exact moorePenrose_mem_orthogonal_ker ⟨_, hyn⟩
    rw [adjoint_moorePenroseL_apply (hclosed n) (lsqProjection T X y hyd n)]
    have hmemdom : lsqProjection T X y hyd n
        ∈ mpDomain (ContinuousLinearMap.adjoint (T ∘L (X n).starProjection)) := by
      rw [mpDomain_eq_top_iff.2 (hclosed' n)]; trivial
    rw [apply_moorePenrose ⟨_, hmemdom⟩]
    refine Submodule.starProjection_eq_self_iff.2 ?_
    have h2 : (LinearMap.range
        (ContinuousLinearMap.adjoint (T ∘L (X n).starProjection)).toLinearMap).topologicalClosure
        = (LinearMap.ker (T ∘L (X n).starProjection).toLinearMap)ᗮ := by
      rw [← Submodule.orthogonal_orthogonal_eq_closure]
      congr 1
      have h3 := (ContinuousLinearMap.adjoint (T ∘L (X n).starProjection)).orthogonal_range
      rwa [ContinuousLinearMap.adjoint_adjoint] at h3
    rw [h2]
    exact hxn
  have hPx : ∀ n, (X n).starProjection (lsqProjection T X y hyd n) = lsqProjection T X y hyd n := by
    intro n
    refine Submodule.starProjection_eq_self_iff.2 ?_
    rw [← hrep n]
    exact hadjmem n _
  have hTnbound : ∀ n, ‖(T ∘L (X n).starProjection)
      (lsqProjection T X y hyd n - moorePenrose T ⟨y, hy⟩)‖
      ≤ 2 * ‖T‖ * ‖moorePenrose T ⟨y, hy⟩ - (X n).starProjection (moorePenrose T ⟨y, hy⟩)‖ := by
    intro n
    have h1 : (T ∘L (X n).starProjection) (lsqProjection T X y hyd n - moorePenrose T ⟨y, hy⟩)
        = (T (lsqProjection T X y hyd n) - T (moorePenrose T ⟨y, hy⟩))
          + T (moorePenrose T ⟨y, hy⟩ - (X n).starProjection (moorePenrose T ⟨y, hy⟩)) := by
      simp only [ContinuousLinearMap.comp_apply, map_sub, hPx n]
      abel
    have h2 : ‖T (moorePenrose T ⟨y, hy⟩ - (X n).starProjection (moorePenrose T ⟨y, hy⟩))‖
        ≤ ‖T‖ * ‖moorePenrose T ⟨y, hy⟩ - (X n).starProjection (moorePenrose T ⟨y, hy⟩)‖ :=
      T.le_opNorm _
    calc ‖(T ∘L (X n).starProjection) (lsqProjection T X y hyd n - moorePenrose T ⟨y, hy⟩)‖
        = ‖(T (lsqProjection T X y hyd n) - T (moorePenrose T ⟨y, hy⟩))
            + T (moorePenrose T ⟨y, hy⟩ - (X n).starProjection (moorePenrose T ⟨y,
                hy⟩))‖ := by rw [h1]
      _ ≤ ‖T (lsqProjection T X y hyd n) - T (moorePenrose T ⟨y, hy⟩)‖
            + ‖T (moorePenrose T ⟨y, hy⟩ - (X n).starProjection (moorePenrose T ⟨y, hy⟩))‖ :=
          norm_add_le _ _
      _ ≤ ‖T‖ * ‖moorePenrose T ⟨y, hy⟩ - (X n).starProjection (moorePenrose T ⟨y, hy⟩)‖
            + ‖T‖ * ‖moorePenrose T ⟨y, hy⟩ - (X n).starProjection (moorePenrose T ⟨y, hy⟩)‖ := by
          exact add_le_add (hcomp n) h2
      _ = 2 * ‖T‖ * ‖moorePenrose T ⟨y, hy⟩ - (X n).starProjection (moorePenrose T ⟨y,
          hy⟩)‖ := by ring
  have heps : ∀ n, ‖(inner 𝕜 (lsqProjection T X y hyd n - moorePenrose T ⟨y, hy⟩)
        (lsqProjection T X y hyd n) : 𝕜)‖
      ≤ (2 * ‖T‖ * ‖moorePenrose T ⟨y, hy⟩ - (X n).starProjection (moorePenrose T ⟨y, hy⟩)‖)
        * ‖ContinuousLinearMap.adjoint (moorePenroseL (hclosed n)) (lsqProjection T X y hyd
            n)‖ := by
    intro n
    have hk : (inner 𝕜 (lsqProjection T X y hyd n - moorePenrose T ⟨y, hy⟩)
          (lsqProjection T X y hyd n) : 𝕜)
        = inner 𝕜 ((T ∘L (X n).starProjection)
            (lsqProjection T X y hyd n - moorePenrose T ⟨y, hy⟩))
          (ContinuousLinearMap.adjoint (moorePenroseL (hclosed n)) (lsqProjection T X y hyd
              n)) := by
      conv_rhs => rw [← ContinuousLinearMap.adjoint_inner_right]
      rw [hrep n]
    rw [hk]
    calc ‖(inner 𝕜 ((T ∘L (X n).starProjection)
            (lsqProjection T X y hyd n - moorePenrose T ⟨y, hy⟩))
          (ContinuousLinearMap.adjoint (moorePenroseL (hclosed n))
            (lsqProjection T X y hyd n)) : 𝕜)‖
        ≤ ‖(T ∘L (X n).starProjection) (lsqProjection T X y hyd n - moorePenrose T ⟨y, hy⟩)‖ *
            ‖ContinuousLinearMap.adjoint (moorePenroseL (hclosed n))
              (lsqProjection T X y hyd n)‖ := norm_inner_le_norm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (hTnbound n) (norm_nonneg _)
  have hquad : ∀ n, ‖lsqProjection T X y hyd n‖ * ‖lsqProjection T X y hyd n‖
      ≤ ‖(inner 𝕜 (lsqProjection T X y hyd n - moorePenrose T ⟨y, hy⟩)
            (lsqProjection T X y hyd n) : 𝕜)‖
        + ‖moorePenrose T ⟨y, hy⟩‖ * ‖lsqProjection T X y hyd n‖ := by
    intro n
    have h1 : RCLike.re (inner 𝕜 (lsqProjection T X y hyd n) (lsqProjection T X y hyd n) : 𝕜)
        = RCLike.re (inner 𝕜 (lsqProjection T X y hyd n - moorePenrose T ⟨y, hy⟩)
            (lsqProjection T X y hyd n) : 𝕜)
          + RCLike.re (inner 𝕜 (moorePenrose T ⟨y, hy⟩) (lsqProjection T X y hyd n) : 𝕜) := by
      rw [← map_add, ← inner_add_left]
      congr 2
      abel
    have h2 := RCLike.re_le_norm (inner 𝕜 (lsqProjection T X y hyd n - moorePenrose T ⟨y, hy⟩)
      (lsqProjection T X y hyd n) : 𝕜)
    have h3 : RCLike.re (inner 𝕜 (moorePenrose T ⟨y, hy⟩) (lsqProjection T X y hyd n) : 𝕜)
        ≤ ‖moorePenrose T ⟨y, hy⟩‖ * ‖lsqProjection T X y hyd n‖ :=
      le_trans (RCLike.re_le_norm _) (norm_inner_le_norm _ _)
    have h4 : RCLike.re (inner 𝕜 (lsqProjection T X y hyd n) (lsqProjection T X y hyd n) : 𝕜)
        = ‖lsqProjection T X y hyd n‖ * ‖lsqProjection T X y hyd n‖ :=
      inner_self_eq_norm_mul_norm _
    linarith
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in atTop,
      ‖ContinuousLinearMap.adjoint (moorePenroseL (hclosed n)) (lsqProjection T X y hyd
          n)‖ ≤ M := by
    set L := limsup (fun n =>
      ‖ContinuousLinearMap.adjoint (moorePenroseL (hclosed n)) (lsqProjection T X y hyd n)‖ₑ)
      atTop with hL
    have hLne : L ≠ ⊤ := ne_of_lt hbdd
    have hlt : L < L + 1 := ENNReal.lt_add_right hLne one_ne_zero
    have hne : L + 1 ≠ ⊤ := by
      simp [ENNReal.add_eq_top, hLne]
    refine ⟨(L + 1).toReal, ENNReal.toReal_nonneg, ?_⟩
    filter_upwards [Filter.eventually_lt_of_limsup_lt hlt] with n hn
    rw [← ofReal_norm] at hn
    exact le_of_lt ((ENNReal.ofReal_lt_iff_lt_toReal (norm_nonneg _) hne).1 hn)
  have hfinal : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ‖lsqProjection T X y hyd n‖ ≤ ‖moorePenrose T ⟨y, hy⟩‖ + δ := by
    intro δ hδ
    have h0 : Tendsto (fun n => (2 * ‖T‖ * M) *
        ‖moorePenrose T ⟨y, hy⟩ - (X n).starProjection (moorePenrose T ⟨y, hy⟩)‖) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := 2 * ‖T‖ * M) (f := (atTop : Filter ℕ))).mul hdefect
      simpa using this
    have hsmall := h0.eventually_lt_const (show (0:ℝ) < δ * δ by positivity)
    filter_upwards [hsmall, hM] with n h1 h2
    have hle1 : ‖(inner 𝕜 (lsqProjection T X y hyd n - moorePenrose T ⟨y, hy⟩)
        (lsqProjection T X y hyd n) : 𝕜)‖ < δ * δ := by
      refine lt_of_le_of_lt (le_trans (heps n) ?_) h1
      have hd : (0:ℝ) ≤ 2 * ‖T‖ *
          ‖moorePenrose T ⟨y, hy⟩ - (X n).starProjection (moorePenrose T ⟨y, hy⟩)‖ := by positivity
      calc (2 * ‖T‖ * ‖moorePenrose T ⟨y, hy⟩ - (X n).starProjection (moorePenrose T ⟨y, hy⟩)‖)
            * ‖ContinuousLinearMap.adjoint (moorePenroseL (hclosed n)) (lsqProjection T X y hyd n)‖
          ≤ (2 * ‖T‖ * ‖moorePenrose T ⟨y, hy⟩ - (X n).starProjection (moorePenrose T ⟨y,
              hy⟩)‖) * M :=
            mul_le_mul_of_nonneg_left h2 hd
        _ = (2 * ‖T‖ * M) *
            ‖moorePenrose T ⟨y, hy⟩ - (X n).starProjection (moorePenrose T ⟨y, hy⟩)‖ := by ring
    by_contra hcon
    push Not at hcon
    nlinarith [hquad n, norm_nonneg (moorePenrose T ⟨y, hy⟩), norm_nonneg (lsqProjection T X y
        hyd n)]
  -- The goal is the `ℝ≥0∞` limsup bound of the convergence criterion.
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hev : ∀ᶠ n in atTop, ‖lsqProjection T X y hyd n‖ₑ
      ≤ ‖moorePenrose T ⟨y, hy⟩‖ₑ + (ε : ℝ≥0∞) := by
    filter_upwards [hfinal (ε : ℝ) (by exact_mod_cast hε)] with n hn
    calc ‖lsqProjection T X y hyd n‖ₑ
        = ENNReal.ofReal ‖lsqProjection T X y hyd n‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (‖moorePenrose T ⟨y, hy⟩‖ + (ε : ℝ)) := ENNReal.ofReal_le_ofReal hn
      _ = ‖moorePenrose T ⟨y, hy⟩‖ₑ + (ε : ℝ≥0∞) := by
          rw [ENNReal.ofReal_add (norm_nonneg _) ε.coe_nonneg, ENNReal.ofReal_coe_nnreal,
            ofReal_norm]
  exact Filter.limsup_le_of_le (h := hev)

end AutoIp

end _thm_lsq_convergence
