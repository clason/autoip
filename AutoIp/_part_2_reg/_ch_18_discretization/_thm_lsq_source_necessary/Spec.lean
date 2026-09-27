/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose_bounded
public import AutoIp._part_2_reg._ch_18_discretization._def_lsq_projection
public import AutoIp._part_2_reg._ch_18_discretization._lem_lsq_range_closed
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import AutoIp.Auxiliary.FiniteDimensional
import AutoIp._part_1_funcanal._ch_05_weak_convergence._thm_weak_compactness
import AutoIp._part_1_funcanal._ch_06_compact_operators._thm_complete_continuity
import AutoIp._part_1_funcanal._ch_06_compact_operators._thm_schauder
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_adjoint
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_domain_dense
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_equations
import AutoIp._part_2_reg._ch_18_discretization._thm_lsq_convergence
import Mathlib.Algebra.Order.Ring.Star

section _thm_lsq_source_necessary

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- For compact `K`, nested subspaces `X n` with `dim Xₙ = n` and `closure(⋃ₙ Xₙ) = X`, and
`y ∈ Dom(K†)` satisfying the hypothesis `limsup ‖(Kₙ†)* xₙ‖ < ∞` of the convergence theorem, the
source condition `x† ∈ Ran(K*)` holds.

The limsup is taken in `ℝ≥0∞`. -/
public theorem moorePenrose_mem_range_adjoint (K : E →L[𝕜] F) (X : ℕ → Submodule 𝕜 E)
    [∀ n, (X n).HasOrthogonalProjection] (hK : IsCompactOperator K) (hmono : Monotone X)
    (hfin : ∀ n, Module.finrank 𝕜 (X n) = n)
    (hdenseX : (⨆ n, X n).topologicalClosure = ⊤)
    {y : F} (hy : y ∈ mpDomain K)
    (hbdd : limsup (fun n =>
      ‖(moorePenroseL (isClosed_range_lsq K X hmono hfin n)).adjoint
        (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n)‖ₑ)
      atTop < ⊤) :
    moorePenrose K ⟨y, hy⟩ ∈ K.adjoint.toLinearMap.range := by
  classical
  have hclosed : ∀ n,
      IsClosed (LinearMap.range (K ∘L (X n).starProjection).toLinearMap : Set F) :=
    isClosed_range_lsq K X hmono hfin
  have hfd : ∀ m, FiniteDimensional 𝕜 (X m) :=
    finiteDimensional_of_monotone_finrank hmono hfin
  have hadj : ∀ n, ContinuousLinearMap.adjoint (K ∘L (X n).starProjection)
      = (X n).starProjection ∘L ContinuousLinearMap.adjoint K := by
    intro n
    rw [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection (X n))]
  have hadjmem : ∀ n (u : F),
      ContinuousLinearMap.adjoint (K ∘L (X n).starProjection) u ∈ X n := by
    intro n u
    rw [hadj n]
    exact (X n).starProjection_apply_mem _
  have hclosed' : ∀ n, IsClosed
      (LinearMap.range (ContinuousLinearMap.adjoint (K ∘L (X n).starProjection)).toLinearMap
        : Set E) := by
    intro n
    have := hfd n
    have : FiniteDimensional 𝕜
        (LinearMap.range
          (ContinuousLinearMap.adjoint (K ∘L (X n).starProjection)).toLinearMap) := by
      refine Submodule.finiteDimensional_of_le (S₂ := X n) ?_
      rintro z ⟨u, rfl⟩
      exact hadjmem n u
    exact Submodule.closed_of_finiteDimensional _
  set w : ℕ → F := fun n =>
    ContinuousLinearMap.adjoint (moorePenroseL (hclosed n)) (lsqProjection K X y
        (mem_mpDomain_lsq K X hmono hfin y) n) with hwdef
  have hrep : ∀ n, ContinuousLinearMap.adjoint (K ∘L (X n).starProjection) (w n)
      = lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n := by
    intro n
    have hyn : y ∈ mpDomain (K ∘L (X n).starProjection) := by
      rw [mpDomain_eq_top_iff.2 (hclosed n)]; trivial
    have hxn : lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n
        ∈ (LinearMap.ker (K ∘L (X n).starProjection).toLinearMap)ᗮ := by
      rw [lsqProjection_def]
      exact moorePenrose_mem_orthogonal_ker ⟨_, hyn⟩
    rw [hwdef]
    simp only
    rw [adjoint_moorePenroseL_apply (hclosed n) (lsqProjection K X y (mem_mpDomain_lsq K X hmono
        hfin y) n)]
    have hmemdom : lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n
        ∈ mpDomain (ContinuousLinearMap.adjoint (K ∘L (X n).starProjection)) := by
      rw [mpDomain_eq_top_iff.2 (hclosed' n)]; trivial
    rw [apply_moorePenrose ⟨_, hmemdom⟩]
    refine Submodule.starProjection_eq_self_iff.2 ?_
    have h2 : (LinearMap.range
        (ContinuousLinearMap.adjoint
          (K ∘L (X n).starProjection)).toLinearMap).topologicalClosure
        = (LinearMap.ker (K ∘L (X n).starProjection).toLinearMap)ᗮ := by
      rw [← Submodule.orthogonal_orthogonal_eq_closure]
      congr 1
      have h3 := (ContinuousLinearMap.adjoint (K ∘L (X n).starProjection)).orthogonal_range
      rwa [ContinuousLinearMap.adjoint_adjoint] at h3
    rw [h2]
    exact hxn
  have hxrep : ∀ n, lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n
      = (X n).starProjection (ContinuousLinearMap.adjoint K (w n)) := by
    intro n
    rw [← hrep n, hadj n]
    rfl
  have hIP : ∀ (n : ℕ) (v : E), ‖v - (X n).starProjection v‖ ≤ ‖v‖ := by
    intro n v
    have h1 : ((X n)ᗮ).starProjection v = v - (X n).starProjection v := by
      rw [Submodule.starProjection_orthogonal]
      simp
    rw [← h1]
    exact Submodule.norm_starProjection_apply_le _ _
  obtain ⟨M, hM0, hMev⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in atTop, ‖w n‖ ≤ M := by
    set L := limsup (fun n => ‖w n‖ₑ) atTop with hL
    have hLne : L ≠ ⊤ := ne_of_lt hbdd
    have hlt : L < L + 1 := ENNReal.lt_add_right hLne one_ne_zero
    have hne : L + 1 ≠ ⊤ := by simp [ENNReal.add_eq_top, hLne]
    refine ⟨(L + 1).toReal, ENNReal.toReal_nonneg, ?_⟩
    filter_upwards [Filter.eventually_lt_of_limsup_lt hlt] with n hn
    rw [← ofReal_norm] at hn
    exact le_of_lt ((ENNReal.ofReal_lt_iff_lt_toReal (norm_nonneg _) hne).1 hn)
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ n, ‖w n‖ ≤ C := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 hMev
    refine ⟨max M (((Finset.range N).sup (fun i => ‖w i‖₊) : NNReal) : ℝ), fun n => ?_⟩
    rcases le_or_gt N n with h | h
    · exact le_trans (hN n h) (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      have hle : ‖w n‖₊ ≤ (Finset.range N).sup (fun i => ‖w i‖₊) :=
        Finset.le_sup (f := fun i => ‖w i‖₊) (Finset.mem_range.2 h)
      exact_mod_cast hle
  obtain ⟨φ, wbar, hφ, hwk⟩ :=
    exists_tendstoWeakly_subseq_of_bounded (𝕜 := 𝕜) w C hC
  have hKadj : IsCompactOperator (ContinuousLinearMap.adjoint K) :=
    (IsCompactOperator.adjoint_iff K).2 hK
  have hstrong : Tendsto (fun k => ContinuousLinearMap.adjoint K (w (φ k))) atTop
      (𝓝 (ContinuousLinearMap.adjoint K wbar)) :=
    hKadj.tendsto_of_tendstoWeakly hwk
  have hconv := lsq_tendsto K X hmono hfin hdenseX hy hbdd
  have hconvs : Tendsto (fun k => lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) (φ
      k)) atTop (𝓝 (moorePenrose K ⟨y, hy⟩)) :=
    hconv.comp hφ.tendsto_atTop
  have hprojself : Tendsto
      (fun k => (X (φ k)).starProjection (ContinuousLinearMap.adjoint K wbar)) atTop
      (𝓝 (ContinuousLinearMap.adjoint K wbar)) := by
    have h := Submodule.starProjection_tendsto_self X hmono
      (ContinuousLinearMap.adjoint K wbar) (by rw [hdenseX])
    exact h.comp hφ.tendsto_atTop
  have hz1 : Tendsto (fun k => ‖ContinuousLinearMap.adjoint K (w (φ k))
      - ContinuousLinearMap.adjoint K wbar‖) atTop (𝓝 0) := by
    rw [← tendsto_iff_norm_sub_tendsto_zero] at *
    exact hstrong
  have hz2 : Tendsto (fun k => ‖ContinuousLinearMap.adjoint K wbar
      - (X (φ k)).starProjection (ContinuousLinearMap.adjoint K wbar)‖) atTop (𝓝 0) := by
    have h := hprojself
    rw [tendsto_iff_norm_sub_tendsto_zero] at h
    refine h.congr fun k => ?_
    rw [norm_sub_rev]
  have hz3 : Tendsto (fun k => ‖lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) (φ k) -
      moorePenrose K ⟨y, hy⟩‖) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero] at hconvs
    exact hconvs
  have hsum : Tendsto (fun k =>
      ‖ContinuousLinearMap.adjoint K (w (φ k)) - ContinuousLinearMap.adjoint K wbar‖
        + ‖ContinuousLinearMap.adjoint K wbar
            - (X (φ k)).starProjection (ContinuousLinearMap.adjoint K wbar)‖
        + ‖lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) (φ k) - moorePenrose K ⟨y,
            hy⟩‖) atTop (𝓝 0) := by
    have := (hz1.add hz2).add hz3
    simpa using this
  have hbound : ∀ k, ‖ContinuousLinearMap.adjoint K (w (φ k)) - moorePenrose K ⟨y, hy⟩‖
      ≤ ‖ContinuousLinearMap.adjoint K (w (φ k)) - ContinuousLinearMap.adjoint K wbar‖
        + ‖ContinuousLinearMap.adjoint K wbar
            - (X (φ k)).starProjection (ContinuousLinearMap.adjoint K wbar)‖
        + ‖lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) (φ k) - moorePenrose K ⟨y,
            hy⟩‖ := by
    intro k
    set n := φ k with hn
    set v : E := ContinuousLinearMap.adjoint K (w n) with hv
    set vb : E := ContinuousLinearMap.adjoint K wbar with hvb
    have hsplit : v - moorePenrose K ⟨y, hy⟩
        = (v - (X n).starProjection v)
          + (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n - moorePenrose K ⟨y,
              hy⟩) := by
      rw [hxrep n]
      abel
    have h1 : ‖v - (X n).starProjection v‖ ≤ ‖v - vb‖ + ‖vb - (X n).starProjection vb‖ := by
      have he : v - (X n).starProjection v
          = ((v - vb) - (X n).starProjection (v - vb))
            + (vb - (X n).starProjection vb) := by
        rw [map_sub]
        abel
      calc ‖v - (X n).starProjection v‖
          ≤ ‖(v - vb) - (X n).starProjection (v - vb)‖ + ‖vb - (X n).starProjection vb‖ := by
            rw [he]; exact norm_add_le _ _
        _ ≤ ‖v - vb‖ + ‖vb - (X n).starProjection vb‖ := by
            gcongr
            exact hIP n (v - vb)
    calc ‖v - moorePenrose K ⟨y, hy⟩‖
        ≤ ‖v - (X n).starProjection v‖ + ‖lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin
            y) n - moorePenrose K ⟨y, hy⟩‖ := by
          rw [hsplit]; exact norm_add_le _ _
      _ ≤ (‖v - vb‖ + ‖vb - (X n).starProjection vb‖)
            + ‖lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n - moorePenrose K ⟨y,
                hy⟩‖ := by gcongr
  have hfinal : Tendsto (fun k => ContinuousLinearMap.adjoint K (w (φ k))) atTop
      (𝓝 (moorePenrose K ⟨y, hy⟩)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun k => norm_nonneg _) hbound hsum
  have heq : ContinuousLinearMap.adjoint K wbar = moorePenrose K ⟨y, hy⟩ :=
    tendsto_nhds_unique hstrong hfinal
  exact ⟨wbar, heq⟩

end AutoIp

end _thm_lsq_source_necessary
