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
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_adjoint
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_domain_dense
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_equations
import AutoIp._part_2_reg._ch_18_discretization._thm_lsq_source_necessary
import Mathlib.Algebra.Order.Ring.Star

section _thm_lsq_rate

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Rate for the least-squares projection: for compact `K`, nested subspaces `Xₙ` with
`dim Xₙ = n` and `closure(⋃ₙ Xₙ) = X`, and `y ∈ Dom(K†)` satisfying the hypothesis
`limsup ‖(Kₙ†)* xₙ‖ < ∞` of the convergence theorem, there is `C > 0` with
`‖xₙ - x†‖ ≤ C ‖(Id - Pₙ) K*‖` for all `n`.

The limsup is taken in `ℝ≥0∞`. -/
public theorem norm_lsqProjection_sub_le (K : E →L[𝕜] F) (X : ℕ → Submodule 𝕜 E)
    [∀ n, (X n).HasOrthogonalProjection] (hK : IsCompactOperator K) (hmono : Monotone X)
    (hfin : ∀ n, Module.finrank 𝕜 (X n) = n)
    (hdenseX : (⨆ n, X n).topologicalClosure = ⊤)
    {y : F} (hy : y ∈ mpDomain K)
    (hbdd : limsup (fun n =>
      ‖(moorePenroseL (isClosed_range_lsq K X hmono hfin n)).adjoint
        (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n)‖ₑ)
      atTop < ⊤) :
    ∃ C > (0 : ℝ), ∀ n, ‖lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin
        y) n - moorePenrose K ⟨y, hy⟩‖ ≤
      C * ‖(ContinuousLinearMap.id 𝕜 E - (X n).starProjection) ∘L
        K.adjoint‖ := by
  classical
  have hclosed : ∀ n,
      IsClosed (LinearMap.range (K ∘L (X n).starProjection).toLinearMap : Set F) :=
    isClosed_range_lsq K X hmono hfin
  obtain ⟨w, hw⟩ := moorePenrose_mem_range_adjoint K X hK hmono hfin hdenseX hy hbdd
  have hwx : moorePenrose K ⟨y, hy⟩ = ContinuousLinearMap.adjoint K w := hw.symm
  -- The representation `xₙ = Kₙ* wₙ` with `wₙ = (Kₙ†)* xₙ`.
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
  have hfd : ∀ m, FiniteDimensional 𝕜 (X m) :=
    finiteDimensional_of_monotone_finrank hmono hfin
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
  set wn : ℕ → F := fun n =>
    ContinuousLinearMap.adjoint (moorePenroseL (hclosed n)) (lsqProjection K X y
        (mem_mpDomain_lsq K X hmono hfin y) n) with hwndef
  have hrep : ∀ n, ContinuousLinearMap.adjoint (K ∘L (X n).starProjection) (wn n)
      = lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n := by
    intro n
    have hyn : y ∈ mpDomain (K ∘L (X n).starProjection) := by
      rw [mpDomain_eq_top_iff.2 (hclosed n)]; trivial
    have hxn : lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n
        ∈ (LinearMap.ker (K ∘L (X n).starProjection).toLinearMap)ᗮ := by
      rw [lsqProjection_def]
      exact moorePenrose_mem_orthogonal_ker ⟨_, hyn⟩
    rw [hwndef]
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
  have hPx : ∀ n, (X n).starProjection (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y)
      n) = lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n := by
    intro n
    refine Submodule.starProjection_eq_self_iff.2 ?_
    rw [← hrep n]
    exact hadjmem n _
  obtain ⟨M, hM0, hMev⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in atTop, ‖wn n‖ ≤ M := by
    set L := limsup (fun n => ‖wn n‖ₑ) atTop with hL
    have hLne : L ≠ ⊤ := ne_of_lt hbdd
    have hlt : L < L + 1 := ENNReal.lt_add_right hLne one_ne_zero
    have hne : L + 1 ≠ ⊤ := by simp [ENNReal.add_eq_top, hLne]
    refine ⟨(L + 1).toReal, ENNReal.toReal_nonneg, ?_⟩
    filter_upwards [Filter.eventually_lt_of_limsup_lt hlt] with n hn
    rw [← ofReal_norm] at hn
    exact le_of_lt ((ENNReal.ofReal_lt_iff_lt_toReal (norm_nonneg _) hne).1 hn)
  obtain ⟨C₁, hC₁0, hC₁⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖wn n‖ ≤ C := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 hMev
    refine ⟨max M (((Finset.range N).sup (fun i => ‖wn i‖₊) : NNReal) : ℝ),
      le_trans hM0 (le_max_left _ _), fun n => ?_⟩
    rcases le_or_gt N n with h | h
    · exact le_trans (hN n h) (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      have hle : ‖wn n‖₊ ≤ (Finset.range N).sup (fun i => ‖wn i‖₊) :=
        Finset.le_sup (f := fun i => ‖wn i‖₊) (Finset.mem_range.2 h)
      exact_mod_cast hle
  have hres : y - K (moorePenrose K ⟨y, hy⟩) ∈ (LinearMap.range K.toLinearMap)ᗮ :=
    sub_apply_moorePenrose_mem_orthogonal ⟨_, hy⟩
  have hsharp : ∀ n, ‖K (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y)
      n) - K (moorePenrose K ⟨y, hy⟩)‖
      ≤ ‖K (moorePenrose K ⟨y, hy⟩ - (X n).starProjection (moorePenrose K ⟨y, hy⟩))‖ := by
    intro n
    have hyn : y ∈ mpDomain (K ∘L (X n).starProjection) := by
      rw [mpDomain_eq_top_iff.2 (hclosed n)]; trivial
    have key : ∀ x : E,
        ‖(K ∘L (X n).starProjection) x - y‖ * ‖(K ∘L (X n).starProjection) x - y‖
          = ‖(K ∘L (X n).starProjection) x - K (moorePenrose K ⟨y, hy⟩)‖ *
              ‖(K ∘L (X n).starProjection) x - K (moorePenrose K ⟨y, hy⟩)‖
            + ‖y - K (moorePenrose K ⟨y, hy⟩)‖ * ‖y - K (moorePenrose K ⟨y, hy⟩)‖ := by
      intro x
      have hmemR : (K ∘L (X n).starProjection) x - K (moorePenrose K ⟨y, hy⟩)
          ∈ LinearMap.range K.toLinearMap :=
        Submodule.sub_mem _ ⟨(X n).starProjection x, rfl⟩ ⟨moorePenrose K ⟨y, hy⟩, rfl⟩
      have hin : ⟪(K ∘L (X n).starProjection) x - K (moorePenrose K ⟨y, hy⟩),
          -(y - K (moorePenrose K ⟨y, hy⟩))⟫_𝕜 = 0 := by
        rw [inner_neg_right, (Submodule.mem_orthogonal _ _).1 hres _ hmemR, neg_zero]
      have he : (K ∘L (X n).starProjection) x - y
          = ((K ∘L (X n).starProjection) x - K (moorePenrose K ⟨y, hy⟩))
            + -(y - K (moorePenrose K ⟨y, hy⟩)) := by abel
      rw [he, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hin, norm_neg]
    have hcmp := (moorePenrose_isMinimumNorm ⟨_, hyn⟩).isLeastSquares
      ((X n).starProjection (moorePenrose K ⟨y, hy⟩))
    have k1 := key (moorePenrose (K ∘L (X n).starProjection) ⟨y, (mem_mpDomain_lsq K X hmono hfin
        y n)⟩)
    have k2 := key ((X n).starProjection (moorePenrose K ⟨y, hy⟩))
    have hstep :
        ‖(K ∘L (X n).starProjection) (moorePenrose (K ∘L (X n).starProjection) ⟨y,
            (mem_mpDomain_lsq K X hmono hfin y n)⟩)
            - K (moorePenrose K ⟨y, hy⟩)‖
          ≤ ‖(K ∘L (X n).starProjection) ((X n).starProjection (moorePenrose K ⟨y, hy⟩))
            - K (moorePenrose K ⟨y, hy⟩)‖ := by
      refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
      simp only [pow_two]
      nlinarith [hcmp, k1, k2,
        norm_nonneg ((K ∘L (X n).starProjection)
          (moorePenrose (K ∘L (X n).starProjection) ⟨y, (mem_mpDomain_lsq K X hmono hfin y
              n)⟩) - y),
        norm_nonneg ((K ∘L (X n).starProjection)
          ((X n).starProjection (moorePenrose K ⟨y, hy⟩)) - y)]
    have e1 : (K ∘L (X n).starProjection) (moorePenrose (K ∘L (X n).starProjection) ⟨y,
        (mem_mpDomain_lsq K X hmono hfin y n)⟩)
        = K (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n) := by
      have hPxn : (X n).starProjection (moorePenrose (K ∘L (X n).starProjection) ⟨y,
          (mem_mpDomain_lsq K X hmono hfin y n)⟩)
          = lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n := by
        rw [← lsqProjection_def]; exact hPx n
      simp only [ContinuousLinearMap.comp_apply, hPxn]
    have e2 : (K ∘L (X n).starProjection) ((X n).starProjection (moorePenrose K ⟨y, hy⟩))
        = K ((X n).starProjection (moorePenrose K ⟨y, hy⟩)) := by
      simp only [ContinuousLinearMap.comp_apply,
        Submodule.starProjection_eq_self_iff.2 ((X n).starProjection_apply_mem _)]
    rw [e1, e2] at hstep
    refine le_trans hstep (le_of_eq ?_)
    have he : K ((X n).starProjection (moorePenrose K ⟨y, hy⟩)) - K (moorePenrose K ⟨y, hy⟩)
        = -(K (moorePenrose K ⟨y, hy⟩ - (X n).starProjection (moorePenrose K ⟨y, hy⟩))) := by
      rw [map_sub]; abel
    rw [he, norm_neg]
  have hcross : ∀ n, ‖(inner 𝕜 (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n -
      moorePenrose K ⟨y, hy⟩)
        (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n) : 𝕜)‖
      ≤ 2 * ‖K (moorePenrose K ⟨y, hy⟩ - (X n).starProjection (moorePenrose K ⟨y, hy⟩))‖ * C₁ := by
    intro n
    have hk : (inner 𝕜 (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n - moorePenrose
        K ⟨y, hy⟩)
          (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n) : 𝕜)
        = inner 𝕜 ((K ∘L (X n).starProjection)
            (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n - moorePenrose K ⟨y,
                hy⟩)) (wn n) := by
      conv_rhs => rw [← ContinuousLinearMap.adjoint_inner_right]
      rw [hrep n]
    have hsplit : (K ∘L (X n).starProjection)
        (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n - moorePenrose K ⟨y, hy⟩)
        = (K (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n) - K (moorePenrose K ⟨y,
            hy⟩))
          + K (moorePenrose K ⟨y, hy⟩ - (X n).starProjection (moorePenrose K ⟨y, hy⟩)) := by
      simp only [ContinuousLinearMap.comp_apply, map_sub, hPx n]
      abel
    have hb : ‖(K ∘L (X n).starProjection) (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin
        y) n - moorePenrose K ⟨y, hy⟩)‖
        ≤ 2 * ‖K (moorePenrose K ⟨y, hy⟩ - (X n).starProjection (moorePenrose K ⟨y, hy⟩))‖ := by
      rw [hsplit]
      calc ‖(K (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n) - K (moorePenrose K
          ⟨y, hy⟩))
              + K (moorePenrose K ⟨y, hy⟩ - (X n).starProjection (moorePenrose K ⟨y, hy⟩))‖
          ≤ ‖K (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n) - K (moorePenrose K
              ⟨y, hy⟩)‖
              + ‖K (moorePenrose K ⟨y, hy⟩ - (X n).starProjection (moorePenrose K ⟨y, hy⟩))‖ :=
            norm_add_le _ _
        _ ≤ ‖K (moorePenrose K ⟨y, hy⟩ - (X n).starProjection (moorePenrose K ⟨y, hy⟩))‖
              + ‖K (moorePenrose K ⟨y, hy⟩ - (X n).starProjection (moorePenrose K ⟨y, hy⟩))‖ := by
            gcongr
            exact hsharp n
        _ = 2 * ‖K (moorePenrose K ⟨y, hy⟩ - (X n).starProjection (moorePenrose K ⟨y,
            hy⟩))‖ := by ring
    rw [hk]
    calc ‖(inner 𝕜 ((K ∘L (X n).starProjection)
            (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n - moorePenrose K ⟨y,
                hy⟩)) (wn n) : 𝕜)‖
        ≤ ‖(K ∘L (X n).starProjection) (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n
            - moorePenrose K ⟨y, hy⟩)‖ *
            ‖wn n‖ := norm_inner_le_norm _ _
      _ ≤ (2 * ‖K (moorePenrose K ⟨y, hy⟩ - (X n).starProjection (moorePenrose K ⟨y,
          hy⟩))‖) * C₁ := by
          exact mul_le_mul hb (hC₁ n) (norm_nonneg _) (by positivity)
  have hcross2 : ∀ n, ‖(inner 𝕜 (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n -
      moorePenrose K ⟨y, hy⟩)
        (moorePenrose K ⟨y, hy⟩) : 𝕜)‖
      ≤ ‖K (moorePenrose K ⟨y, hy⟩ - (X n).starProjection (moorePenrose K ⟨y, hy⟩))‖ * ‖w‖ := by
    intro n
    have hk : (inner 𝕜 (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n - moorePenrose
        K ⟨y, hy⟩)
          (moorePenrose K ⟨y, hy⟩) : 𝕜)
        = inner 𝕜 (K (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n) - K
            (moorePenrose K ⟨y, hy⟩)) w := by
      rw [hwx]
      conv_rhs => rw [← map_sub]
      rw [← ContinuousLinearMap.adjoint_inner_right]
    rw [hk]
    calc ‖(inner 𝕜 (K (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n) - K
        (moorePenrose K ⟨y, hy⟩)) w : 𝕜)‖
        ≤ ‖K (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n) - K (moorePenrose K ⟨y,
            hy⟩)‖ * ‖w‖ :=
          norm_inner_le_norm _ _
      _ ≤ ‖K (moorePenrose K ⟨y, hy⟩ - (X n).starProjection (moorePenrose K ⟨y, hy⟩))‖ * ‖w‖ := by
          gcongr
          exact hsharp n
  have hdefect : ∀ n, ‖K (moorePenrose K ⟨y, hy⟩ - (X n).starProjection (moorePenrose K ⟨y, hy⟩))‖
      ≤ ‖(ContinuousLinearMap.id 𝕜 E - (X n).starProjection) ∘L
          ContinuousLinearMap.adjoint K‖ ^ 2 * ‖w‖ := by
    intro n
    set A : E →L[𝕜] E := ContinuousLinearMap.id 𝕜 E - (X n).starProjection with hAdef
    have hAeq : A = ((X n)ᗮ).starProjection := by
      rw [hAdef]; exact (Submodule.starProjection_orthogonal (X n)).symm
    have hAmem : ∀ x : E, A x ∈ (X n)ᗮ := by
      intro x; rw [hAeq]; exact ((X n)ᗮ).starProjection_apply_mem x
    have hAid : ∀ x : E, x ∈ (X n)ᗮ → A x = x := by
      intro x hx; rw [hAeq]; exact Submodule.starProjection_eq_self_iff.2 hx
    have hPsa : ContinuousLinearMap.adjoint ((X n).starProjection) = (X n).starProjection :=
      ContinuousLinearMap.isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection (X n))
    have hAsa : ContinuousLinearMap.adjoint A = A := by
      rw [hAdef, map_sub, ContinuousLinearMap.adjoint_id, hPsa]
    have hnormeq : ‖A ∘L ContinuousLinearMap.adjoint K‖ = ‖K ∘L A‖ := by
      have hcomp : ContinuousLinearMap.adjoint (K ∘L A)
          = A ∘L ContinuousLinearMap.adjoint K := by
        rw [ContinuousLinearMap.adjoint_comp, hAsa]
      rw [← hcomp]
      exact LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint (K ∘L A)
    have hxA : moorePenrose K ⟨y, hy⟩ - (X n).starProjection (moorePenrose K ⟨y, hy⟩)
        = A (ContinuousLinearMap.adjoint K w) := by
      rw [hAdef, hwx]
      simp
    have hidem : A (A (ContinuousLinearMap.adjoint K w))
        = A (ContinuousLinearMap.adjoint K w) := hAid _ (hAmem _)
    have h1 : ‖K (A (ContinuousLinearMap.adjoint K w))‖
        ≤ ‖K ∘L A‖ * ‖A (ContinuousLinearMap.adjoint K w)‖ := by
      conv_lhs => rw [← hidem]
      exact (K ∘L A).le_opNorm _
    have h2 : ‖A (ContinuousLinearMap.adjoint K w)‖
        ≤ ‖A ∘L ContinuousLinearMap.adjoint K‖ * ‖w‖ :=
      (A ∘L ContinuousLinearMap.adjoint K).le_opNorm w
    rw [hxA]
    calc ‖K (A (ContinuousLinearMap.adjoint K w))‖
        ≤ ‖K ∘L A‖ * ‖A (ContinuousLinearMap.adjoint K w)‖ := h1
      _ ≤ ‖K ∘L A‖ * (‖A ∘L ContinuousLinearMap.adjoint K‖ * ‖w‖) := by
          gcongr
      _ = ‖A ∘L ContinuousLinearMap.adjoint K‖ ^ 2 * ‖w‖ := by
          rw [hnormeq]; ring
  refine ⟨Real.sqrt ((2 * C₁ + ‖w‖) * ‖w‖) + 1, by positivity, fun n => ?_⟩
  set A : E →L[𝕜] E := ContinuousLinearMap.id 𝕜 E - (X n).starProjection with hAdef
  set d : ℝ := ‖K (moorePenrose K ⟨y, hy⟩ - (X n).starProjection (moorePenrose K ⟨y, hy⟩))‖ with hd
  set a : ℝ := ‖lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n - moorePenrose K ⟨y,
      hy⟩‖ with ha
  set b : ℝ := ‖A ∘L ContinuousLinearMap.adjoint K‖ with hb
  have hsq : a * a ≤ (2 * C₁ + ‖w‖) * d := by
    have h1 : RCLike.re (inner 𝕜 (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n -
        moorePenrose K ⟨y, hy⟩)
        (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n - moorePenrose K ⟨y, hy⟩) : 𝕜)
        = RCLike.re (inner 𝕜 (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n -
            moorePenrose K ⟨y, hy⟩)
            (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n) : 𝕜)
          - RCLike.re (inner 𝕜 (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n -
              moorePenrose K ⟨y, hy⟩)
            (moorePenrose K ⟨y, hy⟩) : 𝕜) := by
      rw [← map_sub, ← inner_sub_right]
    have h2 : RCLike.re (inner 𝕜 (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n -
        moorePenrose K ⟨y, hy⟩)
        (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n - moorePenrose K ⟨y,
            hy⟩) : 𝕜) = a * a :=
      inner_self_eq_norm_mul_norm _
    have h3 := RCLike.re_le_norm (inner 𝕜 (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin
        y) n - moorePenrose K ⟨y, hy⟩)
      (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n) : 𝕜)
    have h4 : -RCLike.re (inner 𝕜 (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n -
        moorePenrose K ⟨y, hy⟩)
        (moorePenrose K ⟨y, hy⟩) : 𝕜)
        ≤ ‖(inner 𝕜 (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin y) n - moorePenrose K
            ⟨y, hy⟩)
            (moorePenrose K ⟨y, hy⟩) : 𝕜)‖ := by
      have := RCLike.re_le_norm (-(inner 𝕜 (lsqProjection K X y (mem_mpDomain_lsq K X hmono hfin
          y) n - moorePenrose K ⟨y, hy⟩)
        (moorePenrose K ⟨y, hy⟩) : 𝕜))
      simpa using this
    have h5 := hcross n
    have h6 := hcross2 n
    nlinarith [h1, h2, h3, h4, h5, h6]
  have hd' : d ≤ b ^ 2 * ‖w‖ := hdefect n
  have hbnn : (0:ℝ) ≤ b := norm_nonneg _
  have hann : (0:ℝ) ≤ a := norm_nonneg _
  have hwnn : (0:ℝ) ≤ ‖w‖ := norm_nonneg _
  have hcnn : (0:ℝ) ≤ (2 * C₁ + ‖w‖) := by positivity
  have hkey : a * a ≤ ((2 * C₁ + ‖w‖) * ‖w‖) * (b * b) := by
    have := mul_le_mul_of_nonneg_left hd' hcnn
    nlinarith
  have hsqrt : Real.sqrt ((2 * C₁ + ‖w‖) * ‖w‖) ^ 2 = (2 * C₁ + ‖w‖) * ‖w‖ :=
    Real.sq_sqrt (by positivity)
  have hfinal : a ≤ (Real.sqrt ((2 * C₁ + ‖w‖) * ‖w‖) + 1) * b := by
    have hs0 : (0:ℝ) ≤ Real.sqrt ((2 * C₁ + ‖w‖) * ‖w‖) := Real.sqrt_nonneg _
    nlinarith [hkey, hsqrt, hbnn, hann, hs0, mul_nonneg hs0 hbnn]
  exact hfinal

end AutoIp

end _thm_lsq_rate
