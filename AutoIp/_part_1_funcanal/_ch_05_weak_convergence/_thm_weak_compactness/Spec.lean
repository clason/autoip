/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_05_weak_convergence._def_weak_conv
public import Mathlib.Analysis.InnerProductSpace.Defs
import AutoIp._part_1_funcanal._ch_01_bounded_operators._prop_ptwise_limit_exists
import Mathlib.Analysis.InnerProductSpace.Dual

section _thm_weak_compactness

open scoped InnerProductSpace Topology
variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [CompleteSpace H]

/-- Every bounded sequence in a Hilbert space has a weakly convergent subsequence: if
‖xₙ‖ ≤ C for all n, there are a strictly increasing φ and a point a with x_{φ(k)} ⇀ a. -/
public theorem exists_tendstoWeakly_subseq_of_bounded
    (x : ℕ → H) (C : ℝ) (hC : ∀ n, ‖x n‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (a : H), StrictMono φ ∧
      TendstoWeakly 𝕜 (fun k => x (φ k)) a := by
  have hproper : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (x 0)) (hC 0)
  -- Step 1: a single subsequence along which `⟪x n, x m⟫` converges for *every* `m`,
  -- obtained from compactness of a countable product of balls rather than by a hand-rolled
  -- diagonal argument.
  set Kb : Set (ℕ → 𝕜) := Set.pi Set.univ (fun m => Metric.closedBall 0 (C * ‖x m‖)) with hKb
  have hKcomp : IsCompact Kb := isCompact_univ_pi fun m => isCompact_closedBall 0 _
  have hymem : ∀ n, (fun m => (inner 𝕜 (x n) (x m) : 𝕜)) ∈ Kb := by
    intro n m _
    simp only [Metric.mem_closedBall, dist_zero_right]
    calc ‖(inner 𝕜 (x n) (x m) : 𝕜)‖ ≤ ‖x n‖ * ‖x m‖ := norm_inner_le_norm _ _
      _ ≤ C * ‖x m‖ := by gcongr; exact hC n
  obtain ⟨c, -, φ, hφ, hconv⟩ := hKcomp.tendsto_subseq hymem
  have hcoord : ∀ m, Filter.Tendsto (fun k => (inner 𝕜 (x (φ k)) (x m) : 𝕜))
      Filter.atTop (nhds (c m)) := by
    intro m
    exact (tendsto_pi_nhds.mp hconv) m
  -- Step 2: the closed span of the sequence, and the total set `range x ∪ X₀ᗮ`.
  set X₀ : Submodule 𝕜 H := (Submodule.span 𝕜 (Set.range x)).topologicalClosure with hX₀
  have hX₀closed : IsClosed ((X₀ : Submodule 𝕜 H) : Set H) :=
    Submodule.isClosed_topologicalClosure _
  have hX₀complete : CompleteSpace (↥X₀) := hX₀closed.completeSpace_coe
  have hxX₀ : ∀ n, x n ∈ X₀ :=
    fun n => Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)
  set M : Set H := Set.range x ∪ ((X₀ᗮ : Submodule 𝕜 H) : Set H) with hM
  have hMdense : Dense ((Submodule.span 𝕜 M : Submodule 𝕜 H) : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.eq_top_iff']
    intro z
    have hsup : X₀ ⊔ X₀ᗮ = ⊤ := Submodule.sup_orthogonal_of_hasOrthogonalProjection
    have h1 : X₀ ≤ (Submodule.span 𝕜 M).topologicalClosure := by
      rw [hX₀]
      refine Submodule.topologicalClosure_mono (Submodule.span_mono ?_)
      exact fun w hw => Set.mem_union_left _ hw
    have h2 : X₀ᗮ ≤ (Submodule.span 𝕜 M).topologicalClosure :=
      le_trans (fun w hw => Submodule.subset_span (Set.mem_union_right _ hw))
        (Submodule.le_topologicalClosure _)
    have : X₀ ⊔ X₀ᗮ ≤ (Submodule.span 𝕜 M).topologicalClosure := sup_le h1 h2
    rw [hsup] at this
    exact this Submodule.mem_top
  -- Step 3: the functionals `⟪x_{φ k}, ·⟫` converge on `M`, uniformly bounded by `C`.
  set L : ℕ → (H →L[𝕜] 𝕜) := fun k => innerSL 𝕜 (x (φ k)) with hL
  have hLnorm : ∀ k, ‖L k‖ ≤ C := by
    intro k
    refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun z => ?_
    calc ‖L k z‖ = ‖(inner 𝕜 (x (φ k)) z : 𝕜)‖ := by simp [hL, coe_innerSL_apply]
      _ ≤ ‖x (φ k)‖ * ‖z‖ := norm_inner_le_norm _ _
      _ ≤ C * ‖z‖ := by gcongr; exact hC _
  have hLM : ∀ z ∈ M, ∃ w : 𝕜, Filter.Tendsto (fun k => L k z) Filter.atTop (nhds w) := by
    rintro z (⟨m, rfl⟩ | hz)
    · exact ⟨c m, hcoord m⟩
    · refine ⟨0, ?_⟩
      have hzero : ∀ k, L k z = 0 := by
        intro k
        exact (Submodule.mem_orthogonal _ _).mp hz _ (hxX₀ (φ k))
      simp [hzero]
  obtain ⟨S, -, hS⟩ :=
    ContinuousLinearMap.exists_tendsto_of_dense_span L C hLnorm M hMdense hLM
  -- Step 4: Fréchet--Riesz turns the limit functional into the weak limit.
  refine ⟨φ, (InnerProductSpace.toDual 𝕜 H).symm S, hφ, ?_⟩
  intro f
  set y : H := (InnerProductSpace.toDual 𝕜 H).symm f with hy
  have hfy : ∀ z : H, f z = (inner 𝕜 y z : 𝕜) := by
    intro z
    rw [hy, InnerProductSpace.toDual_symm_apply]
  have hSa : ∀ z : H, S z = (inner 𝕜 ((InnerProductSpace.toDual 𝕜 H).symm S) z : 𝕜) := by
    intro z
    rw [InnerProductSpace.toDual_symm_apply]
  have hconj := (continuous_star.tendsto (S y)).comp (hS y)
  simp only [hfy]
  have hrw : ∀ k, (inner 𝕜 y (x (φ k)) : 𝕜) = starRingEnd 𝕜 (L k y) := by
    intro k
    simp only [hL, coe_innerSL_apply]
    rw [inner_conj_symm]
  simp only [hrw]
  have hlim : (starRingEnd 𝕜) (S y) = (inner 𝕜 y ((InnerProductSpace.toDual 𝕜 H).symm S) : 𝕜) := by
    rw [hSa y, inner_conj_symm]
  rw [← hlim]
  exact hconj

end _thm_weak_compactness
