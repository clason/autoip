/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_08_svd._cor_sigma_null.Spec
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Distinct singular vectors have images at least `σ i` apart. -/
private theorem IsSingularSystem.le_norm_map_sub_map_of_ne (hs : IsSingularSystem K σ v u)
    {i j : ι} (hij : i ≠ j) : σ i ≤ ‖K (v i) - K (v j)‖ := by
  classical
  have hexp : K (v i) - K (v j)
      = (RCLike.ofReal (σ i) : 𝕜) • u i - (RCLike.ofReal (σ j) : 𝕜) • u j := by
    rw [hs.map_left i, hs.map_left j]
  have hinner : (inner 𝕜 (u i) (K (v i) - K (v j)) : 𝕜) = (RCLike.ofReal (σ i) : 𝕜) := by
    rw [hexp, inner_sub_right, inner_smul_right, inner_smul_right]
    have h1 : (inner 𝕜 (u i) (u i) : 𝕜) = 1 := by
      simpa using (orthonormal_iff_ite.mp hs.orthonormal_right i i)
    have h2 : (inner 𝕜 (u i) (u j) : 𝕜) = 0 := by
      simpa [hij] using (orthonormal_iff_ite.mp hs.orthonormal_right i j)
    rw [h1, h2]; ring
  have hcs := norm_inner_le_norm (𝕜 := 𝕜) (u i) (K (v i) - K (v j))
  rw [hinner, RCLike.norm_ofReal, abs_of_pos (hs.pos i), hs.orthonormal_right.1 i,
    one_mul] at hcs
  exact hcs

/-- The singular values of a compact operator with infinite-dimensional range get
arbitrarily small. -/
public theorem IsSingularSystem.exists_lt_of_not_finiteDimensional_range
    (hs : IsSingularSystem K σ v u) (hKc : IsCompactOperator K)
    (hinf : ¬ FiniteDimensional 𝕜 K.toLinearMap.range)
    {ε : ℝ} (hε : 0 < ε) : ∃ i, σ i < ε := by
  by_contra hcon
  push Not at hcon
  have hIinf : Infinite ι := hs.infinite_of_not_finiteDimensional_range hinf
  have hcomp : IsCompact (closure (K '' Metric.closedBall (0 : E) 1)) :=
    hKc.isCompact_closure_image_of_bounded Metric.isBounded_closedBall
  obtain ⟨t, ht, htcov⟩ :=
    Metric.totallyBounded_iff.mp hcomp.totallyBounded (ε / 2) (by positivity)
  have hmem : ∀ i : ι, K (v i) ∈ closure (K '' Metric.closedBall (0 : E) 1) := by
    intro i
    refine subset_closure ⟨v i, ?_, rfl⟩
    simp [Metric.mem_closedBall, hs.orthonormal_left.1 i]
  choose f hft hfb using fun i : ι => Set.mem_iUnion₂.mp (htcov (hmem i))
  have hinj : Function.Injective f := by
    intro i j hijf
    by_contra hij
    have h1 : dist (K (v i)) (f i) < ε / 2 := Metric.mem_ball.mp (hfb i)
    have h2 : dist (K (v j)) (f j) < ε / 2 := Metric.mem_ball.mp (hfb j)
    rw [hijf] at h1
    have h3 : ‖K (v i) - K (v j)‖ < ε := by
      have htri := dist_triangle (K (v i)) (f j) (K (v j))
      rw [dist_comm (f j) (K (v j)), dist_eq_norm, dist_eq_norm, dist_eq_norm] at htri
      rw [dist_eq_norm] at h1 h2
      linarith
    linarith [hs.le_norm_map_sub_map_of_ne hij, hcon i]
  have hft' : Finite ↥t := ht.to_subtype
  have : Finite ι := Finite.of_injective (fun i => (⟨f i, hft i⟩ : ↥t))
    (fun i j hij => hinj (by simpa using congrArg Subtype.val hij))
  exact (not_finite ι)
