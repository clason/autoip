/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import AutoIp._part_1_funcanal._ch_01_bounded_operators._thm_closed_range
import AutoIp._part_1_funcanal._ch_01_bounded_operators._thm_riesz_ball

section _thm_compact_range_not_closed

open scoped Topology
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Let `E`, `F` be Banach spaces and K ∈ 𝒦(E, F) with dim 𝓡(K) = ∞. Then 𝓡(K) is not
closed in `F`. -/
public theorem IsCompactOperator.not_isClosed_range_of_not_finiteDimensional [CompleteSpace E]
    [CompleteSpace F] {K : E →L[𝕜] F} (hK : IsCompactOperator K)
    (h : ¬ FiniteDimensional 𝕜 K.toLinearMap.range) :
    ¬ IsClosed (K.toLinearMap.range : Set F) := by
  intro hclosed
  -- Closed range makes `K` bounded below on `E ⧸ N`.
  obtain ⟨c, hc, hbound⟩ :=
    (ContinuousLinearMap.isClosed_range_iff_exists_mul_norm_quotient_le K).mp hclosed
  set N := LinearMap.ker K.toLinearMap with hN
  -- Every `y` in the unit ball of the range is `K w` for a representative of norm `< 2/c`:
  -- the quotient bound caps `‖mk x‖` by `1/c`, and a near-minimal representative costs
  -- another `1/c`.
  have hkey : (LinearMap.range K.toLinearMap : Set F) ∩ Metric.closedBall (0 : F) 1 ⊆
      K '' Metric.closedBall (0 : E) (2 / c) := by
    rintro y ⟨⟨x, rfl⟩, hy⟩
    have hy1 : ‖K x‖ ≤ 1 := by simpa using hy
    have h1 : ‖(Submodule.Quotient.mk x : E ⧸ N)‖ ≤ 1 / c := by
      rw [le_div_iff₀ hc, mul_comm]
      exact (hbound x).trans hy1
    obtain ⟨w, hw, hwlt⟩ :=
      Submodule.Quotient.norm_mk_lt (Submodule.Quotient.mk x : E ⧸ N)
        (show (0 : ℝ) < 1 / c by positivity)
    refine ⟨w, ?_, ?_⟩
    · have : ‖w‖ < 2 / c := by
        refine hwlt.trans_le ?_
        have : (1 : ℝ) / c + 1 / c = 2 / c := by ring
        linarith [h1]
      simpa using this.le
    · have hmem : w - x ∈ N := (Submodule.Quotient.eq N).mp hw
      have : K w - K x = 0 := by
        simpa [hN, LinearMap.mem_ker, map_sub] using hmem
      simpa [sub_eq_zero] using this
  -- `closure (K '' ball)` is compact, and the unit ball of the range is a closed subset
  -- of it, hence compact.
  have hScomp : IsCompact (closure (K '' Metric.closedBall (0 : E) (2 / c))) :=
    hK.isCompact_closure_image_of_bounded Metric.isBounded_closedBall
  have hInter : IsCompact
      ((LinearMap.range K.toLinearMap : Set F) ∩ Metric.closedBall (0 : F) 1) :=
    hScomp.of_isClosed_subset (hclosed.inter Metric.isClosed_closedBall)
      (hkey.trans subset_closure)
  -- Transferred to the subspace itself, that says the unit ball of `R (K)` is compact, so
  -- Riesz's theorem on the compact unit ball makes `R (K)` finite-dimensional -- the
  -- contradiction.
  have hball : IsCompact
      (Metric.closedBall (0 : (LinearMap.range K.toLinearMap : Submodule 𝕜 F)) 1) := by
    have hset : (Subtype.val '' Metric.closedBall (0 : LinearMap.range K.toLinearMap) 1)
        = (LinearMap.range K.toLinearMap : Set F) ∩ Metric.closedBall (0 : F) 1 := by
      ext y
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u.2, by simpa using hu⟩
      · rintro ⟨hyR, hy⟩
        exact ⟨⟨y, hyR⟩, by simpa using hy, rfl⟩
    rw [Subtype.isCompact_iff, hset]
    exact hInter
  exact h (isCompact_unitClosedBall_iff_finiteDimensional (𝕜 := 𝕜).mp hball)

end _thm_compact_range_not_closed
