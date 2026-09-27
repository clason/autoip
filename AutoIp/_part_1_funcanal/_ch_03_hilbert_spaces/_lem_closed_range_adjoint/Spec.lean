/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
import AutoIp.Auxiliary.QuotientNorm
import AutoIp._part_1_funcanal._ch_01_bounded_operators._thm_closed_range

section _lem_closed_range_adjoint

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Closed range transfers to the adjoint, the "in particular": if `T ∈ 𝓛(X, Y)` between
Hilbert spaces has closed range, then `R(T*)` is closed. -/
public theorem ContinuousLinearMap.isClosed_range_adjoint_of_isClosed_range (T : E →L[𝕜] F)
    (hT : IsClosed (T.toLinearMap.range : Set F)) :
    IsClosed (T.adjoint.toLinearMap.range : Set E) := by
  have hperp_norm : ∀ w ∈ (LinearMap.ker T.toLinearMap)ᗮ,
      ‖w‖ ≤ ‖(Submodule.Quotient.mk w : E ⧸ LinearMap.ker T.toLinearMap)‖ :=
    fun w hw => (Submodule.Quotient.norm_mk_eq_norm_of_mem_orthogonal _ hw).ge
  -- The closed range criterion for `T` gives a lower bound; transport it to `T*`.
  obtain ⟨c, hc, hb⟩ := (ContinuousLinearMap.isClosed_range_iff_exists_mul_norm_quotient_le T).mp hT
  have hRcomplete : CompleteSpace (LinearMap.range T.toLinearMap) := hT.completeSpace_coe
  rw [ContinuousLinearMap.isClosed_range_iff_exists_mul_norm_quotient_le]
  refine ⟨c, hc, fun y => ?_⟩
  set R : Submodule 𝕜 F := LinearMap.range T.toLinearMap with hR
  set P : F := R.starProjection y with hP
  have hPmem : P ∈ R := R.starProjection_apply_mem y
  have hPerp : y - P ∈ Rᗮ := R.sub_starProjection_mem_orthogonal y
  -- `y` and `P` have the same class mod `ker T* = (range T)ᗮ`.
  have hkeradj : Rᗮ = LinearMap.ker (ContinuousLinearMap.adjoint T).toLinearMap :=
    T.orthogonal_range
  have hmk : ‖(Submodule.Quotient.mk y :
      F ⧸ LinearMap.ker (ContinuousLinearMap.adjoint T).toLinearMap)‖ ≤ ‖P‖ := by
    have heq : (Submodule.Quotient.mk y :
        F ⧸ LinearMap.ker (ContinuousLinearMap.adjoint T).toLinearMap)
          = Submodule.Quotient.mk P :=
      (Submodule.Quotient.eq _).mpr (hkeradj ▸ hPerp)
    rw [heq]
    exact Submodule.Quotient.norm_mk_le _ P
  -- A preimage of `P` orthogonal to `ker T`, on which `T` is bounded below by `c`.
  obtain ⟨v, hv⟩ := id hPmem
  set w : E := v - (LinearMap.ker T.toLinearMap).starProjection v with hw
  have hwperp : w ∈ (LinearMap.ker T.toLinearMap)ᗮ :=
    (LinearMap.ker T.toLinearMap).sub_starProjection_mem_orthogonal v
  have hTw : T w = P := by
    have hmem := (LinearMap.ker T.toLinearMap).starProjection_apply_mem v
    have hz : T ((LinearMap.ker T.toLinearMap).starProjection v) = 0 :=
      LinearMap.mem_ker.mp hmem
    rw [hw, map_sub, hz, sub_zero]
    exact hv
  have hcw : c * ‖w‖ ≤ ‖P‖ := by
    have h1 := hb w
    have h2 := hperp_norm w hwperp
    rw [hTw] at h1
    nlinarith [hc, norm_nonneg w]
  -- Cauchy--Schwarz against `w` turns the bound into one for `T*`.
  have hinner : inner 𝕜 (ContinuousLinearMap.adjoint T y) w = ((‖P‖ ^ 2 : ℝ) : 𝕜) := by
    rw [ContinuousLinearMap.adjoint_inner_left, hTw]
    have hsplit : inner 𝕜 y P = inner 𝕜 P P + inner 𝕜 (y - P) P := by
      rw [← inner_add_left]; congr 1; abel
    rw [hsplit, ((Submodule.mem_orthogonal' _ _).mp hPerp) P hPmem, add_zero,
      inner_self_eq_norm_sq_to_K, RCLike.ofReal_pow]
  have hcs : ‖P‖ ^ 2 ≤ ‖ContinuousLinearMap.adjoint T y‖ * ‖w‖ := by
    have h1 : ‖inner 𝕜 (ContinuousLinearMap.adjoint T y) w‖
        ≤ ‖ContinuousLinearMap.adjoint T y‖ * ‖w‖ := norm_inner_le_norm _ _
    rw [hinner] at h1
    simpa [abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖P‖ ^ 2)] using h1
  have hkey : c * ‖P‖ ≤ ‖ContinuousLinearMap.adjoint T y‖ := by
    rcases eq_or_lt_of_le (norm_nonneg P) with hP0 | hP0
    · rw [← hP0, mul_zero]
      exact norm_nonneg _
    · nlinarith [hcs, hcw, hP0, norm_nonneg (ContinuousLinearMap.adjoint T y)]
  calc c * ‖(Submodule.Quotient.mk y :
        F ⧸ LinearMap.ker (ContinuousLinearMap.adjoint T).toLinearMap)‖
      ≤ c * ‖P‖ := mul_le_mul_of_nonneg_left hmk hc.le
    _ ≤ ‖ContinuousLinearMap.adjoint T y‖ := hkey

/-- Closed range transfers to the adjoint: if `T ∈ 𝓛(X, Y)` between Hilbert spaces has closed
range, then `R(T*) = N(T)⊥`. -/
public theorem ContinuousLinearMap.range_adjoint_eq_orthogonal_ker_of_isClosed_range (T : E →L[𝕜] F)
    (hT : IsClosed (T.toLinearMap.range : Set F)) :
    T.adjoint.toLinearMap.range
      = (T.toLinearMap.ker)ᗮ := by
  rw [ContinuousLinearMap.orthogonal_ker]
  exact (T.isClosed_range_adjoint_of_isClosed_range hT).submodule_topologicalClosure_eq.symm

end _lem_closed_range_adjoint
