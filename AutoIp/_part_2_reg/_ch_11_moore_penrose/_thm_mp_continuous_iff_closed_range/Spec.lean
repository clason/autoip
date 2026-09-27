/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
import AutoIp._part_1_funcanal._ch_01_bounded_operators._thm_closed_range
import AutoIp._part_1_funcanal._ch_03_hilbert_spaces._lem_closed_range_adjoint
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_equations
import AutoIp.Auxiliary.QuotientNorm

section _thm_mp_continuous_iff_closed_range

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- `T† : Dom(T†) → X` is bounded if and only if `Ran(T)` is closed. Boundedness is stated
as a bound `‖T† y‖ ≤ C ‖y‖` on `Dom(T†)`. -/
public theorem exists_norm_moorePenrose_le_iff_isClosed_range {T : E →L[𝕜] F} :
    (∃ C : ℝ, ∀ y : (moorePenrose T).domain, ‖moorePenrose T y‖ ≤ C * ‖(y : F)‖) ↔
      IsClosed (T.toLinearMap.range : Set F) := by
  constructor
  · rintro ⟨C, hC⟩
    rw [ContinuousLinearMap.isClosed_range_iff_exists_mul_norm_quotient_le]
    have hpos : (0 : ℝ) < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    refine ⟨(max C 1)⁻¹, by positivity, fun x => ?_⟩
    have h2 : ‖moorePenrose T ⟨(T x), (Submodule.mem_sup_left ⟨x, rfl⟩)⟩‖ ≤ C * ‖T x‖ :=
      hC ⟨T x, Submodule.mem_sup_left ⟨x, rfl⟩⟩
    rw [moorePenrose_apply_apply x] at h2
    have h3 : (Submodule.Quotient.mk x : E ⧸ LinearMap.ker T.toLinearMap)
        = Submodule.Quotient.mk (x - (LinearMap.ker T.toLinearMap).starProjection x) := by
      refine ((Submodule.Quotient.eq _).mpr ?_).symm
      have hx : x - (LinearMap.ker T.toLinearMap).starProjection x - x
          = -((LinearMap.ker T.toLinearMap).starProjection x) := by abel
      rw [hx]
      exact Submodule.neg_mem _ (Submodule.starProjection_apply_mem _ _)
    have h4 : ‖(Submodule.Quotient.mk x : E ⧸ LinearMap.ker T.toLinearMap)‖
        ≤ ‖x - (LinearMap.ker T.toLinearMap).starProjection x‖ := by
      rw [h3]
      exact Submodule.Quotient.norm_mk_le _ _
    have key : ‖(Submodule.Quotient.mk x : E ⧸ LinearMap.ker T.toLinearMap)‖
        ≤ max C 1 * ‖T x‖ := by
      have := le_max_left C 1
      nlinarith [norm_nonneg (T x)]
    calc (max C 1)⁻¹ * ‖(Submodule.Quotient.mk x : E ⧸ LinearMap.ker T.toLinearMap)‖
        ≤ (max C 1)⁻¹ * (max C 1 * ‖T x‖) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = ‖T x‖ := by field_simp
  · intro hclosed
    have hperp_norm : ∀ w ∈ (LinearMap.ker T.toLinearMap)ᗮ,
        ‖w‖ ≤ ‖(Submodule.Quotient.mk w : E ⧸ LinearMap.ker T.toLinearMap)‖ :=
      fun w hw => (Submodule.Quotient.norm_mk_eq_norm_of_mem_orthogonal _ hw).ge
    obtain ⟨c, hc, hb⟩ :=
      (ContinuousLinearMap.isClosed_range_iff_exists_mul_norm_quotient_le T).mp hclosed
    refine ⟨c⁻¹, fun y => ?_⟩
    have hmin := moorePenrose_isMinimumNorm y
    have hkerperp : moorePenrose T y ∈ (LinearMap.ker T.toLinearMap)ᗮ :=
      (isMinimumNorm_iff.1 hmin).2
    have h1 := hb (moorePenrose T y)
    have h2 := hperp_norm _ hkerperp
    have h3 : ‖T (moorePenrose T y)‖ ≤ ‖(y : F)‖ := by
      rw [apply_moorePenrose y]
      exact Submodule.norm_starProjection_apply_le _ (y : F)
    have h4 : c * ‖moorePenrose T y‖ ≤ ‖(y : F)‖ := by nlinarith
    have h5 : ‖moorePenrose T y‖ = c⁻¹ * (c * ‖moorePenrose T y‖) := by field_simp
    rw [h5]
    exact mul_le_mul_of_nonneg_left h4 (by positivity)

end AutoIp

end _thm_mp_continuous_iff_closed_range
