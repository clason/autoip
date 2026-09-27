/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

section _thm_closed_range

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Closed range criterion: for Banach spaces `X`, `Y` and `T ∈ L(X,Y)`, `R(T)` is closed if and
only if there is `c > 0` with `c ‖x + N(T)‖ ≤ ‖T x‖` for all `x ∈ X`, the norm on the left being
that of `X/N(T)`. The rephrasing as the induced operator `X/N(T) → Y` being bounded below is not
stated separately. -/
public theorem isClosed_range_iff_exists_mul_norm_quotient_le [CompleteSpace E] [CompleteSpace F]
    (T : E →L[𝕜] F) :
    IsClosed (T.toLinearMap.range : Set F) ↔
      ∃ c > 0, ∀ x : E,
        c * ‖Submodule.Quotient.mk (p := T.toLinearMap.ker) x‖ ≤ ‖T x‖ := by
  set N := LinearMap.ker T.toLinearMap with hN
  constructor
  · -- (→) The corestriction of `T` to its range is a surjection onto a Banach space, so the
    -- open mapping theorem provides preimages of controlled norm; the quotient norm is an
    -- infimum over `N`, so that control passes to it.  Uses completeness of both `E` and `F`.
    intro hclosed
    have : CompleteSpace (LinearMap.range T.toLinearMap) := hclosed.completeSpace_coe
    set T' : E →L[𝕜] LinearMap.range T.toLinearMap :=
      T.codRestrict (LinearMap.range T.toLinearMap) (fun x => ⟨x, rfl⟩)
    have hsurj : Function.Surjective T' := by
      rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩
    obtain ⟨C, hCpos, hC⟩ := ContinuousLinearMap.exists_preimage_norm_le T' hsurj
    refine ⟨C⁻¹, by positivity, fun x => ?_⟩
    obtain ⟨x', hx'eq, hx'le⟩ := hC (T' x)
    have hker : x - x' ∈ N := by
      have : T x' = T x := congrArg Subtype.val hx'eq
      simp [hN, LinearMap.mem_ker, map_sub, this]
    have hmk : (Submodule.Quotient.mk x : E ⧸ N) = Submodule.Quotient.mk x' :=
      (Submodule.Quotient.eq N).mpr hker
    have hnorm : ‖(Submodule.Quotient.mk x : E ⧸ N)‖ ≤ C * ‖T x‖ := by
      rw [hmk]
      exact le_trans (Submodule.Quotient.norm_mk_le N x') hx'le
    calc C⁻¹ * ‖(Submodule.Quotient.mk x : E ⧸ N)‖
        ≤ C⁻¹ * (C * ‖T x‖) := mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = ‖T x‖ := by field_simp
  · -- (←) The induced map on `E ⧸ N` is antilipschitz, hence has closed range; and its range
    -- is that of `T`.  Uses completeness of `E` only.
    rintro ⟨c, hc, hbound⟩
    set Th : E ⧸ N →L[𝕜] F := N.liftQL T le_rfl with hTh
    have happ : ∀ x : E, Th (Submodule.Quotient.mk x) = T x := by
      intro x; simp [hTh, Submodule.coe_liftQL]
    have hanti : ∀ ξ : E ⧸ N, ‖ξ‖ ≤ (c⁻¹ : ℝ) * ‖Th ξ‖ := by
      intro ξ
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N ξ
      rw [happ, inv_mul_eq_div, le_div_iff₀ hc]
      calc ‖(Submodule.Quotient.mk x : E ⧸ N)‖ * c
          = c * ‖(Submodule.Quotient.mk x : E ⧸ N)‖ := mul_comm _ _
        _ ≤ ‖T x‖ := hbound x
    have hK : AntilipschitzWith (Real.toNNReal c⁻¹) Th :=
      Th.antilipschitz_of_bound fun ξ => by
        simpa [Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ c⁻¹)] using hanti ξ
    have : IsClosed (Set.range Th) := hK.isClosed_range Th.uniformContinuous
    have hrange : Set.range Th = (LinearMap.range T.toLinearMap : Set F) := by
      ext y
      simp only [Set.mem_range, SetLike.mem_coe, LinearMap.mem_range,
        ContinuousLinearMap.coe_coe]
      constructor
      · rintro ⟨ξ, rfl⟩
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N ξ
        exact ⟨x, happ x⟩
      · rintro ⟨x, rfl⟩
        exact ⟨Submodule.Quotient.mk x, happ x⟩
    rwa [hrange] at this

end ContinuousLinearMap

end _thm_closed_range
