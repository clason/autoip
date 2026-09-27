/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_14_order_optimality._def_worst_case_error
import AutoIp._part_2_reg._ch_11_moore_penrose._thm_mp_inverse

section _thm_worstcase_lower

namespace AutoIp

open Filter Topology
open scoped ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- For linear `{R_α}`, any parameter choice rule `α`, `δ > 0` and `M ⊆ Ker(T)ᗮ`,
`sup {E(y, δ) : y ∈ Dom(T†), T† y ∈ M} ≥ ε(M, δ)`. -/
public theorem modulusOfContinuity_le_iSup_worstCaseError {T : E →L[𝕜] F}
    (R : Set.Ioi (0 : ℝ) → F →ₗ[𝕜] E)
    (a : ParameterChoice F) {M : Set E} (hM : M ⊆ (T.toLinearMap.kerᗮ : Set E))
    {δ : ℝ} (hδ : 0 < δ) :
    modulusOfContinuity T M δ hδ ≤
      ⨆ y : mpDomain T, ⨆ _ : moorePenrose T ⟨(y : F), y.2⟩ ∈ M,
        worstCaseError T (fun α z => R α z) a (y : F) y.2 δ hδ := by
  rw [modulusOfContinuity]
  refine iSup₂_le ?_
  rintro x ⟨hxM, hxδ⟩
  have hxperp : x ∈ (LinearMap.ker T.toLinearMap)ᗮ := hM hxM
  have hmem : T x ∈ mpDomain T := Submodule.mem_sup_left ⟨x, rfl⟩
  have hmp : moorePenrose T ⟨T x, Submodule.mem_sup_left ⟨x, rfl⟩⟩ = x :=
    moorePenrose_apply_apply_of_mem_orthogonal hxperp
  have hz : (0 : F) ∈ Metric.closedBall (T x) δ := by
    simp only [Metric.mem_closedBall, dist_zero_left]
    simpa using hxδ
  have step1 : ‖x‖ₑ
      ≤ worstCaseError T (fun α z => R α z) a (T x) hmem δ hδ := by
    have := le_worstCaseError T (fun α z => R α z) a (T x) hmem hδ hz
    simpa [hmp] using this
  refine step1.trans ?_
  exact le_iSup₂ (α := ℝ≥0∞)
    (f := fun (y : mpDomain T) (_ : moorePenrose T ⟨(y : F), y.2⟩ ∈ M) =>
      worstCaseError T (fun α z => R α z) a (y : F) y.2 δ hδ)
    (⟨T x, hmem⟩ : mpDomain T) (by rw [hmp]; exact hxM)

end AutoIp

end _thm_worstcase_lower
