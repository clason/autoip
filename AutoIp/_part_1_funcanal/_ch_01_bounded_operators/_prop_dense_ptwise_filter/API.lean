/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_01_bounded_operators._prop_dense_ptwise_filter.Spec
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Normed.Operator.Basic

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Pointwise convergence along a filter, under a bound that need only hold eventually. -/
public theorem tendsto_of_dense_span_filter_of_eventually_norm_le {ι : Type*} (ℱ : Filter ι)
    (T : ι → E →L[𝕜] F) (S : E →L[𝕜] F) (C : ℝ) (hC : ∀ᶠ i in ℱ, ‖T i‖ ≤ C)
    (M : Set E) (hM : Dense (Submodule.span 𝕜 M : Set E))
    (hTM : ∀ x ∈ M, Filter.Tendsto (fun i => T i x) ℱ (nhds (S x))) :
    ∀ x : E, Filter.Tendsto (fun i => T i x) ℱ (nhds (S x)) := by
  classical
  -- Equicontinuity is a statement about every index, so an eventual bound cannot be fed
  -- to `tendsto_of_dense_span_filter` directly. Replacing `T i` by `0` where the bound fails
  -- restores a total bound and changes no `ℱ`-limit, the two families agreeing
  -- `ℱ`-eventually.
  set T' : ι → E →L[𝕜] F := fun i => if ‖T i‖ ≤ C then T i else 0 with hT'
  have heq : ∀ x : E, (fun i => T' i x) =ᶠ[ℱ] fun i => T i x :=
    fun x => hC.mono fun i hi => by simp only [hT', ite_eq_left hi]
  have hC' : ∀ i, ‖T' i‖ ≤ max C 0 := by
    intro i
    by_cases hi : ‖T i‖ ≤ C
    · rw [hT']
      simp only [ite_eq_left hi]
      exact le_trans hi (le_max_left _ _)
    · rw [hT']
      simp only [ite_eq_right hi, norm_zero]
      exact le_max_right _ _
  intro x
  refine (Filter.tendsto_congr' (heq x)).mp ?_
  exact tendsto_of_dense_span_filter ℱ T' S (max C 0) hC' M hM
    (fun y hy => (Filter.tendsto_congr' (heq y)).mpr (hTM y hy)) x

end ContinuousLinearMap
