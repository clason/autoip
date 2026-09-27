/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace

section _prop_dense_ptwise_filter

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Pointwise convergence along a filter: let `X`, `Y` be normed spaces, `ℱ` a filter on an
index set `ι`, and `T i ∈ L(X,Y)` with `‖T i‖ ≤ C` for all `i`. Let `S ∈ L(X,Y)` and let `M ⊆ X`
be total. If `T i x → S x` along `ℱ` for every `x ∈ M`, then `T i x → S x` along `ℱ` for every
`x ∈ X`. The blueprint's `T` is `S` here, `sup_i ‖T_i‖ < ∞` is the bound `C`, and `M` total is
written as `span M` being dense. -/
public theorem tendsto_of_dense_span_filter {ι : Type*} (ℱ : Filter ι)
    (T : ι → E →L[𝕜] F) (S : E →L[𝕜] F) (C : ℝ) (hC : ∀ i, ‖T i‖ ≤ C)
    (M : Set E) (hM : Dense (Submodule.span 𝕜 M : Set E))
    (hTM : ∀ x ∈ M, Filter.Tendsto (fun i => T i x) ℱ (nhds (S x))) :
    ∀ x : E, Filter.Tendsto (fun i => T i x) ℱ (nhds (S x)) := by
  let W : Submodule 𝕜 E :=
    { carrier := {x | Filter.Tendsto (fun i => T i x) ℱ (nhds (S x))}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        simpa only [map_add] using ha.add hb
      zero_mem' := by
        simp only [Set.mem_ofPred_eq]
        simpa only [map_zero] using tendsto_const_nhds
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        simpa only [map_smul] using ha.const_smul c }
  have hbound : ∃ C', ∀ i, ‖T i‖ ≤ C' := ⟨C, hC⟩
  have hequi : Equicontinuous ((↑) ∘ T) :=
    ((NormedSpace.equicontinuous_TFAE T).out 5 1).mp hbound
  have hclosed : IsClosed (W : Set E) := hequi.isClosed_setOfPred_tendsto S.continuous
  have hspan : Submodule.span 𝕜 M ≤ W := Submodule.span_le.mpr hTM
  intro x
  exact hclosed.closure_subset_iff.mpr hspan (hM x)

end ContinuousLinearMap

end _prop_dense_ptwise_filter
