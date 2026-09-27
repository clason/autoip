/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.RCLike.Basic
import AutoIp._part_1_funcanal._ch_01_bounded_operators._prop_ptwise_limit_exists.Helpers

section _prop_ptwise_limit_exists

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Existence of the limit operator: let `X` be a normed space, `Y` a Banach space,
`T n ∈ L(X,Y)`, and `M ⊆ X` total. If `‖T n‖ ≤ C` for every `n` and `T n x` converges for every
`x ∈ M`, then there is `S ∈ L(X,Y)` with `‖S‖ ≤ C` and `T n → S` pointwise. The blueprint's `T`
is `S` here, and `M` total is written as `span M` being dense. -/
public theorem exists_tendsto_of_dense_span [CompleteSpace F]
    (T : ℕ → E →L[𝕜] F) (C : ℝ) (hC : ∀ n, ‖T n‖ ≤ C)
    (M : Set E) (hM : Dense (Submodule.span 𝕜 M : Set E))
    (hTM : ∀ x ∈ M, ∃ y : F, Filter.Tendsto (fun n => T n x) Filter.atTop (nhds y)) :
    ∃ S : E →L[𝕜] F, ‖S‖ ≤ C ∧
      ∀ x : E, Filter.Tendsto (fun n => T n x) Filter.atTop (nhds (S x)) :=
  exists_tendsto_of_dense_span_filter_of_eventually_norm_le Filter.atTop T C
    (Filter.Eventually.of_forall hC) M hM hTM

end ContinuousLinearMap

end _prop_ptwise_limit_exists
