/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_20_iterated_tikhonov._def_iterated_tikhonov
import AutoIp._part_2_reg._ch_20_iterated_tikhonov._lem_iterated_tikhonov_filter.Helpers
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init

section _lem_iterated_tikhonov_filter

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- `{φ^(m)_α}` is a regularizing filter with `C_φ = 1`, for `m ≥ 1`.

It holds for every `K`, `K = 0` included. -/
public theorem iteratedTikhonovFilter_isRegularizingFilter (K : E →L[𝕜] F) {m : ℕ} (hm : 0 < m) :
    IsRegularizingFilter K (iteratedTikhonovFilter m) 1 :=
  (iteratedTikhonov_filter_aux K hm).1

/-- Condition (F) with `C_F = m`: `sup_{λ ∈ (0,κ]} |φ^(m)_α(λ)| ≤ m α⁻¹` for all `α > 0`, for
`m ≥ 1`. It is stated as this bound rather than as condition (F) in its structure form, which
also asks for the regularizing-filter property and `C_F > 0`.

It holds for every `K`, `K = 0` included. -/
public theorem iSup_abs_iteratedTikhonovFilter_le (K : E →L[𝕜] F) {m : ℕ} (hm : 0 < m) :
    ∀ α : Set.Ioi (0 : ℝ),
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), |iteratedTikhonovFilter m α lam|) ≤
        (m : ℝ) * (α : ℝ)⁻¹ :=
  (iteratedTikhonov_filter_aux K hm).2

end AutoIp

end _lem_iterated_tikhonov_filter
