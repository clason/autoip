/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_20_iterated_tikhonov._def_landweber_residual_poly.Spec
import all AutoIp._part_2_reg._ch_20_iterated_tikhonov._def_landweber_residual_poly.Spec

namespace AutoIp

/-- The defining equation `q_k(λ) = (1 - ωλ)^k`. -/
public theorem landweberResidualPoly_apply (ω : ℝ) (k : ℕ) :
    landweberResidualPoly ω k = (1 - Polynomial.C ω * Polynomial.X) ^ k := by
  unfold landweberResidualPoly
  rfl

end AutoIp
