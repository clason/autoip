/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_05_weak_convergence._def_weak_conv
import Mathlib.Analysis.LocallyConvex.SeparatingDual

section _lem_weak_limit_unique

open scoped Topology
variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A sequence in a normed space has at most one weak limit: if xₙ ⇀ a and xₙ ⇀ b then
a = b. -/
public theorem TendstoWeakly.unique {x : ℕ → E} {a b : E}
    (ha : TendstoWeakly 𝕜 x a) (hb : TendstoWeakly 𝕜 x b) :
    a = b :=
  SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜) |>.mpr fun f =>
    tendsto_nhds_unique (ha f) (hb f)

end _lem_weak_limit_unique
