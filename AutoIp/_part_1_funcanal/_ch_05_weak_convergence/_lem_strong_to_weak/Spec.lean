/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_05_weak_convergence._def_weak_conv

section _lem_strong_to_weak

open scoped Topology
variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- If xₙ → a in norm then xₙ ⇀ a. -/
public theorem TendstoWeakly.of_tendsto {x : ℕ → E} {a : E}
    (h : Filter.Tendsto x Filter.atTop (nhds a)) : TendstoWeakly 𝕜 x a :=
  fun f => (f.continuous.tendsto a).comp h

end _lem_strong_to_weak
