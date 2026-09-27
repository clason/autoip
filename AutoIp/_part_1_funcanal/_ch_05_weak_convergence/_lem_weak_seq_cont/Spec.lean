/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_05_weak_convergence._def_weak_conv

section _lem_weak_seq_cont

open scoped Topology
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If T ∈ 𝓛(E, F) and xₙ ⇀ a then Txₙ ⇀ Ta. -/
public theorem TendstoWeakly.map (T : E →L[𝕜] F) {x : ℕ → E} {a : E}
    (h : TendstoWeakly 𝕜 x a) :
    TendstoWeakly 𝕜 (fun n => T (x n)) (T a) :=
  fun g => h (g ∘L T)

end _lem_weak_seq_cont
