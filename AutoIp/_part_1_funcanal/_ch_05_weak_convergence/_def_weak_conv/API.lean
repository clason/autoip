/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_05_weak_convergence._def_weak_conv.Spec

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Weak convergence passes to subsequences. -/
public theorem TendstoWeakly.comp {x : ℕ → E} {a : E} (h : TendstoWeakly 𝕜 x a)
    {ns : ℕ → ℕ} (hns : Filter.Tendsto ns Filter.atTop Filter.atTop) :
    TendstoWeakly 𝕜 (x ∘ ns) a :=
  fun g => (h g).comp hns
