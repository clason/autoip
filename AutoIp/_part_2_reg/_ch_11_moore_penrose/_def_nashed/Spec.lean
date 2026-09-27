/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.RCLike.Basic

section _def_nashed

namespace AutoIp

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The equation `T x = y` is ill-posed in the sense of Nashed: `Ran(T)` is not closed.
The Lean allows `X` and `Y` to be normed spaces. -/
@[expose]
public def IsNashedIllPosed (T : E →L[𝕜] F) : Prop :=
  ¬ IsClosed (LinearMap.range T.toLinearMap : Set F)

end AutoIp

end _def_nashed
