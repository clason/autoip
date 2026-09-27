/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
import AutoIp._part_1_funcanal._ch_06_compact_operators._lem_compact_seq
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

section

open Metric
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Naturality of the canonical embedding into the bidual: `T'' ∘ J_E = J_F ∘ T`. -/
public theorem precomp_precomp_comp_inclusionInDoubleDual (T : E →L[𝕜] F) :
    ((ContinuousLinearMap.precomp 𝕜 (ContinuousLinearMap.precomp 𝕜 T)
        : StrongDual 𝕜 (StrongDual 𝕜 E) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F)).comp
      (NormedSpace.inclusionInDoubleDual 𝕜 E))
      = (NormedSpace.inclusionInDoubleDual 𝕜 F).comp T := by
  ext x g
  simp [NormedSpace.dual_def]

end
