/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_12_picard._def_source_set
public import AutoIp._part_2_reg._ch_19_general_source_conditions._def_general_source
import AutoIp._part_2_reg._ch_19_general_source_conditions._lem_source_monotone
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound

section _lem_holder_is_index

section

namespace AutoIp

open Filter Topology

/-- For `ν > 0`, `φ_ν(λ) := λ^{ν/2}` is an index function on `[0, κ]`.

The statement holds for every real `κ`. -/
public theorem isIndexFunction_rpow {ν : ℝ} (hν : 0 < ν) (κ : ℝ) :
    IsIndexFunction κ (fun t => t ^ (ν / 2)) :=
  by
  refine ⟨?_, ?_, ?_⟩
  · exact Real.zero_rpow (show (0:ℝ) < ν / 2 by linarith).ne'
  · exact fun t _ =>
      (Real.continuousAt_rpow_const t (ν / 2) (Or.inr (by linarith))).continuousWithinAt
  · exact fun a ha _ _ hab => Real.rpow_lt_rpow ha.1 hab (by linarith)

end AutoIp

end

section

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- For `ν > 0` and `ρ > 0`, `X_{φ_ν,ρ} = X_{ν,ρ}`. -/
public theorem sourceSetIndex_rpow (hs : IsSingularSystem K σ v u) {ν ρ : ℝ} (hν : 0 < ν)
    (hρ : 0 < ρ) :
    sourceSetIndex hs (fun t => t ^ (ν / 2)) (hs.exists_bound_rpow_sq (by linarith)) ρ hρ
      = sourceSet hs ν hν ρ hρ := by
  rw [sourceSetIndex_def, sourceSet_def]
  rw [hs.absRpow_def ν hν.le (hs.exists_bound_rpow_sq (by linarith))]

end AutoIp

end

end _lem_holder_is_index
