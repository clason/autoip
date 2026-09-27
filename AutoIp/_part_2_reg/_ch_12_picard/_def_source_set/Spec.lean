/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_frac_power

section _def_source_set

namespace AutoIp

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- The source set `X_{ν,ρ} = {|K|^ν w : w ∈ X, ‖w‖ ≤ ρ}` for `ν, ρ > 0`. -/
public def sourceSet (hs : IsSingularSystem K σ v u) (ν : ℝ) (hν : 0 < ν) (ρ : ℝ)
    -- The condition is an argument because the object is defined only under it, though the
    -- formula does not read it.
    (_hρ : 0 < ρ) : Set E :=
  (hs.absRpow ν hν.le) '' {w : E | ‖w‖ ≤ ρ}

/-- The source set `X_ν = Ran(|K|^ν)` for `ν > 0`. -/
public def sourceSetAll (hs : IsSingularSystem K σ v u) (ν : ℝ) (hν : 0 < ν) : Set E :=
  Set.range (hs.absRpow ν hν.le)

/-- `X_ν = ⋃_{ρ > 0} X_{ν,ρ}`. -/
public theorem iUnion_sourceSet (hs : IsSingularSystem K σ v u) (ν : ℝ) (hν : 0 < ν) :
    ⋃ ρ : Set.Ioi (0 : ℝ), sourceSet hs ν hν (ρ : ℝ) ρ.2 = sourceSetAll hs ν hν := by
  ext x
  simp only [Set.mem_iUnion, sourceSet, sourceSetAll, Set.mem_image,
    Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨ρ, w, -, rfl⟩
    exact ⟨w, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨⟨‖w‖ + 1, Set.mem_Ioi.2 (by positivity)⟩, w, by linarith [norm_nonneg w], rfl⟩

end AutoIp

end _def_source_set
