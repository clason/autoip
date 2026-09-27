/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_12_picard._def_source_set.Spec
import all AutoIp._part_2_reg._ch_12_picard._def_source_set.Spec

namespace AutoIp

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- `X_{ν,ρ}` is the image of the closed ball of radius `ρ` under `|K|^ν`. -/
public theorem sourceSet_def (hs : IsSingularSystem K σ v u) (ν : ℝ) (hν : 0 < ν) (ρ : ℝ)
    (hρ : 0 < ρ) :
    sourceSet hs ν hν ρ hρ = (hs.absRpow ν hν.le) '' {w : E | ‖w‖ ≤ ρ} := by
  unfold sourceSet
  rfl

/-- `x ∈ X_{ν,ρ}` if and only if `x = |K|^ν w` for some `w` with `‖w‖ ≤ ρ`. -/
public theorem mem_sourceSet_iff (hs : IsSingularSystem K σ v u) (ν : ℝ) (hν : 0 < ν) (ρ : ℝ)
    (hρ : 0 < ρ) {x : E} :
    x ∈ sourceSet hs ν hν ρ hρ ↔ ∃ w : E, ‖w‖ ≤ ρ ∧ hs.absRpow ν hν.le w = x := by
  rw [sourceSet_def]
  exact Iff.rfl

/-- `x ∈ X_ν` if and only if `x = |K|^ν w` for some `w ∈ X`. -/
public theorem mem_sourceSetAll_iff (hs : IsSingularSystem K σ v u) (ν : ℝ) (hν : 0 < ν)
    {x : E} :
    x ∈ sourceSetAll hs ν hν ↔ ∃ w : E, hs.absRpow ν hν.le w = x := by
  unfold sourceSetAll
  exact Iff.rfl

/-- `X_{ν,ρ} ⊆ X_{ν,ρ'}` for `ρ ≤ ρ'`. -/
public theorem sourceSet_mono_radius (hs : IsSingularSystem K σ v u) (ν : ℝ) (hν : 0 < ν) {ρ ρ' : ℝ}
    (hρ0 : 0 < ρ) (hρ : ρ ≤ ρ') :
    sourceSet hs ν hν ρ hρ0 ⊆ sourceSet hs ν hν ρ' (lt_of_lt_of_le hρ0 hρ) := by
  intro x hx
  rw [mem_sourceSet_iff] at hx ⊢
  obtain ⟨w, hw, rfl⟩ := hx
  exact ⟨w, le_trans hw hρ, rfl⟩

end AutoIp
