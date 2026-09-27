/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_12_picard._def_source_set
public import AutoIp._part_2_reg._ch_13_regularization._def_parameter_choice
public import AutoIp._part_2_reg._ch_14_order_optimality._def_worst_case_error

section _def_order_optimal

namespace AutoIp

open Filter Topology
open scoped ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- `({R_α}, β)` is order optimal with constant `c` for `ν` and `ρ`:
`E_β(K x†, δ) ≤ c δ^{ν/(ν+1)} ρ^{1/(ν+1)}` for all `δ > 0` and all `x† ∈ X_{ν,ρ}`. The
source set `X_{ν,ρ}` is formed from a singular system of `K`, and `K` is not assumed
compact. -/
public structure IsOrderOptimal (K : E →L[𝕜] F) (R : Set.Ioi (0 : ℝ) → F → E)
    (b : ParameterChoice F)
    (hs : IsSingularSystem K σ v u) (ν ρ c : ℝ) : Prop where
  /-- `ν > 0`. -/
  nu_pos : 0 < ν
  /-- `ρ > 0`. -/
  rho_pos : 0 < ρ
  /-- `c ≥ 1`. -/
  one_le_const : 1 ≤ c
  /-- `E_β(K x†, δ) ≤ c δ^{ν/(ν+1)} ρ^{1/(ν+1)}` for all `x† ∈ X_{ν,ρ}` and all `δ > 0`. -/
  worstCaseError_le : ∀ x ∈ sourceSet hs ν nu_pos ρ rho_pos, ∀ (δ : ℝ) (hδ : 0 < δ),
    worstCaseError K R b (K x) (Submodule.mem_sup_left ⟨x, rfl⟩) δ hδ ≤
      ENNReal.ofReal (c * δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1)))

/-- `({R_α}, β)` is order optimal for `ν`: for every `x† ∈ X_ν` there is `c = c(x†) ≥ 1`
with `E_β(K x†, δ) ≤ c δ^{ν/(ν+1)}` for all `δ > 0`. The source set `X_ν` is formed from a
singular system of `K`, and `K` is not assumed compact. -/
public structure IsOrderOptimalPointwise (K : E →L[𝕜] F) (R : Set.Ioi (0 : ℝ) → F → E)
    (b : ParameterChoice F)
    (hs : IsSingularSystem K σ v u) (ν : ℝ) : Prop where
  /-- `ν > 0`. -/
  nu_pos : 0 < ν
  /-- For every `x† ∈ X_ν` there is `c ≥ 1` with `E_β(K x†, δ) ≤ c δ^{ν/(ν+1)}` for all
`δ > 0`. -/
  bound : ∀ x ∈ sourceSetAll hs ν nu_pos, ∃ c : ℝ, 1 ≤ c ∧ ∀ (δ : ℝ) (hδ : 0 < δ),
    worstCaseError K R b (K x) (Submodule.mem_sup_left ⟨x, rfl⟩) δ hδ
      ≤ ENNReal.ofReal (c * δ ^ (ν / (ν + 1)))

end AutoIp

end _def_order_optimal
