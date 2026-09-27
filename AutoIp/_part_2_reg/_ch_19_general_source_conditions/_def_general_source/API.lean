/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_19_general_source_conditions._def_general_source.Spec
import all AutoIp._part_2_reg._ch_19_general_source_conditions._def_general_source.Spec
public import AutoIp._part_2_reg._ch_19_general_source_conditions._def_index_function
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- `X_{φ,ρ}` is the image of the closed ball of radius `ρ` under `φ(K*K)`. -/
public theorem sourceSetIndex_def (hs : IsSingularSystem K σ v u) (φ : ℝ → ℝ)
    (hφ : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C) (ρ : ℝ) (hρ : 0 < ρ) :
    sourceSetIndex hs φ hφ ρ hρ = (hs.funCalc φ hφ) '' {w : E | ‖w‖ ≤ ρ} := by
  unfold sourceSetIndex
  rfl

/-- `x ∈ X_{φ,ρ}` if and only if `x = φ(K*K) w` for some `w` with `‖w‖ ≤ ρ`. -/
public theorem mem_sourceSetIndex_iff (hs : IsSingularSystem K σ v u) (φ : ℝ → ℝ)
    (hφ : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C) (ρ : ℝ) (hρ : 0 < ρ) {x : E} :
    x ∈ sourceSetIndex hs φ hφ ρ hρ ↔ ∃ w : E, ‖w‖ ≤ ρ ∧ hs.funCalc φ hφ w = x := by
  unfold sourceSetIndex
  exact Iff.rfl

/-- An index function on `[0, ‖K‖²]` is bounded on the squared singular values `σᵢ²`. -/
public theorem IsIndexFunction.exists_bound_on_spectrum (hs : IsSingularSystem K σ v u)
    {φ : ℝ → ℝ} (hφ : IsIndexFunction (‖K‖ ^ 2) φ) : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C := by
  refine ⟨φ (‖K‖ ^ 2), fun i => ?_⟩
  rw [abs_of_nonneg (hφ.nonneg _ (hs.sq_mem_Icc i))]
  exact hφ.strictMonoOn.monotoneOn (hs.sq_mem_Icc i) ⟨by positivity, le_rfl⟩
    (hs.sq_mem_Icc i).2

/-- For an index function `φ`, `X_{φ,ρ} ⊆ Ker(K)^⊥`. -/
public
theorem sourceSetIndex_subset_orthogonal_ker (hs : IsSingularSystem K σ v u) {φ : ℝ → ℝ}
    {ρ : ℝ} {hρ : 0 < ρ} (hφ : IsIndexFunction (‖K‖ ^ 2) φ) :
    sourceSetIndex hs φ (hφ.exists_bound_on_spectrum hs) ρ hρ
      ⊆ ((K.toLinearMap.ker)ᗮ : Set E) := by
  have hb : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C := hφ.exists_bound_on_spectrum hs
  have hvU : ∀ i, v i ∈ (LinearMap.ker K.toLinearMap)ᗮ := fun i => by
    rw [← hs.span_left]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [Set.subset_def]
  intro x hx
  rw [mem_sourceSetIndex_iff] at hx
  obtain ⟨w, -, rfl⟩ := hx
  have h := hs.hasSum_funCalc_sub_starProjection hb w
  rw [hφ.map_zero, RCLike.ofReal_zero, zero_smul, sub_zero] at h
  rw [SetLike.mem_coe]
  refine (Submodule.isClosed_orthogonal _).mem_of_tendsto h ?_
  exact Filter.Eventually.of_forall fun s =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hvU i)

/-- `X_{φ,ρ} ⊆ X_{φ,ρ'}` for `ρ ≤ ρ'`. -/
public theorem sourceSetIndex_mono_radius (hs : IsSingularSystem K σ v u) (φ : ℝ → ℝ)
    (hφ : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C) {ρ ρ' : ℝ} (hρ0 : 0 < ρ) (hρ0' : 0 < ρ')
    (hρ : ρ ≤ ρ') :
    sourceSetIndex hs φ hφ ρ hρ0 ⊆ sourceSetIndex hs φ hφ ρ' hρ0' := by
  intro x hx
  rw [mem_sourceSetIndex_iff] at hx ⊢
  obtain ⟨w, hw, rfl⟩ := hx
  exact ⟨w, le_trans hw hρ, rfl⟩

end AutoIp
