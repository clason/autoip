/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_fun_calc_y.Spec
import all AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_fun_calc_y.Spec
import AutoIp._part_1_funcanal._ch_03_hilbert_spaces._prop_adjoint_props

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- `ψ(KK*)` is the calculus of `K*` built from the singular system `{(σₙ, uₙ, vₙ)}` of `K*`. -/
public theorem IsSingularSystem.funCalcRight_eq (hs : IsSingularSystem K σ v u) (ψ : ℝ → ℝ)
    (hψ : ∃ C, ∀ i, |ψ (σ i ^ 2)| ≤ C) :
    hs.funCalcRight ψ hψ = hs.adjoint.funCalc ψ hψ := by
  unfold IsSingularSystem.funCalcRight
  rfl

/-- The Fourier series of `y` against the right singular vectors sums to its projection onto
the closure of `𝓡(K)`. -/
public
theorem IsSingularSystem.hasSum_starProjection_range (hs : IsSingularSystem K σ v u) (y : F) :
    HasSum (fun i => (inner 𝕜 (u i) y : 𝕜) • u i)
      (K.toLinearMap.range.topologicalClosure.starProjection y) := by
  -- `simp only` on the goal rather than `rw` on the hypothesis: `starProjection` carries a
  -- completeness instance for its submodule, so rewriting the submodule under it leaves a
  -- motive that does not typecheck.
  have hMN : (LinearMap.range K.toLinearMap).topologicalClosure
      = (LinearMap.ker (ContinuousLinearMap.adjoint K).toLinearMap)ᗮ := by
    rw [ContinuousLinearMap.orthogonal_ker, ContinuousLinearMap.adjoint_adjoint]
  simp only [hMN, Submodule.starProjection_orthogonal_val]
  exact hs.adjoint.hasSum_sub_starProjection y

/-- `ψ(KK*) uᵢ = ψ(σᵢ²) uᵢ`. -/
public theorem IsSingularSystem.funCalcRight_apply_u (hs : IsSingularSystem K σ v u) {ψ : ℝ → ℝ}
    (hψ : ∃ C, ∀ i, |ψ (σ i ^ 2)| ≤ C) (i : ι) :
    hs.funCalcRight ψ hψ (u i) = (ψ (σ i ^ 2) : 𝕜) • u i :=
  hs.adjoint.funCalc_apply_v hψ i

/-- `ψ(KK*)` is self-adjoint. -/
public theorem IsSingularSystem.isSelfAdjoint_funCalcRight (hs : IsSingularSystem K σ v u)
    {ψ : ℝ → ℝ} (hψ : ∃ C, ∀ i, |ψ (σ i ^ 2)| ≤ C) :
    IsSelfAdjoint (hs.funCalcRight ψ hψ) :=
  hs.adjoint.isSelfAdjoint_funCalc hψ
