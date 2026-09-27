/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_fun_calc

section _def_spectral_reg

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Spectral regularization operator: `R_α := φ_α(K*K) K*`, with `φ_α(K*K)` the function of
`K*K` given by the singular system `{(σ_n, u_n, v_n)}` of `K`. The family `{φ_α}` need not be
a regularizing filter; the bound of each `φ_α` at the `σ_n²` is there because the
functional calculus needs it as an argument. -/
public noncomputable def spectralReg (hs : IsSingularSystem K σ v u)
    (φ : Set.Ioi (0 : ℝ) → ℝ → ℝ) (hφ : ∀ α, ∃ C, ∀ i, |φ α (σ i ^ 2)| ≤ C)
    (α : Set.Ioi (0 : ℝ)) : F →L[𝕜] E :=
  hs.funCalc (φ α) (hφ α) ∘L ContinuousLinearMap.adjoint K

/-- `R_α y = ∑_{n ∈ I} φ_α(σ_n²) σ_n ⟨u_n, y⟩ v_n` for `y ∈ Y`.

It holds for every `K`, `K = 0` included. -/
public theorem hasSum_spectralReg (hs : IsSingularSystem K σ v u)
    (φ : Set.Ioi (0 : ℝ) → ℝ → ℝ) (hφ : ∀ α, ∃ C, ∀ i, |φ α (σ i ^ 2)| ≤ C)
    (α : Set.Ioi (0 : ℝ)) (y : F) :
    HasSum (fun i => (((φ α (σ i ^ 2) * σ i : ℝ) : 𝕜) * inner 𝕜 (u i) y) • v i)
      (spectralReg hs φ hφ α y) := by
  have hmemperp : ContinuousLinearMap.adjoint K y ∈ (K.toLinearMap.ker)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    have hKw : K w = 0 := by simpa using hw
    rw [ContinuousLinearMap.adjoint_inner_right, hKw, inner_zero_left]
  have hker0 : K.toLinearMap.ker.starProjection
      (ContinuousLinearMap.adjoint K y) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr hmemperp
  have h1 := hs.hasSum_funCalc_sub_starProjection (hφ α) (ContinuousLinearMap.adjoint K y)
  rw [hker0, smul_zero, sub_zero] at h1
  have hfun : (fun i => ((RCLike.ofReal (φ α (σ i ^ 2)) : 𝕜) *
      inner 𝕜 (v i) (ContinuousLinearMap.adjoint K y)) • v i)
      = fun i => ((RCLike.ofReal (φ α (σ i ^ 2) * σ i) : 𝕜) * inner 𝕜 (u i) y) • v i := by
    funext i
    rw [ContinuousLinearMap.adjoint_inner_right, hs.map_left i, inner_smul_left,
      RCLike.conj_ofReal, RCLike.ofReal_mul, mul_assoc]
  rw [hfun] at h1
  exact h1

end AutoIp

end _def_spectral_reg
