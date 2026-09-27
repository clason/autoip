/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg.Spec
import all AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg.Spec
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_filter
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- `R_α = φ_α(K*K) K*`. -/
public theorem spectralReg_eq (hs : IsSingularSystem K σ v u)
    (φ : Set.Ioi (0 : ℝ) → ℝ → ℝ) (hφ : ∀ α, ∃ C, ∀ i, |φ α (σ i ^ 2)| ≤ C)
    (α : Set.Ioi (0 : ℝ)) :
    spectralReg hs φ hφ α = hs.funCalc (φ α) (hφ α) ∘L K.adjoint := by
  unfold spectralReg
  rfl

/-- For a regularizing filter, each `φ_α` is bounded at the squared singular values `σₙ²`. -/
public theorem IsRegularizingFilter.exists_bound_on_spectrum (hs : IsSingularSystem K σ v u)
    {φ : Set.Ioi (0 : ℝ) → ℝ → ℝ} {C : ℝ} (hφ : IsRegularizingFilter K φ C) :
    ∀ α, ∃ c, ∀ i, |φ α (σ i ^ 2)| ≤ c :=
  fun α => hs.exists_bound_sq (hφ.bddOn α)

/-- For a regularizing filter, `|1 - σₙ² φ_α(σₙ²)| ≤ 1 + C_φ` for every index `n`. -/
public theorem IsRegularizingFilter.exists_bound_residual {φ : Set.Ioi (0 : ℝ) → ℝ → ℝ}
    {C : ℝ}
    (hφ : IsRegularizingFilter K φ C) (hs : IsSingularSystem K σ v u)
    (α : Set.Ioi (0 : ℝ)) :
    ∃ c, ∀ i, |(fun lam => 1 - lam * φ α lam) (σ i ^ 2)| ≤ c := by
  refine ⟨1 + C, fun i => ?_⟩
  have hmem : σ i ^ 2 ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2) :=
    ⟨pow_pos (hs.pos i) 2, (hs.sq_mem_Icc i).2⟩
  have h := hφ.mul_abs_le α (σ i ^ 2) hmem
  have habs : |σ i ^ 2 * φ α (σ i ^ 2)| ≤ C := by
    rw [abs_mul, abs_of_pos hmem.1]
    exact h
  rw [abs_le] at habs
  simp only
  rw [abs_le]
  constructor <;> linarith [habs.1, habs.2]

end AutoIp
