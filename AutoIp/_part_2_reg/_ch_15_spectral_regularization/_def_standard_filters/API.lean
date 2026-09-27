/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_standard_filters.Spec
public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_fun_calc

namespace AutoIp

open scoped InnerProductSpace

/-- The Tikhonov filter is `φ_α(λ) = (λ + α)⁻¹`. -/
public theorem tikhonovFilter_apply (α : Set.Ioi (0 : ℝ)) (lam : ℝ) :
    tikhonovFilter α lam = (lam + (α : ℝ))⁻¹ := rfl

/-- Each Tikhonov filter `φ_α` is bounded at the squared singular values `σₙ²`. -/
public theorem tikhonovFilter_exists_bound_on_spectrum {𝕜 : Type*} [RCLike 𝕜] {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [CompleteSpace F] {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E}
    {u : ι → F} (hs : IsSingularSystem K σ v u) :
    ∀ α : Set.Ioi (0 : ℝ), ∃ c, ∀ i, |tikhonovFilter α (σ i ^ 2)| ≤ c :=
  fun α => hs.exists_bound_sq ((tikhonovFilter_isRegularizingFilter K).bddOn α)

/-- For `0 < ω` and `ωκ ≤ 1`, each Landweber filter `φ_α` is bounded at the squared singular
values `σₙ²`. -/
public theorem landweberFilter_exists_bound_on_spectrum {𝕜 : Type*} [RCLike 𝕜] {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [CompleteSpace F] {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E}
    {u : ι → F} (hs : IsSingularSystem K σ v u) {ω : ℝ} (hω : 0 < ω ∧ ω * ‖K‖ ^ 2 ≤ 1) :
    ∀ α : Set.Ioi (0 : ℝ), ∃ c, ∀ i, |landweberFilter ω α (σ i ^ 2)| ≤ c :=
  fun α => hs.exists_bound_sq ((landweberFilter_isRegularizingFilter K hω).bddOn α)

/-- The Tikhonov residual in closed form: `|1 - λ φ_α(λ)| = α / (λ + α)`. -/
public theorem abs_one_sub_mul_tikhonovFilter {α : Set.Ioi (0 : ℝ)} {lam : ℝ} (hlam : 0 < lam) :
    |1 - lam * tikhonovFilter α lam| = (α : ℝ) / (lam + (α : ℝ)) := by
  have hα : (0 : ℝ) < (α : ℝ) := α.2
  have hsum : (0 : ℝ) < lam + (α : ℝ) := by linarith
  rw [tikhonovFilter_apply]
  have h : 1 - lam * (lam + (α : ℝ))⁻¹ = (α : ℝ) / (lam + (α : ℝ)) := by field_simp; ring
  rw [h, abs_of_nonneg (by positivity)]

end AutoIp
