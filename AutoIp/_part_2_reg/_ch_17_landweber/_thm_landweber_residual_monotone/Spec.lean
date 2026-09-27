/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_17_landweber._def_landweber
import AutoIp.Auxiliary.StepSize
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import AutoIp._part_2_reg._ch_17_landweber._thm_landweber_residual_monotone.Helpers

section _thm_landweber_residual_monotone

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F}

/-- With `x₀ = 0`, the hypothesis `K*(K x^δ_m - y^δ) ≠ 0` is equivalent to
`y^δ ∉ Ker(K*)`, for the datum `y^δ = z` and every `m`.

The step size `ω ∈ (0, κ⁻¹)` is stated as `0 < ω` and `ωκ < 1`, which is the same for `K ≠ 0` and,
unlike the interval, makes no use of `0⁻¹`. It holds for every `K`, `K = 0` included. -/
public theorem landweber_adjoint_residual_ne_zero_iff (K : E →L[𝕜] F) {ω : ℝ}
    (hω : 0 < ω ∧ ω * ‖K‖ ^ 2 < 1) (z : F) (m : ℕ) :
    K.adjoint (K (landweber K ω z m) - z) ≠ 0 ↔
      K.adjoint z ≠ 0 := by
  have hinj := injective_id_sub_smul_adjoint_comp_self K hω
  induction m with
  | zero => simp [landweber_zero]
  | succ m ih =>
    rw [landweber_adjoint_residual_succ, ne_eq, map_eq_zero_iff _ hinj, ← ne_eq]
    exact ih

/-- The residual decreases strictly: if `K*(K x^δ_m - y^δ) ≠ 0`, then
`‖K x^δ_{m+1} - y^δ‖ < ‖K x^δ_m - y^δ‖`, for the datum `y^δ = z`.

The step size `ω ∈ (0, κ⁻¹)` is stated as `0 < ω` and `ωκ < 1`, which is the same for `K ≠ 0` and,
unlike the interval, makes no use of `0⁻¹`. It holds for every `K`, `K = 0` included. -/
public theorem landweber_residual_lt (K : E →L[𝕜] F) {ω : ℝ}
    (hω : 0 < ω ∧ ω * ‖K‖ ^ 2 < 1) (z : F) (m : ℕ)
    (hne : K.adjoint (K (landweber K ω z m) - z) ≠ 0) :
    ‖K (landweber K ω z (m + 1)) - z‖ < ‖K (landweber K ω z m) - z‖ := by
  obtain ⟨hω0, hωKlt⟩ := hω
  have hωK : ω * ‖K‖ ^ 2 ≤ 1 := hωKlt.le
  set r : F := z - K (landweber K ω z m) with hrdef
  have hrne : ContinuousLinearMap.adjoint K r ≠ 0 := by
    intro h0
    apply hne
    have : K (landweber K ω z m) - z = -r := by rw [hrdef]; abel
    rw [this, map_neg, h0, neg_zero]
  have hstep : K (landweber K ω z (m + 1)) - z =
      -(r - (RCLike.ofReal ω : 𝕜) • K (ContinuousLinearMap.adjoint K r)) := by
    have hrec : landweber K ω z (m + 1) = landweber K ω z m +
        (RCLike.ofReal ω : 𝕜) • ContinuousLinearMap.adjoint K r := by
      rw [landweber_succ, hrdef]
    rw [hrec, map_add, map_smul, hrdef]
    abel
  have hnr : ‖r‖ = ‖K (landweber K ω z m) - z‖ := by rw [hrdef, norm_sub_rev]
  rw [hstep, norm_neg, ← hnr]
  have h := sq_norm_sub_smul_apply_adjoint_le K hω0 hωK r
  have hpos : 0 < ω * ‖ContinuousLinearMap.adjoint K r‖ ^ 2 := by
    have hn : 0 < ‖ContinuousLinearMap.adjoint K r‖ := norm_pos_iff.mpr hrne
    positivity
  have h2 : ‖r - (RCLike.ofReal ω : 𝕜) • K (ContinuousLinearMap.adjoint K r)‖ ^ 2 < ‖r‖ ^ 2 := by
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg r) h2

/-- If `closure (Ran K) = Y`, the hypothesis `K*(K x^δ_m - y^δ) ≠ 0` reduces to `y^δ ≠ 0`,
for the datum `y^δ = z` and every `m`.

The step size `ω ∈ (0, κ⁻¹)` is stated as `0 < ω` and `ωκ < 1`, which is the same for `K ≠ 0` and,
unlike the interval, makes no use of `0⁻¹`. It holds for every `K`, `K = 0` included. -/
public theorem landweber_adjoint_residual_ne_zero_iff_of_dense (K : E →L[𝕜] F) {ω : ℝ}
    (hω : 0 < ω ∧ ω * ‖K‖ ^ 2 < 1)
    (hdense : K.toLinearMap.range.topologicalClosure = ⊤) (z : F) (m : ℕ) :
    K.adjoint (K (landweber K ω z m) - z) ≠ 0 ↔ z ≠ 0 := by
  rw [landweber_adjoint_residual_ne_zero_iff K hω z m]
  have hker : (ContinuousLinearMap.adjoint K).toLinearMap.ker = ⊥ := by
    have h := Submodule.topologicalClosure_eq_top_iff.mp hdense
    rwa [show K.toLinearMap.range = K.range from rfl,
      ContinuousLinearMap.orthogonal_range] at h
  constructor
  · intro h hz
    exact h (by rw [hz, map_zero])
  · intro hz h
    have hmem : z ∈ (ContinuousLinearMap.adjoint K).toLinearMap.ker := h
    rw [hker, Submodule.mem_bot] at hmem
    exact hz hmem

end AutoIp

end _thm_landweber_residual_monotone
