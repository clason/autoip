/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_approx_error_spectral.Spec
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_basic
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_bounded
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_hom
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- If `x† = K† y = |K|^ν w` and `|1 - λ φ_α(λ)| ≤ B` on `[0, κ]`, then
`x† - R_α y = |K|^ν ξ` for some `ξ` with `‖ξ‖ ≤ B ‖w‖`. -/
public theorem exists_norm_le_and_sub_eq_absRpow (hs : IsSingularSystem K σ v u)
    {φ : Set.Ioi (0 : ℝ) → ℝ → ℝ} {Cφ : ℝ} (hφ : IsRegularizingFilter K φ Cφ) {B : ℝ} (hB1 : 1 ≤ B)
    (hBub : ∀ (b : Set.Ioi (0 : ℝ)), ∀ s ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2),
      |1 - s * φ b s| ≤ B)
    {ν : ℝ} (hν0 : 0 < ν) {α : Set.Ioi (0 : ℝ)}
    {y : F} (hymem : y ∈ mpDomain K) {w : E}
    (hw : hs.absRpow ν hν0.le w = moorePenrose K ⟨y, hymem⟩) :
    ∃ ξ : E, ‖ξ‖ ≤ B * ‖w‖ ∧
      moorePenrose K ⟨y, hymem⟩ - spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y
        = hs.absRpow ν hν0.le ξ := by
  have hB0 : (0 : ℝ) ≤ B := by linarith
  have hbr : ∃ C, ∀ s ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2),
      |(fun lam => 1 - lam * φ α lam) s| ≤ C := ⟨B, hBub α⟩
  have hbψ : ∃ C, ∀ s ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |(fun s : ℝ => s ^ (ν / 2)) s| ≤ C :=
    ⟨(‖K‖ ^ 2) ^ (ν / 2), fun s hsm => by
      simp only
      rw [abs_of_nonneg (Real.rpow_nonneg hsm.1 _)]
      exact Real.rpow_le_rpow hsm.1 hsm.2 (by positivity)⟩
  have hbrsq := hs.exists_bound_sq hbr
  have hbψsq := hs.exists_bound_sq hbψ
  refine ⟨hs.funCalc (fun lam => 1 - lam * φ α lam) hbrsq w, ?_, ?_⟩
  · have hop := hs.norm_funCalc_le (fun lam => 1 - lam * φ α lam) B
      (fun i => hBub α _ (hs.sq_mem_Icc i))
    have h0 : |(fun lam => 1 - lam * φ α lam) (0 : ℝ)| = 1 := by
      norm_num
    rw [h0, max_eq_left hB1] at hop
    exact le_trans ((hs.funCalc (fun lam => 1 - lam * φ α lam) hbrsq).le_opNorm w)
      (mul_le_mul_of_nonneg_right hop (norm_nonneg _))
  · have hcomm : hs.funCalc (fun lam => 1 - lam * φ α lam) hbrsq (hs.absRpow ν hν0.le w)
        = hs.absRpow ν hν0.le (hs.funCalc (fun lam => 1 - lam * φ α lam) hbrsq w) := by
      have e : hs.funCalc (fun lam => 1 - lam * φ α lam) hbrsq ∘L
            hs.funCalc (fun s : ℝ => s ^ (ν / 2)) hbψsq
          = hs.funCalc (fun s : ℝ => s ^ (ν / 2)) hbψsq ∘L
            hs.funCalc (fun lam => 1 - lam * φ α lam) hbrsq := by
        rw [← hs.funCalc_mul' hbrsq hbψsq, ← hs.funCalc_mul' hbψsq hbrsq]
        exact hs.funCalc_congr _ _ fun t _ => mul_comm _ _
      rw [hs.absRpow_def ν hν0.le hbψsq]
      exact congrArg (fun T : E →L[𝕜] E => T w) e
    obtain ⟨h1, -⟩ := moorePenrose_sub_spectralReg_eq_funCalc (α := α) hs hφ hymem
    rw [h1, ← hw, hcomm]

end AutoIp
