/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_standard_filters
import AutoIp._part_1_funcanal._ch_03_hilbert_spaces._prop_adjoint_props
import AutoIp._part_2_reg._ch_16_tikhonov._lem_tikhonov_normal
import AutoIp.Auxiliary.Rpow

section _lem_tikhonov_operator_perturbation

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K Kh : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F} {ι' : Type*}
variable {σ' : ι' → ℝ} {v' : ι' → E} {u' : ι' → F}

/-- Perturbation bound for the Tikhonov operator: for `‖K - K_h‖ ≤ h` and every `α > 0`,
`‖R_α[K_h] - R_α[K]‖ ≤ h/α + h (2‖K‖ + h) / (2 α^(3/2))`, with `R_α` built from the Tikhonov
filter. -/
public theorem opNorm_tikhonov_perturbed_sub_le (hs : IsSingularSystem K σ v u)
    (hsh : IsSingularSystem Kh σ' v' u') {h : ℝ} {α : Set.Ioi (0 : ℝ)} (hh : ‖K - Kh‖ ≤ h) :
    ‖spectralReg hsh tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum
        hsh) α - spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) α‖ ≤
      h / (α : ℝ) + h * (2 * ‖K‖ + h) / (2 * (α : ℝ) ^ ((3 : ℝ) / 2)) := by
  have hα : (0 : ℝ) < (α : ℝ) := α.2
  have hh0 : (0 : ℝ) ≤ h := le_trans (norm_nonneg _) hh
  have hsq0 : 0 < Real.sqrt (α : ℝ) := Real.sqrt_pos.mpr hα
  have hsqsq : Real.sqrt (α : ℝ) * Real.sqrt (α : ℝ) = (α : ℝ) := Real.mul_self_sqrt hα.le
  have hα32 := rpow_three_halves hα
  have hlow : ∀ (L : E →L[𝕜] F) (x : E), (α : ℝ) * ‖x‖ ≤
      ‖(ContinuousLinearMap.adjoint L ∘L L +
        (RCLike.ofReal (α : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E) x‖ := by
    intro L x
    set A : E →L[𝕜] E := ContinuousLinearMap.adjoint L ∘L L +
      (RCLike.ofReal (α : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E with hAdef
    have hik : (inner 𝕜 x (A x) : 𝕜)
        = (RCLike.ofReal (‖L x‖ ^ 2 + (α : ℝ) * ‖x‖ ^ 2) : 𝕜) := by
      simp only [hAdef, add_apply, ContinuousLinearMap.comp_apply,
        smul_apply, ContinuousLinearMap.id_apply, inner_add_right,
        inner_smul_right, ContinuousLinearMap.adjoint_inner_right,
        inner_self_eq_norm_sq_to_K, RCLike.ofReal_add, RCLike.ofReal_mul, RCLike.ofReal_pow]
    have h1 : ‖L x‖ ^ 2 + (α : ℝ) * ‖x‖ ^ 2 ≤ ‖x‖ * ‖A x‖ := by
      have h2 := re_inner_le_norm (𝕜 := 𝕜) x (A x)
      rwa [hik, RCLike.ofReal_re] at h2
    rcases eq_or_lt_of_le (norm_nonneg x) with hx | hx
    · have hx0 : x = 0 := by rw [← norm_eq_zero]; exact hx.symm
      simp [hx0]
    · nlinarith [sq_nonneg ‖L x‖, norm_nonneg (A x)]
  have hKh : ‖Kh‖ ≤ ‖K‖ + h := by
    calc ‖Kh‖ = ‖K - (K - Kh)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖K‖ + ‖K - Kh‖ := norm_sub_le _ _
      _ ≤ ‖K‖ + h := by linarith
  have hdiff : ContinuousLinearMap.adjoint K ∘L K - ContinuousLinearMap.adjoint Kh ∘L Kh
      = ContinuousLinearMap.adjoint K ∘L (K - Kh)
        + ContinuousLinearMap.adjoint (K - Kh) ∘L Kh := by
    rw [map_sub]
    ext x
    simp only [
      add_apply, sub_apply,
      ContinuousLinearMap.comp_apply, map_sub]
    abel
  have hAAh : ‖ContinuousLinearMap.adjoint K ∘L K - ContinuousLinearMap.adjoint Kh ∘L Kh‖
      ≤ h * (2 * ‖K‖ + h) := by
    rw [hdiff]
    have h1 : ‖ContinuousLinearMap.adjoint K ∘L (K - Kh)‖ ≤ ‖K‖ * h := by
      calc ‖ContinuousLinearMap.adjoint K ∘L (K - Kh)‖
          ≤ ‖ContinuousLinearMap.adjoint K‖ * ‖K - Kh‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ = ‖K‖ * ‖K - Kh‖ := by rw [ContinuousLinearMap.norm_adjoint]
        _ ≤ ‖K‖ * h := by gcongr
    have h2 : ‖ContinuousLinearMap.adjoint (K - Kh) ∘L Kh‖ ≤ h * (‖K‖ + h) := by
      calc ‖ContinuousLinearMap.adjoint (K - Kh) ∘L Kh‖
          ≤ ‖ContinuousLinearMap.adjoint (K - Kh)‖ * ‖Kh‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ = ‖K - Kh‖ * ‖Kh‖ := by rw [ContinuousLinearMap.norm_adjoint]
        _ ≤ h * (‖K‖ + h) := by
            refine mul_le_mul hh hKh (norm_nonneg _) hh0
    calc ‖ContinuousLinearMap.adjoint K ∘L (K - Kh)
            + ContinuousLinearMap.adjoint (K - Kh) ∘L Kh‖
        ≤ ‖ContinuousLinearMap.adjoint K ∘L (K - Kh)‖
            + ‖ContinuousLinearMap.adjoint (K - Kh) ∘L Kh‖ := norm_add_le _ _
      _ ≤ ‖K‖ * h + h * (‖K‖ + h) := by linarith
      _ = h * (2 * ‖K‖ + h) := by ring
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  have hnh : (ContinuousLinearMap.adjoint Kh ∘L Kh +
        (RCLike.ofReal (α : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E)
      (spectralReg hsh tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hsh) α
          y) = ContinuousLinearMap.adjoint Kh y :=
    (tikhonov_iff_normal hsh y _).mp rfl
  have hn : (ContinuousLinearMap.adjoint K ∘L K +
        (RCLike.ofReal (α : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E)
      (spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) α
          y) = ContinuousLinearMap.adjoint K y :=
    (tikhonov_iff_normal hs y _).mp rfl
  set xh := spectralReg hsh tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum
      hsh) α y with hxhdef
  set x := spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) α y with hxdef
  have hAw : (ContinuousLinearMap.adjoint K ∘L K +
        (RCLike.ofReal (α : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E) (xh - x)
      = (ContinuousLinearMap.adjoint K ∘L K - ContinuousLinearMap.adjoint Kh ∘L Kh) xh
        + (ContinuousLinearMap.adjoint Kh y - ContinuousLinearMap.adjoint K y) := by
    have e1 : (ContinuousLinearMap.adjoint K ∘L K +
          (RCLike.ofReal (α : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E) xh
        = (ContinuousLinearMap.adjoint K ∘L K - ContinuousLinearMap.adjoint Kh ∘L Kh) xh
          + (ContinuousLinearMap.adjoint Kh ∘L Kh +
              (RCLike.ofReal (α : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E) xh := by
      simp only [add_apply, sub_apply,
        ContinuousLinearMap.comp_apply, smul_apply,
        ContinuousLinearMap.id_apply]
      abel
    rw [map_sub, e1, hnh, hn]
    abel
  have hb1 : ‖(ContinuousLinearMap.adjoint K ∘L K
      - ContinuousLinearMap.adjoint Kh ∘L Kh) xh‖
      ≤ h * (2 * ‖K‖ + h) * (‖y‖ / (2 * Real.sqrt (α : ℝ))) := by
    calc ‖(ContinuousLinearMap.adjoint K ∘L K
          - ContinuousLinearMap.adjoint Kh ∘L Kh) xh‖
        ≤ ‖ContinuousLinearMap.adjoint K ∘L K
            - ContinuousLinearMap.adjoint Kh ∘L Kh‖ * ‖xh‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ h * (2 * ‖K‖ + h) * (‖y‖ / (2 * Real.sqrt (α : ℝ))) :=
          mul_le_mul hAAh (norm_spectralReg_tikhonov_le hsh y) (norm_nonneg _) (by positivity)
  have hb2 : ‖ContinuousLinearMap.adjoint Kh y - ContinuousLinearMap.adjoint K y‖
      ≤ h * ‖y‖ := by
    have e : ContinuousLinearMap.adjoint Kh y - ContinuousLinearMap.adjoint K y
        = ContinuousLinearMap.adjoint (Kh - K) y := by
      simp [map_sub]
    rw [e]
    calc ‖ContinuousLinearMap.adjoint (Kh - K) y‖
        ≤ ‖ContinuousLinearMap.adjoint (Kh - K)‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖K - Kh‖ * ‖y‖ := by rw [ContinuousLinearMap.norm_adjoint, norm_sub_rev]
      _ ≤ h * ‖y‖ := by gcongr
  have hAnorm : ‖(ContinuousLinearMap.adjoint K ∘L K +
        (RCLike.ofReal (α : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E) (xh - x)‖
      ≤ h * (2 * ‖K‖ + h) * (‖y‖ / (2 * Real.sqrt (α : ℝ))) + h * ‖y‖ := by
    rw [hAw]
    exact le_trans (norm_add_le _ _) (by linarith)
  have hfinal := hlow K (xh - x)
  have hle : ‖xh - x‖
      ≤ (h * (2 * ‖K‖ + h) * (‖y‖ / (2 * Real.sqrt (α : ℝ))) + h * ‖y‖) / (α : ℝ) := by
    rw [le_div_iff₀ hα]
    linarith
  rw [sub_apply, ← hxhdef, ← hxdef, hα32]
  refine hle.trans (le_of_eq ?_)
  field_simp
  ring

end AutoIp

end _lem_tikhonov_operator_perturbation
