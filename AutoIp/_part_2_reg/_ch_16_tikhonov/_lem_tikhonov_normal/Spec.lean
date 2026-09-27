/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_standard_filters
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_basic
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_hom

section _lem_tikhonov_normal

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Tikhonov solves a regularised normal equation: for `y ∈ Y`, `α > 0` and `x ∈ X`,
`x = R_α y` if and only if `(K*K + α Id) x = K* y`.

It holds for every `K`, `K = 0` included. -/
public theorem tikhonov_iff_normal (hs : IsSingularSystem K σ v u) {α : Set.Ioi (0 : ℝ)} (y : F)
    (x : E) :
    x = spectralReg hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) α y ↔
      (K.adjoint ∘L K +
          ((α : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E) x =
        K.adjoint y := by
  have hα : (0 : ℝ) < (α : ℝ) := α.2
  have hbT : ∃ c, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |tikhonovFilter α t| ≤ c :=
    (tikhonovFilter_isRegularizingFilter K).bddOn α
  have hbid : ∃ c, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |(id : ℝ → ℝ) t| ≤ c :=
    ⟨‖K‖ ^ 2, fun t ht => by simpa [abs_of_nonneg ht.1] using ht.2⟩
  have hbone : ∃ c, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |(fun _ => (1 : ℝ)) t| ≤ c :=
    ⟨1, fun t _ => by simp⟩
  have hbconst : ∃ c, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2),
      |((α : ℝ) • (fun _ => (1 : ℝ)) : ℝ → ℝ) t| ≤ c := ⟨|(α : ℝ)|, fun t _ => by simp⟩
  have hbsum : ∃ c, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2),
      |((id : ℝ → ℝ) + (α : ℝ) • (fun _ => (1 : ℝ)) : ℝ → ℝ) t| ≤ c :=
    ⟨‖K‖ ^ 2 + (α : ℝ), fun t ht => by
      simp only [Pi.add_apply, id_eq, Pi.smul_apply, smul_eq_mul, mul_one]
      rw [abs_of_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ t + (α : ℝ))]
      linarith [ht.2]⟩
  have hbTsq := tikhonovFilter_exists_bound_on_spectrum hs α
  have hbsumsq := hs.exists_bound_sq hbsum
  have hbonesq := hs.exists_bound_sq hbone
  have hAeq : ContinuousLinearMap.adjoint K ∘L K +
        (RCLike.ofReal (α : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E
      = hs.funCalc ((id : ℝ → ℝ) + (α : ℝ) • (fun _ => (1 : ℝ))) hbsumsq := by
    rw [hs.funCalc_add hbid hbconst, hs.funCalc_id (hs.exists_bound_sq hbid),
      hs.funCalc_smul (α : ℝ) hbone, hs.funCalc_one hbonesq]
  have hgeq : hs.funCalc (((id : ℝ → ℝ) + (α : ℝ) • (fun _ => (1 : ℝ))) * tikhonovFilter α)
        (exists_forall_abs_mul_sq_le hbsumsq hbTsq)
      = ContinuousLinearMap.id 𝕜 E := by
    rw [hs.funCalc_congr _ (ψ := fun _ => (1 : ℝ)) hbonesq ?_, hs.funCalc_one hbonesq]
    intro t ht
    have h : 0 < t + (α : ℝ) := by linarith [ht.1]
    simp only [Pi.mul_apply, Pi.add_apply, id_eq, Pi.smul_apply, smul_eq_mul, mul_one,
      tikhonovFilter]
    exact mul_inv_cancel₀ h.ne'
  have hAT : (ContinuousLinearMap.adjoint K ∘L K +
        (RCLike.ofReal (α : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E) ∘L
      hs.funCalc (tikhonovFilter α) hbTsq = ContinuousLinearMap.id 𝕜 E := by
    rw [hAeq, ← hs.funCalc_mul hbsum hbT]; exact hgeq
  have hTA : hs.funCalc (tikhonovFilter α) hbTsq ∘L
      (ContinuousLinearMap.adjoint K ∘L K +
        (RCLike.ofReal (α : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E) = ContinuousLinearMap.id 𝕜 E := by
    rw [hAeq, ← hs.funCalc_mul hbT hbsum]
    refine Eq.trans ?_ hgeq
    exact hs.funCalc_congr _ _ fun t _ => mul_comm _ _
  constructor
  · rintro rfl
    have h := congrArg (fun S : E →L[𝕜] E => S (ContinuousLinearMap.adjoint K y)) hAT
    rw [spectralReg_eq hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) α]
    simpa using h
  · intro h
    have h2 := congrArg (fun z : E => hs.funCalc (tikhonovFilter α) hbTsq z) h
    rw [← ContinuousLinearMap.comp_apply, hTA] at h2
    rw [spectralReg_eq hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) α]
    simpa using h2

end AutoIp

end _lem_tikhonov_normal
