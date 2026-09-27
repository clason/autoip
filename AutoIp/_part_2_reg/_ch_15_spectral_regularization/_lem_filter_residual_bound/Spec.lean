/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_filter
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_intertwine
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_y
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound

section _lem_filter_residual_bound

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Residual bound: for a regularizing filter and all `α > 0`,
`‖K R_α‖ ≤ sup_{n ∈ I} |φ_α(σ_n²)| σ_n² ≤ C_φ`.

It holds for every `K`, `K = 0` included. -/
public theorem opNorm_comp_spectralReg_le (hs : IsSingularSystem K σ v u) {φ : Set.Ioi (0 : ℝ) →
    ℝ → ℝ} {C : ℝ}
    (hφ : IsRegularizingFilter K φ C) {α : Set.Ioi (0 : ℝ)} :
    ‖K ∘L spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α‖ ≤ (⨆ i, |φ α (σ i ^ 2)| * σ i ^ 2) ∧
      (⨆ i, |φ α (σ i ^ 2)| * σ i ^ 2) ≤ C := by
  have hpt : ∀ i, |φ α (σ i ^ 2)| * σ i ^ 2 ≤ C := by
    intro i
    have hmem : σ i ^ 2 ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2) :=
      ⟨pow_pos (hs.pos i) 2, (hs.sq_mem_Icc i).2⟩
    have h := hφ.mul_abs_le α (σ i ^ 2) hmem
    linarith [h, mul_comm (σ i ^ 2) |φ α (σ i ^ 2)|]
  have hsup_le : (⨆ i, |φ α (σ i ^ 2)| * σ i ^ 2) ≤ C :=
    Real.iSup_le hpt hφ.const_pos.le
  have hsup_nonneg : (0 : ℝ) ≤ ⨆ i, |φ α (σ i ^ 2)| * σ i ^ 2 :=
    Real.iSup_nonneg (fun i => by positivity)
  refine ⟨?_, hsup_le⟩
  obtain ⟨B, hB⟩ := hφ.bddOn α
  have hbφ : ∃ c, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |φ α t| ≤ c := ⟨B, hB⟩
  have hbid : ∃ c, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |(id : ℝ → ℝ) t| ≤ c :=
    ⟨‖K‖ ^ 2, fun t ht => by simpa [abs_of_nonneg ht.1] using ht.2⟩
  have hbidsq : ∃ c, ∀ i, |id (σ i ^ 2)| ≤ c := hs.exists_bound_sq hbid
  have hbφsq : ∃ c, ∀ i, |φ α (σ i ^ 2)| ≤ c := hφ.exists_bound_on_spectrum hs α
  have hcomp : K ∘L spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α
      = hs.funCalcRight ((id : ℝ → ℝ) * φ α)
        (exists_forall_abs_mul_sq_le hbidsq hbφsq) := by
    rw [hs.funCalcRight_mul hbid hbφ, hs.funCalcRight_id hbidsq]
    ext z
    simp only [ContinuousLinearMap.comp_apply]
    rw [spectralReg_eq hs φ (hφ.exists_bound_on_spectrum hs) α,
      ContinuousLinearMap.comp_apply]
    exact congrArg K (congrArg (fun S : F →L[𝕜] E => S z) (hs.funCalc_comp_adjoint hbφsq))
  rw [hcomp]
  have hbdd : BddAbove (Set.range fun i => |φ α (σ i ^ 2)| * σ i ^ 2) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact hpt i
  have ha : ∀ i, |((id : ℝ → ℝ) * φ α) (σ i ^ 2)| ≤ ⨆ i, |φ α (σ i ^ 2)| * σ i ^ 2 := by
    intro i
    have hb1 : |((id : ℝ → ℝ) * φ α) (σ i ^ 2)| = |φ α (σ i ^ 2)| * σ i ^ 2 := by
      simp only [Pi.mul_apply, id_eq, abs_mul, abs_of_nonneg (sq_nonneg (σ i))]
      ring
    rw [hb1]
    exact le_ciSup hbdd i
  have h := hs.norm_funCalcRight_le ((id : ℝ → ℝ) * φ α) _ ha
  have h0 : |((id : ℝ → ℝ) * φ α) 0| = 0 := by simp
  rw [h0, max_eq_left hsup_nonneg] at h
  exact h

end AutoIp

end _lem_filter_residual_bound
