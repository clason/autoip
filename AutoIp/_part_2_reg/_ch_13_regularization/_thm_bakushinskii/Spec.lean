/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_13_regularization._def_parameter_choice
import AutoIp._part_2_reg._ch_11_moore_penrose._thm_mp_inverse

section _thm_bakushinskii

namespace AutoIp

open Filter Topology
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Bakushinskiĭ veto: if `{R_α}` is any family of maps `Y → X` and `α` a heuristic rule such
that `(R_α, α)` satisfies the limit of a convergent regularization method, then `T†` is
bounded. -/
public theorem exists_norm_moorePenrose_le_of_heuristic {T : E →L[𝕜] F}
    (R : Set.Ioi (0 : ℝ) → F → E)
    (a : ParameterChoice F)
    (hheur : a.IsHeuristic) (hconv : IsRegularizationMethod T R a) :
    ∃ C : ℝ, ∀ y : (moorePenrose T).domain, ‖moorePenrose T y‖ ≤ C * ‖(y : F)‖ := by
  have hstep1 : ∀ w, ∀ hw : w ∈ mpDomain T, ∀ (δ : ℝ) (hδ : 0 < δ),
      R (a.param ⟨δ, hδ⟩ w) w = moorePenrose T ⟨w, hw⟩ := by
    intro w hw δ hδ
    have hz : ‖R (a.param ⟨δ, hδ⟩ w) w - moorePenrose T ⟨w, hw⟩‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖R (a.param ⟨δ, hδ⟩ w) w - moorePenrose T ⟨w, hw⟩‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      obtain ⟨δ₀, hδ₀, hb⟩ := hconv w hw _ hpos
      have h1 := hb (δ₀ / 2) ⟨by linarith, by linarith⟩ w
        (by simp only [sub_self, norm_zero]; linarith)
      rw [a.param_congr (hheur ⟨δ₀ / 2, Set.mem_Ioi.2 (by linarith)⟩ ⟨δ, hδ⟩ w)] at h1
      exact lt_irrefl _ h1
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  have hzero : (0 : F) ∈ mpDomain T := Submodule.zero_mem _
  have hmp0 : moorePenrose T ⟨(0 : F), hzero⟩ = 0 := moorePenrose_zero
  obtain ⟨d, hdpos, hkey⟩ :
      ∃ d : ℝ, 0 < d ∧ ∀ w, ∀ hw : w ∈ mpDomain T, ‖w‖ ≤ d → ‖moorePenrose T ⟨w, hw⟩‖ ≤ 1 := by
    obtain ⟨δ₀, hδ₀, hb⟩ := hconv 0 hzero 1 one_pos
    refine ⟨δ₀ / 2, by linarith, ?_⟩
    intro w hw hwn
    have h1 := hb (δ₀ / 2) ⟨by linarith, by linarith⟩ w (by simpa using hwn)
    rw [hmp0, sub_zero, hstep1 w hw (δ₀ / 2) (by linarith)] at h1
    exact h1.le
  refine ⟨1 / d, ?_⟩
  rintro ⟨w, hw⟩
  change ‖moorePenrose T ⟨w, hw⟩‖ ≤ 1 / d * ‖w‖
  rcases eq_or_ne w 0 with rfl | hwne
  · simp [hmp0]
  · have hwn : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hwne
    have ht : (0 : ℝ) < d / ‖w‖ := by positivity
    have hmem : ((d / ‖w‖ : ℝ) : 𝕜) • w ∈ mpDomain T := Submodule.smul_mem _ _ hw
    have hnz : ‖((d / ‖w‖ : ℝ) : 𝕜) • w‖ = d := by
      rw [norm_smul, RCLike.norm_ofReal, abs_of_pos ht]
      field_simp
    have hk := hkey _ hmem hnz.le
    rw [show (⟨((d / ‖w‖ : ℝ) : 𝕜) • w, hmem⟩ : (moorePenrose T).domain)
        = ((d / ‖w‖ : ℝ) : 𝕜) • ⟨w, hw⟩ from rfl,
      (moorePenrose T).map_smul, norm_smul, RCLike.norm_ofReal, abs_of_pos ht] at hk
    rw [div_mul_eq_mul_div, div_le_iff₀ hwn] at hk
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hdpos]
    have hcomm : ‖moorePenrose T ⟨w, hw⟩‖ * d = d * ‖moorePenrose T ⟨w, hw⟩‖ := mul_comm _ _
    linarith

end AutoIp

end _thm_bakushinskii
