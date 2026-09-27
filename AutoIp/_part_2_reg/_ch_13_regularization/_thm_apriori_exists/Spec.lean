/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_13_regularization._def_parameter_choice
public import AutoIp._part_2_reg._ch_13_regularization._def_regularization
import AutoIp._part_2_reg._ch_13_regularization._thm_apriori_characterisation
import AutoIp._part_2_reg._ch_13_regularization._thm_apriori_exists.Helpers
import Mathlib.Topology.Order.AtTopBotIxx

section _thm_apriori_exists

namespace AutoIp

open Filter Topology
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Every regularization `{R_α}` of `T†` admits an a priori rule `α` such that `(R_α, α)` is a
convergent regularization method. -/
public theorem exists_apriori_isRegularizationMethod {T : E →L[𝕜] F}
    {R : Set.Ioi (0 : ℝ) → F →L[𝕜] E} (hR : IsRegularization T R) :
    ∃ a : ParameterChoice F, a.IsAPriori ∧ IsRegularizationMethod T (fun α w => R α w) a := by
  classical
  obtain ⟨e, hepos, heanti, hesmall, hebound⟩ :=
    exists_antitone_scale
      (fun m => ‖R ⟨1 / ((m : ℝ) + 1), Set.mem_Ioi.2 (by positivity)⟩‖) fun _ => norm_nonneg _
  obtain ⟨nn, hnn1, hnn2⟩ := exists_index_of_antitone_scale heanti hesmall
  obtain ⟨A, hA0, hAdata⟩ :
      ∃ A : ℝ → Set.Ioi (0 : ℝ),
        Tendsto (fun δ => (A δ : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
        Tendsto (fun δ => δ * ‖R (A δ)‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine ⟨fun δ => ⟨1 / ((nn δ : ℝ) + 1), Set.mem_Ioi.2 (by positivity)⟩, ?_, ?_⟩
    · rw [Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
      refine ⟨e N, hepos N, ?_⟩
      intro δ hδs hdd
      have hδpos : (0 : ℝ) < δ := hδs
      have hδlt : δ < e N := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hδpos] at hdd; exact hdd
      have hNn : N ≤ nn δ := hnn1 δ N hδpos hδlt
      have hcast : (N : ℝ) ≤ (nn δ : ℝ) := Nat.cast_le.mpr hNn
      have hb : 1 / ((nn δ : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
      linarith
    · rw [Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
      refine ⟨min (e 0) (e N), lt_min (hepos 0) (hepos N), ?_⟩
      intro δ hδs hdd
      have hδpos : (0 : ℝ) < δ := hδs
      have hdlt : δ < min (e 0) (e N) := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hδpos] at hdd; exact hdd
      have h0lt : δ < e 0 := lt_of_lt_of_le hdlt (min_le_left _ _)
      have hNlt : δ < e N := lt_of_lt_of_le hdlt (min_le_right _ _)
      have hNn : N ≤ nn δ := hnn1 δ N hδpos hNlt
      have hcast : (N : ℝ) ≤ (nn δ : ℝ) := Nat.cast_le.mpr hNn
      have hkey : δ < e (nn δ) := hnn2 δ hδpos h0lt
      have hstep : δ * ‖R ⟨1 / ((nn δ : ℝ) + 1), Set.mem_Ioi.2 (by positivity)⟩‖
          ≤ 1 / ((nn δ : ℝ) + 1) :=
        le_trans (mul_le_mul_of_nonneg_right hkey.le (norm_nonneg _)) (hebound (nn δ))
      have hb : 1 / ((nn δ : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (mul_nonneg hδpos.le (norm_nonneg _))]
      linarith
  set a : ParameterChoice F := ⟨fun δ _ => (A δ : ℝ), fun δ _ => (A δ).2⟩ with hadef
  have hval : ∀ (δ : Set.Ioi (0 : ℝ)) (y : F), a δ y = (A (δ : ℝ) : ℝ) := fun _ _ => rfl
  have hparam : ∀ (δ : Set.Ioi (0 : ℝ)) (y : F), a.param δ y = A (δ : ℝ) := fun _ _ => rfl
  refine ⟨a, ?_, ?_⟩
  · intro δ y z
    rw [hval δ, hval δ]
  · have hcoe : Tendsto ((↑) : Set.Ioi (0 : ℝ) → ℝ) atBot (𝓝[>] (0 : ℝ)) :=
      (map_coe_Ioi_atBot (0 : ℝ)).le
    refine isRegularizationMethod_of_apriori hR (fun δ y z => by rw [hval δ, hval δ])
      (fun y => ?_) (fun y => ?_)
    · exact (hA0.comp hcoe).congr fun δ => by simp only [Function.comp_apply, hval δ y]
    · exact (hAdata.comp hcoe).congr fun δ => by
        simp only [Function.comp_apply, hparam δ y]

end AutoIp

end _thm_apriori_exists
