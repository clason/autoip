/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_19_general_source_conditions._def_general_source
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_bounded
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_hom
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound

section _lem_source_monotone

section

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Monotonicity of the source sets: for index functions `φ, ψ` on `[0, κ]` and `c > 0` with
`φ(λ) ≤ c ψ(λ)` for every `λ ∈ (0, κ]`, `X_{φ,ρ} ⊆ X_{ψ,cρ}` for every `ρ > 0`. -/
public theorem sourceSetIndex_mono_index (hs : IsSingularSystem K σ v u) {φ ψ : ℝ → ℝ} {c ρ : ℝ}
    (hφ : IsIndexFunction (‖K‖ ^ 2) φ) (hψ : IsIndexFunction (‖K‖ ^ 2) ψ)
    (hc : 0 < c) (hρ : 0 < ρ)
    (hle : ∀ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), φ lam ≤ c * ψ lam) :
    sourceSetIndex hs φ (hφ.exists_bound_on_spectrum hs) ρ hρ
      ⊆ sourceSetIndex hs ψ (hψ.exists_bound_on_spectrum hs) (c * ρ) (by positivity) :=
  by
  have hc : (0 : ℝ) ≤ c := hc.le
  have hk0 : (0:ℝ) ≤ ‖K‖ ^ 2 := by positivity
  have hkmem : (‖K‖ ^ 2) ∈ Set.Icc (0:ℝ) (‖K‖ ^ 2) := ⟨hk0, le_rfl⟩
  have h0mem : (0:ℝ) ∈ Set.Icc (0:ℝ) (‖K‖ ^ 2) := ⟨le_rfl, hk0⟩
  have hpsipos : ∀ lam ∈ Set.Ioc (0:ℝ) (‖K‖ ^ 2), 0 < ψ lam := by
    intro lam hlam
    have h := hψ.strictMonoOn h0mem ⟨hlam.1.le, hlam.2⟩ hlam.1
    rwa [hψ.map_zero] at h
  set h : ℝ → ℝ := fun lam => if lam ≤ 0 then 0 else φ lam / ψ lam with hhdef
  have hh0 : h 0 = 0 := by simp only [hhdef]; rw [ite_eq_left le_rfl]
  have hhval : ∀ s : ℝ, 0 < s → h s = φ s / ψ s := by
    intro s hs
    simp only [hhdef]
    rw [ite_eq_right (not_le.mpr hs)]
  have hhb : ∀ t ∈ Set.Icc (0:ℝ) (‖K‖ ^ 2), |h t| ≤ c := by
    intro t ht
    rcases ht.1.eq_or_lt with h0 | h0
    · have htz : t = 0 := h0.symm
      subst htz
      rw [hh0, abs_zero]
      exact hc
    · have hp := hpsipos t ⟨h0, ht.2⟩
      rw [hhval t h0, abs_of_nonneg (div_nonneg (hφ.nonneg t ht) hp.le), div_le_iff₀ hp]
      exact hle t ⟨h0, ht.2⟩
  intro x hx
  simp only [mem_sourceSetIndex_iff] at hx ⊢
  obtain ⟨w, hw, rfl⟩ := hx
  have hb : ∀ i, |h (σ i ^ 2)| ≤ c := fun i => hhb _ (hs.sq_mem_Icc i)
  have hbh : ∃ C, ∀ i, |h (σ i ^ 2)| ≤ C := ⟨c, hb⟩
  refine ⟨hs.funCalc h hbh w, ?_, ?_⟩
  · have hn := hs.norm_funCalc_le h c hb
    rw [hh0, abs_zero, max_eq_left hc] at hn
    calc ‖hs.funCalc h hbh w‖ ≤ ‖hs.funCalc h hbh‖ * ‖w‖ := (hs.funCalc h hbh).le_opNorm w
      _ ≤ c * ρ := mul_le_mul hn hw (norm_nonneg w) hc
  · have heq : hs.funCalc (ψ * h)
        (exists_forall_abs_mul_sq_le (hψ.exists_bound_on_spectrum hs) hbh)
        = hs.funCalc φ (hφ.exists_bound_on_spectrum hs) := by
      refine hs.funCalc_congr _ _ fun t ht => ?_
      rcases ht.1.eq_or_lt with h0 | h0
      · have htz : t = 0 := h0.symm
        subst htz
        rw [Pi.mul_apply, hh0, hψ.map_zero, hφ.map_zero, mul_zero]
      · have hp := hpsipos t ⟨h0, ht.2⟩
        have hne : ψ t ≠ 0 := hp.ne'
        rw [Pi.mul_apply, hhval t h0]
        field_simp
    rw [← heq, hs.funCalc_mul' (hψ.exists_bound_on_spectrum hs) hbh]
    rfl

end AutoIp

end

end _lem_source_monotone
