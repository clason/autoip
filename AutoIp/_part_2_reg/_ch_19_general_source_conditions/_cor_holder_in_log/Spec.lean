/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_12_picard._def_source_set
public import AutoIp._part_2_reg._ch_19_general_source_conditions._def_general_source
public import AutoIp._part_2_reg._ch_19_general_source_conditions._def_log_index
import AutoIp._part_2_reg._ch_19_general_source_conditions._lem_holder_is_index
public import AutoIp._part_2_reg._ch_19_general_source_conditions._lem_log_is_index
import AutoIp._part_2_reg._ch_19_general_source_conditions._lem_source_monotone
import AutoIp.Auxiliary.ExpBound

section _cor_holder_in_log

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- For all `ν, p > 0` and `κ` there is `c > 0` with `X_{ν,ρ} ⊆ X_{φ^log_p, cρ}` for every
`ρ > 0` and every operator `K` with `‖K‖² = κ`, whatever its spaces and its singular system.

The hypothesis that `cρ > 0` is there because the source set needs it. -/
public
theorem exists_sourceSet_subset_sourceSetIndex_logIndex {ν p : ℝ} (hν : 0 < ν) (hp : 0 < p)
    (κ : ℝ) :
    ∃ c > (0 : ℝ), ∀ {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E]
      [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
      [CompleteSpace F] (K : E →L[𝕜] F), ‖K‖ ^ 2 = κ →
      ∀ {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F} (hs : IsSingularSystem K σ v u)
        (ρ : ℝ) (hρ : 0 < ρ) (hcρ : 0 < c * ρ),
        sourceSet hs ν hν ρ hρ
          ⊆ sourceSetIndex hs (logIndex (‖K‖ ^ 2) p hp)
              ((isIndexFunction_logIndex hp).exists_bound_on_spectrum hs) (c * ρ) hcρ :=
  by
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ⌈p⌉₊ + 1 := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ,
      c = 1 + (Real.exp 1 * |κ|) ^ (ν / 2) * ((m : ℝ) / (ν / 2)) ^ m := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    have h1 : (0:ℝ) ≤ (Real.exp 1 * |κ|) ^ (ν / 2) := Real.rpow_nonneg (by positivity) _
    have hm0 : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have h2 : (0:ℝ) ≤ ((m : ℝ) / (ν / 2)) ^ m := pow_nonneg (div_nonneg hm0 (by linarith)) _
    rw [hcdef]
    nlinarith
  refine ⟨c, hc0, ?_⟩
  intro 𝕜 _ E F _ _ _ _ _ _ K hK ι σ v u hs ρ
  have hk0 : (0:ℝ) ≤ ‖K‖ ^ 2 := by positivity
  have hcdef' : c = 1 + (Real.exp 1 * ‖K‖ ^ 2) ^ (ν / 2) * ((m : ℝ) / (ν / 2)) ^ m := by
    rw [hcdef, ← hK, abs_of_nonneg hk0]
  have hep : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hek : (0:ℝ) ≤ Real.exp 1 * ‖K‖ ^ 2 := by positivity
  have hm : 0 < m := by rw [hmdef]; exact Nat.succ_pos _
  have hpm : p ≤ (m : ℝ) := by
    have h := Nat.le_ceil p
    rw [hmdef]
    push_cast
    linarith
  have ha2 : (0:ℝ) < ν / 2 := by linarith
  have hle : ∀ lam ∈ Set.Ioc (0:ℝ) (‖K‖ ^ 2),
      (fun t : ℝ => t ^ (ν / 2)) lam ≤ c * logIndex (‖K‖ ^ 2) p hp lam := by
    intro lam hlam
    have hlam0 : (0:ℝ) < lam := hlam.1
    have hkpos : (0:ℝ) < ‖K‖ ^ 2 := lt_of_lt_of_le hlam0 hlam.2
    have hekpos : (0:ℝ) < Real.exp 1 * ‖K‖ ^ 2 := by positivity
    obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = Real.log (Real.exp 1 * ‖K‖ ^ 2 / lam) := ⟨_, rfl⟩
    have hu1 : 1 ≤ u := by
      have h1 : Real.exp 1 ≤ Real.exp 1 * ‖K‖ ^ 2 / lam := by
        rw [le_div_iff₀ hlam0]
        exact mul_le_mul_of_nonneg_left hlam.2 hep.le
      rw [hudef]
      calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ _ := Real.log_le_log hep h1
    have hu0 : (0:ℝ) < u := by linarith
    have hvl : logIndex (‖K‖ ^ 2) p hp lam = u ^ (-p) := by
      rw [hudef]
      exact logIndex_of_pos hlam0 _ hp
    have hup : (0:ℝ) < u ^ p := Real.rpow_pos_of_pos hu0 p
    have hsub : lam ^ (ν / 2)
        = (Real.exp 1 * ‖K‖ ^ 2) ^ (ν / 2) * Real.exp (-(ν / 2 * u)) := by
      rw [Real.rpow_def_of_pos hlam0, Real.rpow_def_of_pos hekpos, ← Real.exp_add, hudef,
        Real.log_div hekpos.ne' hlam0.ne']
      congr 1
      ring
    have hbnd : Real.exp (-(ν / 2 * u)) * u ^ p ≤ ((m:ℝ) / (ν / 2)) ^ m := by
      have h1 : u ^ p ≤ u ^ (m : ℕ) := by
        rw [← Real.rpow_natCast u m]
        exact Real.rpow_le_rpow_of_exponent_le hu1 hpm
      have h2 := pow_le_pow_div_mul_exp ha2 hm hu0.le
      have he : (0:ℝ) < Real.exp (-(ν / 2 * u)) := Real.exp_pos _
      have hne : Real.exp (ν / 2 * u) ≠ 0 := (Real.exp_pos _).ne'
      calc Real.exp (-(ν / 2 * u)) * u ^ p
          ≤ Real.exp (-(ν / 2 * u)) * (((m:ℝ) / (ν / 2)) ^ m * Real.exp (ν / 2 * u)) :=
            mul_le_mul_of_nonneg_left (h1.trans h2) he.le
        _ = ((m:ℝ) / (ν / 2)) ^ m := by
            rw [Real.exp_neg]
            field_simp
    change lam ^ (ν / 2) ≤ c * logIndex (‖K‖ ^ 2) p hp lam
    rw [hvl, Real.rpow_neg hu0.le, ← div_eq_mul_inv, le_div_iff₀ hup, hsub]
    calc (Real.exp 1 * ‖K‖ ^ 2) ^ (ν / 2) * Real.exp (-(ν / 2 * u)) * u ^ p
        = (Real.exp 1 * ‖K‖ ^ 2) ^ (ν / 2) * (Real.exp (-(ν / 2 * u)) * u ^ p) := by ring
      _ ≤ (Real.exp 1 * ‖K‖ ^ 2) ^ (ν / 2) * ((m:ℝ) / (ν / 2)) ^ m :=
          mul_le_mul_of_nonneg_left hbnd (Real.rpow_nonneg hek _)
      _ ≤ c := by rw [hcdef']; linarith
  intro hρ hcρ
  rw [← sourceSetIndex_rpow hs hν hρ]
  exact sourceSetIndex_mono_index hs (isIndexFunction_rpow hν _)
    (isIndexFunction_logIndex hp) hc0 hρ hle

end AutoIp

end _cor_holder_in_log
