/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_12_picard._def_source_set
public import AutoIp._part_2_reg._ch_14_order_optimality._def_worst_case_error
import AutoIp._part_1_funcanal._ch_08_svd._cor_sigma_null
import AutoIp._part_2_reg._ch_14_order_optimality._thm_modulus_source_upper
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

section _thm_modulus_attained

namespace AutoIp

open Filter Topology
open scoped ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F}

/-- If `K` has infinite-dimensional range and `ν, ρ > 0`, there is a null sequence `(δₙ)`
of positive numbers with `ε(X_{ν,ρ}, δₙ) = δₙ^{ν/(ν+1)} ρ^{1/(ν+1)}`. In place of
compactness of `K` the Lean takes an ordered singular system of `K`, from which
`X_{ν,ρ}` is formed. -/
public
theorem exists_seq_tendsto_zero_modulusOfContinuity_eq {I : Set ℕ} {σ : I → ℝ} {v : I → E}
    {u : I → F} (hs : IsOrderedSingularSystem K σ v u)
    (hinf : ¬ FiniteDimensional 𝕜 K.toLinearMap.range) {ν ρ : ℝ}
    (hν : 0 < ν) (hρ : 0 < ρ) :
    ∃ (d : ℕ → ℝ) (hd : ∀ n, 0 < d n), Tendsto d atTop (𝓝 0) ∧
      ∀ n, modulusOfContinuity K (sourceSet hs.toIsSingularSystem ν hν ρ hρ) (d n) (hd n) =
        ENNReal.ofReal (d n ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1))) := by
  have hν1 : (0 : ℝ) < ν + 1 := by linarith
  obtain ⟨hIinf, hσ0⟩ := hs.infinite_and_tendsto_zero_of_not_finiteDimensional_range hinf
  have hIall : ∀ m : ℕ, m ∈ I := by
    intro m
    obtain ⟨k, hk, hmk⟩ := hIinf.exists_gt m
    exact hs.isLowerSet hk hmk.le
  set e : ℕ → I := fun n => ⟨n, hIall n⟩ with he
  have hetop : Tendsto e atTop atTop := by
    refine tendsto_atTop_atTop.2 fun b => ⟨(b : ℕ), fun a ha => ?_⟩
    exact ha
  have hse : Tendsto (fun n => σ (e n)) atTop (𝓝 0) := hσ0.comp hetop
  have hdpos : ∀ n : ℕ, 0 < ρ * σ (e n) ^ (ν + 1) := fun n =>
    mul_pos hρ (Real.rpow_pos_of_pos (hs.pos _) _)
  refine ⟨fun n => ρ * σ (e n) ^ (ν + 1), hdpos, ?_, ?_⟩
  · have h1 : Tendsto (fun n => σ (e n) ^ (ν + 1)) atTop (𝓝 0) :=
      hse.rpow_const_nhds_zero hν1
    simpa using h1.const_mul ρ
  intro n
  set i : I := e n with hi
  set δ : ℝ := ρ * σ i ^ (ν + 1) with hδdef
  have hσi : 0 < σ i := hs.pos i
  have hδ : 0 < δ := mul_pos hρ (Real.rpow_pos_of_pos hσi _)
  -- name the radius before working with it: the positivity the modulus carries is a
  -- proof of `0 < δ`, so the goal has to be phrased in `δ` and `hδ` throughout
  change modulusOfContinuity K (sourceSet hs.toIsSingularSystem ν hν ρ hρ) δ hδ =
    ENNReal.ofReal (δ ^ (ν / (ν + 1)) * ρ ^ (1 / (ν + 1)))
  refine le_antisymm (modulusOfContinuity_sourceSet_le hs.toIsSingularSystem hν hρ hδ) ?_
  set w : E := (RCLike.ofReal ρ : 𝕜) • v i with hw
  have hvn : ‖v i‖ = 1 := hs.orthonormal_left.1 i
  have hun : ‖u i‖ = 1 := hs.orthonormal_right.1 i
  have hwn : ‖w‖ ≤ ρ := by
    rw [hw, norm_smul, RCLike.norm_ofReal, abs_of_pos hρ, hvn, mul_one]
  set x : E := hs.toIsSingularSystem.absRpow ν hν.le w with hx
  have hxmem : x ∈ sourceSet hs.toIsSingularSystem ν hν ρ hρ := by
    rw [mem_sourceSet_iff]
    exact ⟨w, hwn, rfl⟩
  have hxval : x = (RCLike.ofReal (ρ * σ i ^ ν) : 𝕜) • v i := by
    rw [hx, hw, map_smul, IsSingularSystem.absRpow_apply_v hs.toIsSingularSystem hν.le i, smul_smul,
      ← RCLike.ofReal_mul]
  have hρν : (0 : ℝ) < ρ * σ i ^ ν := mul_pos hρ (Real.rpow_pos_of_pos hσi _)
  have hxnorm : ‖x‖ = ρ * σ i ^ ν := by
    rw [hxval, norm_smul, RCLike.norm_ofReal, abs_of_pos hρν, hvn, mul_one]
  have hKx : ‖K x‖ = δ := by
    rw [hxval, map_smul, hs.map_left i, smul_smul, ← RCLike.ofReal_mul, norm_smul,
      RCLike.norm_ofReal, hun, mul_one, abs_of_pos (by positivity), hδdef, mul_assoc,
      ← Real.rpow_add_one hσi.ne' ν]
  rw [modulusOfContinuity]
  have hle := le_iSup₂ (α := ℝ≥0∞)
    (f := fun z (_ : z ∈ {z ∈ sourceSet hs.toIsSingularSystem ν hν ρ hρ | ‖K z‖ ≤ δ}) =>
      ‖z‖ₑ) x ⟨hxmem, le_of_eq hKx⟩
  refine le_trans (le_of_eq ?_) hle
  rw [← ofReal_norm]
  congr 1
  rw [hxnorm, hδdef]
  have h1 : (ρ * σ i ^ (ν + 1)) ^ (ν / (ν + 1)) = ρ ^ (ν / (ν + 1)) * σ i ^ ν := by
    rw [Real.mul_rpow hρ.le (Real.rpow_nonneg hσi.le _), ← Real.rpow_mul hσi.le]
    congr 2
    field_simp
  rw [h1, mul_right_comm, ← Real.rpow_add hρ,
    show ν / (ν + 1) + 1 / (ν + 1) = 1 by field_simp, Real.rpow_one]

end AutoIp

end _thm_modulus_attained
