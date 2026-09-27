/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIpTests.Witnesses.Diagonal

/-!
# Truncated inverses of the diagonal operator on `ℓ²`

For a positive parameter `α`, the operator inverting the weights of the diagonal operator on
the first `⌈α⁻¹⌉₊` coordinates and discarding the rest. These truncated inverses recover every
preimage as `α` decreases to `0`, and composed with the diagonal operator they have norm at most
one. Also that the diagonal operator is not bounded below.
-/

namespace Witnesses.DiagonalCutoff

open Witnesses.Diagonal Filter Topology
open scoped InnerProductSpace ENNReal

/-- The number of coordinates kept at the parameter `α`. -/
noncomputable def N (α : Set.Ioi (0 : ℝ)) : ℕ := ⌈(α : ℝ)⁻¹⌉₊

/-- The truncated inverse at the parameter `α`. -/
public noncomputable def R (α : Set.Ioi (0 : ℝ)) : H →L[ℝ] H :=
  ∑ k ∈ Finset.range (N α), (w k)⁻¹ • (innerSL ℝ (e k)).smulRight (e k)

theorem R_apply (α : Set.Ioi (0 : ℝ)) (z : H) (n : ℕ) :
    (R α z) n = if n < N α then (w n)⁻¹ * z n else 0 := by
  classical
  have h : R α z = ∑ k ∈ Finset.range (N α), ((w k)⁻¹ * z k) • e k := by
    simp only [R, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, e_def, lp.inner_single_left,
      smul_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simp [mul_comm]
  rw [h, lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply, e_def, lp.single_apply, smul_eq_mul, Pi.single_apply,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

theorem T_R_apply (α : Set.Ioi (0 : ℝ)) (z : H) (n : ℕ) :
    (T (R α z)) n = if n < N α then z n else 0 := by
  rw [T_apply, R_apply]
  split_ifs
  · rw [← mul_assoc, mul_inv_cancel₀ (w_pos n).ne', one_mul]
  · rw [mul_zero]

theorem R_T (α : Set.Ioi (0 : ℝ)) (x : H) :
    R α (T x) = ∑ k ∈ Finset.range (N α), lp.single 2 k (x k) := by
  classical
  refine lp.ext (funext fun n => ?_)
  rw [R_apply, T_apply, lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.single_apply, Pi.single_apply]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range]
  split_ifs
  · rw [← mul_assoc, inv_mul_cancel₀ (w_pos n).ne', one_mul]
  · rfl

theorem tendsto_N : Tendsto N atBot atTop := by
  rw [tendsto_atTop]
  intro b
  rw [Filter.eventually_atBot]
  have hb : (0 : ℝ) < 1 / ((b : ℝ) + 1) := by positivity
  refine ⟨⟨1 / ((b : ℝ) + 1), Set.mem_Ioi.2 hb⟩, fun α hα => ?_⟩
  have hα' : (α : ℝ) ≤ 1 / ((b : ℝ) + 1) := hα
  have hα0 : (0 : ℝ) < α := α.2
  have h1 : (b : ℝ) + 1 ≤ (α : ℝ)⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hα0]
    simpa [one_div] using hα'
  have h2 : (b : ℝ) ≤ (N α : ℝ) := by
    have := Nat.le_ceil ((α : ℝ)⁻¹)
    unfold N
    linarith
  exact_mod_cast h2

/-- The truncated inverses recover every preimage in the limit. -/
public theorem tendsto_R_T (x : H) : Tendsto (fun α => R α (T x)) atBot (𝓝 x) := by
  have hs : Tendsto (fun M => ∑ k ∈ Finset.range M, lp.single 2 k (x k)) atTop (𝓝 x) :=
    (lp.hasSum_single (by norm_num) x).tendsto_sum_nat
  refine (hs.comp tendsto_N).congr fun α => ?_
  exact (R_T α x).symm

/-- The diagonal operator composed with a truncated inverse has norm at most one. -/
public theorem norm_T_comp_R_le (α : Set.Ioi (0 : ℝ)) : ‖T.comp (R α)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
  rw [one_mul]
  refine norm_le_of_forall_sum_sq_le (norm_nonneg _) fun s => ?_
  refine le_trans (Finset.sum_le_sum fun n _ => ?_) (sum_sq_le_norm_sq z s)
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  rw [ContinuousLinearMap.comp_apply, T_R_apply]
  split_ifs
  · exact le_rfl
  · rw [norm_zero]
    exact norm_nonneg _

/-- The diagonal operator is not bounded below. -/
public theorem not_exists_norm_le_mul_norm_T :
    ¬ ∃ C : ℝ, ∀ x : H, ‖x‖ ≤ C * ‖T x‖ := by
  rintro ⟨C, hC⟩
  have hp : (0 : ℝ≥0∞) < 2 := by norm_num
  have hle : ∀ n, 1 ≤ C * w n := by
    intro n
    have h := hC (e n)
    rw [e_def, T_single, lp.norm_single hp, lp.norm_single hp, norm_one, Real.norm_eq_abs,
      abs_of_pos (w_pos n)] at h
    exact h
  have hlim : Tendsto (fun n => C * w n) atTop (𝓝 0) := by
    simpa using tendsto_w.const_mul C
  have hev := (hlim.eventually (gt_mem_nhds one_pos)).exists
  obtain ⟨n, hn⟩ := hev
  exact absurd (hle n) (not_le.2 hn)

end Witnesses.DiagonalCutoff
