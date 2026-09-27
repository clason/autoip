/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_19_general_source_conditions._def_log_index.Spec
import all AutoIp._part_2_reg._ch_19_general_source_conditions._def_log_index.Spec
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace AutoIp

/-- `φ^log_p(λ) = 0` for `λ ≤ 0`. -/
public theorem logIndex_of_nonpos {lam : ℝ} (h : lam ≤ 0) (κ : ℝ) {p : ℝ} (hp : 0 < p) :
    logIndex κ p hp lam = 0 := by
  unfold logIndex
  simp [h]

/-- `φ^log_p(λ) = (log (eκ/λ))^(-p)` for `λ > 0`. -/
public theorem logIndex_of_pos {lam : ℝ} (h : 0 < lam) (κ : ℝ) {p : ℝ} (hp : 0 < p) :
    logIndex κ p hp lam = (Real.log (Real.exp 1 * κ / lam)) ^ (-p) := by
  unfold logIndex
  simp [not_le.2 h]

/-- `1 ≤ log(eκ/s)` for `s ∈ (0, κ]`. -/
public theorem one_le_log_exp_mul_div {κ s : ℝ} (hs : 0 < s) (hsk : s ≤ κ) :
    1 ≤ Real.log (Real.exp 1 * κ / s) := by
  have hep : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h1 : Real.exp 1 ≤ Real.exp 1 * κ / s := by
    rw [le_div_iff₀ hs]
    exact mul_le_mul_of_nonneg_left hsk hep.le
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ _ := Real.log_le_log hep h1

/-- `φ^log_p` is positive on `(0, κ]`. -/
public theorem logIndex_pos {κ p lam : ℝ} (hp : 0 < p) (h0 : 0 < lam) (hκ : lam ≤ κ) :
    0 < logIndex κ p hp lam := by
  rw [logIndex_of_pos h0]
  exact Real.rpow_pos_of_pos (by linarith [one_le_log_exp_mul_div h0 hκ]) _

/-- `φ^log_p` is at most `1` on `(0, κ]`. -/
public theorem logIndex_le_one {κ p lam : ℝ} (hp : 0 < p) (h0 : 0 < lam) (hκ : lam ≤ κ) :
    logIndex κ p hp lam ≤ 1 := by
  rw [logIndex_of_pos h0]
  exact Real.rpow_le_one_of_one_le_of_nonpos (one_le_log_exp_mul_div h0 hκ) (by linarith)

/-- `φ^log_p(κ) = 1` for `κ > 0`. -/
public theorem logIndex_self {κ p : ℝ} (hp : 0 < p) (hκ : 0 < κ) : logIndex κ p hp κ = 1 := by
  rw [logIndex_of_pos hκ, mul_div_assoc, div_self hκ.ne', mul_one, Real.log_exp,
    Real.one_rpow]

end AutoIp
