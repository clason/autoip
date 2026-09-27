/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_13_regularization._def_parameter_choice
public import AutoIp._part_2_reg._ch_13_regularization._def_regularization
import AutoIp._part_2_reg._ch_13_regularization._thm_apriori_characterisation
public import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init

namespace AutoIp

open Filter Topology

/-- For a nonnegative sequence `(cₙ)` there is a positive antitone sequence `(eₙ)` with
`eₙ ≤ 1 / (n + 1)` and `eₙ cₙ ≤ 1 / (n + 1)` for all `n`. -/
public theorem exists_antitone_scale (c : ℕ → ℝ) (hc : ∀ n : ℕ, 0 ≤ c n) :
    ∃ e : ℕ → ℝ, (∀ n : ℕ, 0 < e n) ∧ (∀ m n : ℕ, m ≤ n → e n ≤ e m) ∧
      (∀ n : ℕ, e n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, e n * c n ≤ 1 / ((n : ℝ) + 1)) := by
  set d : ℕ → ℝ := fun m => 1 / (((m : ℝ) + 1) * (1 + c m)) with hd
  have hdpos : ∀ m : ℕ, 0 < d m := by
    intro m
    have h1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < 1 + c m := by linarith [hc m]
    simp only [hd]
    exact one_div_pos.mpr (mul_pos h1 h2)
  have hdle : ∀ m : ℕ, d m ≤ 1 / ((m : ℝ) + 1) := by
    intro m
    have hcm : (0 : ℝ) ≤ c m := hc m
    have h1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    simp only [hd]
    exact one_div_le_one_div_of_le h1 (by nlinarith)
  have hdmul : ∀ m : ℕ, d m * c m ≤ 1 / ((m : ℝ) + 1) := by
    intro m
    have hcm : (0 : ℝ) ≤ c m := hc m
    have h1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < ((m : ℝ) + 1) * (1 + c m) := mul_pos h1 (by linarith)
    simp only [hd]
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ h2 h1]
    nlinarith
  have hne : ∀ n : ℕ, (Finset.range (n + 1)).Nonempty := fun n => ⟨0, by simp⟩
  refine ⟨fun n => (Finset.range (n + 1)).inf' (hne n) d, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [Finset.lt_inf'_iff]
    exact fun i _ => hdpos i
  · intro m n hmn
    refine Finset.le_inf' (hne m) d ?_
    intro i hi
    refine Finset.inf'_le d ?_
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro n
    exact (Finset.inf'_le d (by simp)).trans (hdle n)
  · intro n
    exact le_trans (mul_le_mul_of_nonneg_right (Finset.inf'_le d (by simp)) (hc n)) (hdmul n)

/-- For an antitone sequence `(eₙ)` with `eₙ ≤ 1 / (n + 1)` there is a map `δ ↦ n(δ)` into `ℕ`
with `N ≤ n(δ)` whenever `0 < δ < e_N`, and `δ < e_{n(δ)}` whenever `0 < δ < e₀`. -/
public theorem exists_index_of_antitone_scale {e : ℕ → ℝ}
    (heanti : ∀ m n : ℕ, m ≤ n → e n ≤ e m) (hesmall : ∀ n : ℕ, e n ≤ 1 / ((n : ℝ) + 1)) :
    ∃ nn : ℝ → ℕ,
      (∀ (δ : ℝ) (N : ℕ), 0 < δ → δ < e N → N ≤ nn δ) ∧
      (∀ δ : ℝ, 0 < δ → δ < e 0 → δ < e (nn δ)) := by
  have hSne : ∀ δ : ℝ, 0 < δ → {n : ℕ | e n ≤ δ}.Nonempty := by
    intro δ hδ
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    exact ⟨n, le_of_lt (lt_of_le_of_lt (hesmall n) hn)⟩
  refine ⟨fun δ => sInf {n : ℕ | e n ≤ δ} - 1, ?_, ?_⟩
  · intro δ N hδ hlt
    have hmem : sInf {n : ℕ | e n ≤ δ} ∈ {n : ℕ | e n ≤ δ} := Nat.sInf_mem (hSne δ hδ)
    simp only [Set.mem_ofPred_eq] at hmem
    have hgt : N < sInf {n : ℕ | e n ≤ δ} := by
      by_contra hcon
      rw [not_lt] at hcon
      have h1 : e N ≤ e (sInf {n : ℕ | e n ≤ δ}) := heanti _ N hcon
      linarith
    -- beta-reduce the applied rule, which `omega` cannot see through
    change N ≤ sInf {n : ℕ | e n ≤ δ} - 1
    omega
  · intro δ hδ h0lt
    have hmem : sInf {n : ℕ | e n ≤ δ} ∈ {n : ℕ | e n ≤ δ} := Nat.sInf_mem (hSne δ hδ)
    simp only [Set.mem_ofPred_eq] at hmem
    have hpos : 0 < sInf {n : ℕ | e n ≤ δ} := by
      rcases Nat.eq_zero_or_pos (sInf {n : ℕ | e n ≤ δ}) with h | h
      · rw [h] at hmem; linarith
      · exact h
    have hlt : sInf {n : ℕ | e n ≤ δ} - 1 < sInf {n : ℕ | e n ≤ δ} := by omega
    have hnot := Nat.notMem_of_lt_sInf hlt
    simp only [Set.mem_ofPred_eq, not_le] at hnot
    exact hnot

end AutoIp
