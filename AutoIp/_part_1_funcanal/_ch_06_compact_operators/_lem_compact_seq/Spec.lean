/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Basic

section _lem_compact_seq

open scoped Topology
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- T is compact if and only if every bounded sequence (xₙ) in `E` has a subsequence
(x_{φ(k)}) with (Tx_{φ(k)}) convergent in `F`. Here T is taken to be a bounded linear
operator. -/
public theorem isCompactOperator_iff_tendsto_subseq (T : E →L[𝕜] F) :
    IsCompactOperator T ↔
      ∀ (x : ℕ → E) (C : ℝ), (∀ n, ‖x n‖ ≤ C) →
        ∃ (φ : ℕ → ℕ) (y : F), StrictMono φ ∧
          Filter.Tendsto (fun k => T (x (φ k))) Filter.atTop (nhds y) := by
  constructor
  · -- `→`: the range of a bounded sequence is bounded, so its image has compact closure,
    -- and a compact metric space is sequentially compact.
    intro hT x C hC
    have hbdd : Bornology.IsBounded (Set.range x) :=
      isBounded_iff_forall_norm_le.mpr ⟨C, by rintro _ ⟨n, rfl⟩; exact hC n⟩
    have hcomp := hT.isCompact_closure_image_of_bounded hbdd
    have hmem : ∀ n, T (x n) ∈ closure (T '' Set.range x) := fun n =>
      subset_closure ⟨x n, ⟨n, rfl⟩, rfl⟩
    obtain ⟨y, -, φ, hφ, hconv⟩ := hcomp.tendsto_subseq hmem
    exact ⟨φ, y, hφ, hconv⟩
  · -- `←`: sequential compactness of `closure (T '' closedBall 0 1)`, via approximants.
    intro h
    refine (isCompactOperator_iff_isCompact_closure_image_closedBall
      (T : E →ₗ[𝕜] F) one_pos).mpr (IsSeqCompact.isCompact ?_)
    intro z hz
    have hpick : ∀ n : ℕ, ∃ v : E, ‖v‖ ≤ 1 ∧ dist (z n) (T v) < 1 / (n + 1) := by
      intro n
      obtain ⟨w, hw, hd⟩ :=
        Metric.mem_closure_iff.mp (hz n) (1 / (n + 1)) (by positivity)
      obtain ⟨v, hv, rfl⟩ := hw
      exact ⟨v, by simpa using hv, hd⟩
    choose v hv hd using hpick
    obtain ⟨φ, y, hφ, hconv⟩ := h v 1 hv
    have hy : y ∈ closure ((T : E →ₗ[𝕜] F) '' Metric.closedBall 0 1) :=
      mem_closure_of_tendsto hconv
        (Filter.Eventually.of_forall fun k => ⟨v (φ k), by simpa using hv (φ k), rfl⟩)
    refine ⟨y, hy, φ, hφ, ?_⟩
    -- `z ∘ φ` and `T ∘ v ∘ φ` differ by a null sequence
    rw [tendsto_iff_dist_tendsto_zero]
    have hle : ∀ k : ℕ, dist (z (φ k)) y ≤ 1 / (k + 1) + dist (T (v (φ k))) y := by
      intro k
      refine (dist_triangle (z (φ k)) (T (v (φ k))) y).trans ?_
      gcongr
      refine (hd (φ k)).le.trans ?_
      gcongr
      exact_mod_cast hφ.le_apply
    have hzero : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1) + dist (T (v (φ k))) y)
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using h1.add (tendsto_iff_dist_tendsto_zero.mp hconv)
    exact squeeze_zero (fun k => dist_nonneg) hle hzero

end _lem_compact_seq
