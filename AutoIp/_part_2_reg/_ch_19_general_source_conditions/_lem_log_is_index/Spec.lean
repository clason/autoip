/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_19_general_source_conditions._def_index_function
public import AutoIp._part_2_reg._ch_19_general_source_conditions._def_log_index
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import AutoIp.Auxiliary.ExpBound

section _lem_log_is_index

namespace AutoIp

open Filter Topology

/-- `φ^log_p` is an index function on `[0, κ]` for every `p > 0`.

The statement holds for every real `κ`. -/
public theorem isIndexFunction_logIndex {κ p : ℝ} (hp : 0 < p) :
    IsIndexFunction κ (logIndex κ p hp) :=
  by
  have hep : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hval : ∀ s : ℝ, 0 < s → logIndex κ p hp s = Real.log (Real.exp 1 * κ / s) ^ (-p) :=
    fun s hs => logIndex_of_pos hs κ hp
  have hval0 : logIndex κ p hp 0 = 0 := logIndex_of_nonpos le_rfl κ hp
  have hlog : ∀ s : ℝ, 0 < s → s ≤ κ → 1 ≤ Real.log (Real.exp 1 * κ / s) :=
    fun _ hs hsk => one_le_log_exp_mul_div hs hsk
  refine ⟨hval0, ?_, ?_⟩
  · intro t ht
    rcases ht.1.eq_or_lt with h0 | h0
    · have htz : t = 0 := h0.symm
      subst htz
      have hk0 : (0:ℝ) ≤ κ := ht.2
      have hsub : Set.Icc (0:ℝ) κ ⊆ insert (0:ℝ) (Set.Ioi (0:ℝ)) := by
        intro s hsm
        rcases hsm.1.eq_or_lt with h | h
        · exact Set.mem_insert_iff.mpr (Or.inl h.symm)
        · exact Set.mem_insert_iff.mpr (Or.inr h)
      refine ContinuousWithinAt.mono (continuousWithinAt_insert_self.mpr ?_) hsub
      change Filter.Tendsto (logIndex κ p hp) (𝓝[>] (0:ℝ)) (𝓝 (logIndex κ p hp 0))
      rw [hval0]
      rcases hk0.eq_or_lt with hk | hk
      · refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (0:ℝ)))
        filter_upwards [self_mem_nhdsWithin] with s hs
        show (0:ℝ) = logIndex κ p hp s
        rw [hval s hs, ← hk]
        simp [Real.zero_rpow (neg_ne_zero.mpr hp.ne')]
      · have h1 : Filter.Tendsto (fun s : ℝ => Real.exp 1 * κ / s) (𝓝[>] (0:ℝ))
            Filter.atTop := by
          simp only [div_eq_mul_inv]
          exact Filter.Tendsto.const_mul_atTop (mul_pos hep hk) tendsto_inv_nhdsGT_zero
        have h3 := (tendsto_rpow_neg_atTop hp).comp (Real.tendsto_log_atTop.comp h1)
        refine Filter.Tendsto.congr' ?_ h3
        filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [Function.comp_apply]
        exact (hval s hs).symm
    · have hk : (0:ℝ) < κ := lt_of_lt_of_le h0 ht.2
      have hpos : (0:ℝ) < Real.exp 1 * κ / t := by positivity
      have hne : Real.log (Real.exp 1 * κ / t) ≠ 0 := by
        have := hlog t h0 ht.2
        linarith
      have hc : ContinuousAt (fun s : ℝ => Real.log (Real.exp 1 * κ / s) ^ (-p)) t := by
        refine ContinuousAt.rpow_const ?_ (Or.inl hne)
        refine ContinuousAt.log ?_ hpos.ne'
        exact ContinuousAt.div continuousAt_const continuousAt_id h0.ne'
      refine (hc.congr_of_eventuallyEq ?_).continuousWithinAt
      filter_upwards [eventually_gt_nhds h0] with s hs
      exact hval s hs
  · intro a ha b hb hab
    have hb0 : (0:ℝ) < b := lt_of_le_of_lt ha.1 hab
    have hk : (0:ℝ) < κ := lt_of_lt_of_le hb0 hb.2
    have hlb := hlog b hb0 hb.2
    have hpb : 0 < logIndex κ p hp b := by
      rw [hval b hb0]
      exact Real.rpow_pos_of_pos (by linarith) _
    rcases ha.1.eq_or_lt with h0 | h0
    · have haz : a = 0 := h0.symm
      subst haz
      rw [hval0]
      exact hpb
    · rw [hval a h0, hval b hb0]
      have hla := hlog a h0 ha.2
      have hlt : Real.log (Real.exp 1 * κ / b) < Real.log (Real.exp 1 * κ / a) := by
        refine Real.log_lt_log (by positivity) ?_
        exact div_lt_div_of_pos_left (by positivity) h0 hab
      exact Real.rpow_lt_rpow_of_neg (by linarith) hlt (by linarith)

end AutoIp

end _lem_log_is_index
