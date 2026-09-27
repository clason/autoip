/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_05_weak_convergence._def_weak_conv
import AutoIp._part_1_funcanal._ch_05_weak_convergence._lem_weak_bounded
import Mathlib.Analysis.Normed.Module.HahnBanach

section _lem_weak_lsc

open scoped Topology
variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- If xₙ ⇀ a in a normed space then ‖a‖ ≤ liminfₙ ‖xₙ‖. -/
public theorem TendstoWeakly.norm_le_liminf_norm {x : ℕ → E} {a : E}
    (h : TendstoWeakly 𝕜 x a) :
    ‖a‖ ≤ Filter.liminf (fun n => ‖x n‖) Filter.atTop := by
  -- Hahn--Banach gives a norm-attaining `g` with `‖g‖ ≤ 1`; it works at `a = 0` too, so no
  -- case split is needed.
  obtain ⟨g, hg1, hga⟩ := exists_dual_vector'' 𝕜 a
  have hlim : Filter.Tendsto (fun n => ‖g (x n)‖) Filter.atTop (nhds ‖a‖) := by
    have hcomp := (continuous_norm.tendsto (g a)).comp (h g)
    have hnorm : ‖g a‖ = ‖a‖ := by rw [hga]; exact RCLike.norm_of_nonneg (norm_nonneg a)
    rw [hnorm] at hcomp
    simpa [Function.comp_def] using hcomp
  have hle : ∀ n, ‖g (x n)‖ ≤ ‖x n‖ := fun n => by
    refine (g.le_opNorm (x n)).trans ?_
    nlinarith [norm_nonneg (x n), hg1]
  have hb1 : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop (fun n => ‖g (x n)‖) :=
    Filter.isBoundedUnder_of ⟨0, fun n => norm_nonneg (g (x n))⟩
  -- The second side condition is coboundedness, which is where boundedness of weakly
  -- convergent sequences is used.
  obtain ⟨C, hC⟩ := h.exists_norm_le
  have hb2 : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop (fun n => ‖x n‖) :=
    Filter.isCoboundedUnder_ge_of_le _ hC
  calc ‖a‖ = Filter.liminf (fun n => ‖g (x n)‖) Filter.atTop := hlim.liminf_eq.symm
    _ ≤ Filter.liminf (fun n => ‖x n‖) Filter.atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hle) hb1 hb2

end _lem_weak_lsc
