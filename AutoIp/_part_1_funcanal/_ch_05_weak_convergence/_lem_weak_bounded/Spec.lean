/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_05_weak_convergence._def_weak_conv
import Mathlib.Analysis.Normed.Module.DoubleDual

section _lem_weak_bounded

open scoped Topology
variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- If xₙ ⇀ a in a normed space then supₙ ‖xₙ‖ < ∞, stated as a bound ‖xₙ‖ ≤ C for all
n. -/
public theorem TendstoWeakly.exists_norm_le {x : ℕ → E} {a : E}
    (h : TendstoWeakly 𝕜 x a) : ∃ C : ℝ, ∀ n, ‖x n‖ ≤ C := by
  -- Banach--Steinhaus runs on the dual `E'`, which is complete for any normed `E`; the
  -- family is `x n` seen inside the bidual, and that embedding is an isometry.
  have hb : ∀ f : StrongDual 𝕜 E, ∃ C : ℝ, ∀ n,
      ‖NormedSpace.inclusionInDoubleDual 𝕜 E (x n) f‖ ≤ C := by
    intro f
    have hnorm : Filter.Tendsto (fun n => ‖f (x n)‖) Filter.atTop (nhds ‖f a‖) :=
      (continuous_norm.tendsto _).comp (h f)
    obtain ⟨C, hC⟩ := hnorm.bddAbove_range
    exact ⟨C, fun n => by simpa using hC ⟨n, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hb
  refine ⟨C, fun n => ?_⟩
  have hiso : ‖NormedSpace.inclusionInDoubleDual 𝕜 E (x n)‖ = ‖x n‖ :=
    (NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map (x n)
  rw [← hiso]
  exact hC n

end _lem_weak_bounded
