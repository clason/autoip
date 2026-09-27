/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_13_regularization._def_regularization
import AutoIp._part_1_funcanal._ch_01_bounded_operators._thm_resonance

section _thm_reg_not_uniformly_bounded

namespace AutoIp

open Filter Topology
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- For a regularization `{R_α}` of `T†` with `T†` unbounded,
`limsup_{α→0} ‖R_α‖ = ∞`: every bound `C` is exceeded by `‖R_α‖` at some `α` in every
interval `(0, ε)`. -/
public
theorem exists_mem_Ioo_lt_opNorm {T : E →L[𝕜] F} {R : Set.Ioi (0 : ℝ) → F →L[𝕜] E}
    (hR : IsRegularization T R)
    (hT : ¬ ∃ C : ℝ, ∀ y, ∀ hy : y ∈ mpDomain T, ‖moorePenrose T ⟨y, hy⟩‖ ≤ C * ‖y‖) :
    ∀ (C : ℝ) (ε : ℝ), 0 < ε → ∃ α : Set.Ioi (0 : ℝ), (α : ℝ) < ε ∧ C < ‖R α‖ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨C, ε, hε, hb⟩ := hcon
  refine hT ⟨C, fun y hy => ?_⟩
  have hev : ∀ᶠ α : Set.Ioi (0 : ℝ) in atBot, ‖R α y‖ ≤ C * ‖y‖ := by
    have hlt : ∀ᶠ α : Set.Ioi (0 : ℝ) in atBot, (α : ℝ) < ε :=
      eventually_atBot.2 ⟨⟨ε / 2, half_pos hε⟩, fun β hβ => lt_of_le_of_lt hβ (half_lt_self hε)⟩
    filter_upwards [hlt] with α hα
    calc ‖R α y‖ ≤ ‖R α‖ * ‖y‖ := (R α).le_opNorm y
      _ ≤ C * ‖y‖ := by gcongr; exact hb α hα
  exact le_of_tendsto ((hR y hy).norm) hev

/-- For a regularization `{R_α}` of `T†` with `T†` unbounded, there are `y ∈ Y` and a null
sequence `{α_n}` along which `‖R_{α_n} y‖ → ∞`. -/
public theorem exists_tendsto_norm_atTop [CompleteSpace F] {T : E →L[𝕜] F}
    {R : Set.Ioi (0 : ℝ) → F →L[𝕜] E}
    (hR : IsRegularization T R)
    (hT : ¬ ∃ C : ℝ, ∀ y, ∀ hy : y ∈ mpDomain T, ‖moorePenrose T ⟨y, hy⟩‖ ≤ C * ‖y‖) :
    ∃ (y : F) (a : ℕ → Set.Ioi (0 : ℝ)), Tendsto (fun n => (a n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖R (a n) y‖) atTop atTop := by
  classical
  have key : ∀ n : ℕ, ∃ α : Set.Ioi (0 : ℝ),
      (α : ℝ) < 1 / ((n : ℝ) + 1) ∧ (n : ℝ) < ‖R α‖ :=
    fun n => exists_mem_Ioo_lt_opNorm hR hT n (1 / ((n : ℝ) + 1)) (by positivity)
  choose α hα hαn using key
  have hunb : ∀ C : ℝ, ∃ n : ℕ, C < ‖R (α n)‖ := by
    intro C
    obtain ⟨n, hn⟩ := exists_nat_gt C
    exact ⟨n, hn.trans (hαn n)⟩
  obtain ⟨y, hy⟩ := banach_steinhaus_exists_unbounded (T := fun n : ℕ => R (α n)) hunb
  refine ⟨y, ?_⟩
  have hy' : ∀ (C : ℝ) (N : ℕ), ∃ n : ℕ, N < n ∧ C < ‖R (α n) y‖ := by
    intro C N
    have hne : (Finset.range (N + 1)).Nonempty := ⟨0, by simp⟩
    set B := (Finset.range (N + 1)).sup' hne (fun i => ‖R (α i) y‖) with hB
    obtain ⟨n, hn⟩ := hy (max C B)
    refine ⟨n, ?_, lt_of_le_of_lt (le_max_left _ _) hn⟩
    by_contra hcon
    push Not at hcon
    have hmemn : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    have h1 : ‖R (α n) y‖ ≤ B := by
      rw [hB]; exact Finset.le_sup' (fun i => ‖R (α i) y‖) hmemn
    exact absurd (lt_of_le_of_lt (le_max_right C B) hn) (not_lt.mpr h1)
  have hfreq : ∀ k : ℕ, ∃ᶠ n in atTop, (k : ℝ) < ‖R (α n) y‖ := fun k =>
    frequently_atTop.2 fun N => (hy' k N).imp fun n hn => ⟨hn.1.le, hn.2⟩
  obtain ⟨ns, hmono, hnorm⟩ := Filter.extraction_forall_of_frequently hfreq
  have hge : ∀ k : ℕ, k ≤ ns k := fun k => hmono.le_apply
  refine ⟨fun k => α (ns k), ?_, ?_⟩
  · refine squeeze_zero (fun k => (α (ns k)).2.le) (fun k => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : ((α (ns k) : ℝ)) < 1 / ((ns k : ℝ) + 1) := hα (ns k)
    have h2 : 1 / ((ns k : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      have h3 : ((k : ℕ) : ℝ) ≤ ((ns k : ℕ) : ℝ) := Nat.cast_le.mpr (hge k)
      linarith
    linarith
  · exact tendsto_atTop_mono (fun k => (hnorm k).le) tendsto_natCast_atTop_atTop

end AutoIp

end _thm_reg_not_uniformly_bounded
