module

import AutoIp._part_1_funcanal._ch_05_weak_convergence._thm_weak_compactness.Spec -- shake: keep
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped InnerProductSpace Topology

/-- The hypotheses of `exists_tendstoWeakly_subseq_of_bounded` can hold together. -/
theorem exists_tendstoWeakly_subseq_of_bounded_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (H : Type), ∃ (x3 : NormedAddCommGroup H), ∃ (x4 : InnerProductSpace 𝕜 H), ∃ (x5 : CompleteSpace H), ∃ (x : ℕ → H), ∃ (C : ℝ), ∀ (n : ℕ), ‖x n‖ ≤ C :=
  by
  classical
  refine ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, inferInstance, fun _ => 0, 0, ?_⟩
  exact by simp

/-- The hypotheses of `exists_tendstoWeakly_subseq_of_bounded` can fail. -/
theorem exists_tendstoWeakly_subseq_of_bounded_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (H : Type), ∃ (x3 : NormedAddCommGroup H), ∃ (x4 : InnerProductSpace 𝕜 H), ∃ (x5 : CompleteSpace H), ∃ (x : ℕ → H), ∃ (C : ℝ), ¬ (∀ (n : ℕ), ‖x n‖ ≤ C) :=
  ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, inferInstance, fun _ => 1, 0, by
      intro h
      have := h 0
      simp only [norm_one] at this
      linarith⟩
