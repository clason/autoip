module

import AutoIp._part_1_funcanal._ch_06_compact_operators._thm_complete_continuity.Spec -- shake: keep
import AutoIpTests.Witnesses.Diagonal

open scoped InnerProductSpace Topology
open scoped Topology

/-- The hypotheses of `isCompactOperator_of_tendstoWeakly_tendsto` can hold together. -/
theorem isCompactOperator_of_tendstoWeakly_tendsto_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (H : Type), ∃ (x3 : NormedAddCommGroup H), ∃ (x4 : InnerProductSpace 𝕜 H), ∃ (x5 : CompleteSpace H), ∃ (F : Type), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : NormedSpace 𝕜 F), ∃ (T : H →L[𝕜] F), ∀ (x : ℕ → H) (a : H),
  TendstoWeakly 𝕜 x a → Filter.Tendsto (fun (n : ℕ) => (T : H → F) (x n)) Filter.atTop (nhds ((T : H → F) a)) :=
  by
  classical
  refine ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, inferInstance, ℝ, inferInstance,
    inferInstance, 0, ?_⟩
  exact by simp

/-- The hypotheses of `isCompactOperator_of_tendstoWeakly_tendsto` can fail. -/
theorem isCompactOperator_of_tendstoWeakly_tendsto_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (H : Type), ∃ (x3 : NormedAddCommGroup H), ∃ (x4 : InnerProductSpace 𝕜 H), ∃ (x5 : CompleteSpace H), ∃ (F : Type), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : NormedSpace 𝕜 F), ∃ (T : H →L[𝕜] F), ¬ (∀ (x : ℕ → H) (a : H),
  TendstoWeakly 𝕜 x a → Filter.Tendsto (fun (n : ℕ) => (T : H → F) (x n)) Filter.atTop (nhds ((T : H → F) a))) :=
  by
  refine ⟨ℝ, inferInstance, Witnesses.Diagonal.H, inferInstance, inferInstance, inferInstance,
    Witnesses.Diagonal.H, inferInstance, inferInstance, 1, ?_⟩
  intro h
  have hw : TendstoWeakly ℝ Witnesses.Diagonal.e 0 := fun f => by
    simpa using Witnesses.Diagonal.tendsto_dual_e f
  have ht := h _ 0 hw
  have hn := (tendsto_zero_iff_norm_tendsto_zero.1 (by simpa using ht))
  simp only [Witnesses.Diagonal.norm_e] at hn
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hn)

/-- The hypotheses of `IsCompactOperator.tendsto_of_tendstoWeakly` can hold together. -/
theorem IsCompactOperator.tendsto_of_tendstoWeakly_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : NormedSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : NormedSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (x : ℕ → E), ∃ (a : E), (IsCompactOperator (⇑T : E → F)) ∧ (TendstoWeakly 𝕜 x a) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    0, fun _ => 0, 0, ?_⟩
  exact ⟨isCompactOperator_zero, fun f => tendsto_const_nhds⟩

/-- The hypotheses of `IsCompactOperator.tendsto_of_tendstoWeakly` can fail. -/
theorem IsCompactOperator.tendsto_of_tendstoWeakly_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : NormedSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : NormedSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (x : ℕ → E), ∃ (a : E), ¬ ((IsCompactOperator (⇑T : E → F)) ∧ (TendstoWeakly 𝕜 x a)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    0, fun _ => 1, 0, ?_⟩
  rintro ⟨-, h⟩
  have ht := h (ContinuousLinearMap.id ℝ ℝ)
  simp only [ContinuousLinearMap.id_apply] at ht
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds ht)
