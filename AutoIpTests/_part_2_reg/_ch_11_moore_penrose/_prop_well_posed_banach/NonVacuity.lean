module

import AutoIp._part_2_reg._ch_11_moore_penrose._prop_well_posed_banach.Spec -- shake: keep

/-- The hypotheses of `AutoIp.isWellPosed_of_bijective` can hold together. -/
theorem AutoIp.isWellPosed_of_bijective_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : NormedSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : NormedSpace 𝕜 F), ∃ (x8 : CompleteSpace E), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), (∀ (y : F), ∃ (x : E), (T : E → F) x = y) ∧ (∀ (x x' : E), (T : E → F) x = (T : E → F) x' → x = x') :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ContinuousLinearMap.id ℝ ℝ, ?_⟩
  exact ⟨fun y => ⟨y, rfl⟩, fun x x' h => h⟩

/-- The hypotheses of `AutoIp.isWellPosed_of_bijective` can fail. -/
theorem AutoIp.isWellPosed_of_bijective_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : NormedSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : NormedSpace 𝕜 F), ∃ (x8 : CompleteSpace E), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ¬ ((∀ (y : F), ∃ (x : E), (T : E → F) x = y) ∧ (∀ (x x' : E), (T : E → F) x = (T : E → F) x' → x = x')) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, ?_⟩
  rintro ⟨-, h⟩
  exact zero_ne_one (h 0 1 rfl)
