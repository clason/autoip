module

import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_equations.Spec -- shake: keep
import AutoIpTests.Witnesses.Diagonal

open scoped InnerProductSpace

/-- The hypotheses of `AutoIp.moorePenrose_comp_self_comp_moorePenrose` can hold together. -/
theorem AutoIp.moorePenrose_comp_self_comp_moorePenrose_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (y : F), y ∈ AutoIp.mpDomain T :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 0, 0, ?_⟩
  exact by simp

/-- The hypotheses of `AutoIp.moorePenrose_comp_self_comp_moorePenrose` can fail. -/
theorem AutoIp.moorePenrose_comp_self_comp_moorePenrose_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (y : F), ¬ (y ∈ AutoIp.mpDomain T) :=
  ⟨ℝ, inferInstance, Witnesses.Diagonal.H, Witnesses.Diagonal.H, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, Witnesses.Diagonal.T, Witnesses.Diagonal.y, Witnesses.Diagonal.notMem_sup_orthogonal_range⟩
