module

import AutoIp._part_2_reg._ch_11_moore_penrose._lem_normal_mp.Spec -- shake: keep
import AutoIpTests.Witnesses.Diagonal

open scoped InnerProductSpace

/-- The hypotheses of `AutoIp.mem_mpDomain_adjoint_comp_self` can hold together. -/
theorem AutoIp.mem_mpDomain_adjoint_comp_self_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (y : F), y ∈ AutoIp.mpDomain T :=
  ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, 0, by simp⟩

/-- The hypotheses of `AutoIp.mem_mpDomain_adjoint_comp_self` can fail. -/
theorem AutoIp.mem_mpDomain_adjoint_comp_self_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (y : F), ¬ (y ∈ AutoIp.mpDomain T) :=
  ⟨ℝ, inferInstance, Witnesses.Diagonal.H, Witnesses.Diagonal.H, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, Witnesses.Diagonal.T,
    Witnesses.Diagonal.y, Witnesses.Diagonal.notMem_sup_orthogonal_range⟩

/-- The hypotheses of `AutoIp.moorePenrose_eq_moorePenrose_adjoint_comp_self` can hold together. -/
theorem AutoIp.moorePenrose_eq_moorePenrose_adjoint_comp_self_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (y : F), y ∈ AutoIp.mpDomain T :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, 0, ?_⟩
  exact by simp

/-- The hypotheses of `AutoIp.moorePenrose_eq_moorePenrose_adjoint_comp_self` can fail. -/
theorem AutoIp.moorePenrose_eq_moorePenrose_adjoint_comp_self_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (y : F), ¬ (y ∈ AutoIp.mpDomain T) :=
  ⟨ℝ, inferInstance, Witnesses.Diagonal.H, Witnesses.Diagonal.H, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, Witnesses.Diagonal.T,
    Witnesses.Diagonal.y, Witnesses.Diagonal.notMem_sup_orthogonal_range⟩
