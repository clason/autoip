module

import AutoIp._part_2_reg._ch_18_discretization._lem_lsq_comparison.Spec -- shake: keep
import AutoIpTests.Witnesses.Diagonal
import AutoIpTests.Witnesses.Zero

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.norm_apply_lsqProjection_sub_le` can hold together. -/
theorem AutoIp.norm_apply_lsqProjection_sub_le_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (X : ℕ → Submodule 𝕜 E), ∃ (x12 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (X n)), ∃ (y : F), ∃ (n : ℕ), (∀ (n : ℕ), FiniteDimensional 𝕜 ↥(X n)) ∧ (y ∈ AutoIp.mpDomain T) :=
  by
  exact ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, fun _ => ⊤, fun _ => inferInstance, 1, 0,
    fun _ => inferInstance, Submodule.mem_sup_left ⟨1, rfl⟩⟩

/-- The hypotheses of `AutoIp.norm_apply_lsqProjection_sub_le` can fail. -/
theorem AutoIp.norm_apply_lsqProjection_sub_le_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (X : ℕ → Submodule 𝕜 E), ∃ (x12 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (X n)), ∃ (y : F), ∃ (n : ℕ), ¬ ((∀ (n : ℕ), FiniteDimensional 𝕜 ↥(X n)) ∧ (y ∈ AutoIp.mpDomain T)) :=
  by
  refine ⟨ℝ, inferInstance, Witnesses.Diagonal.H, Witnesses.Diagonal.H, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Witnesses.Diagonal.T,
    fun _ => ⊥, fun _ => inferInstance, Witnesses.Diagonal.y, 0, ?_⟩
  rintro ⟨_, hy⟩
  exact Witnesses.Diagonal.notMem_sup_orthogonal_range hy

/-- The hypotheses of `AutoIp.tendsto_opNorm_mul_norm_sub_starProjection` can hold together. -/
theorem AutoIp.tendsto_opNorm_mul_norm_sub_starProjection_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (X : ℕ → Submodule 𝕜 E), ∃ (x11 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (X n)), ∃ (y : F), (Monotone X) ∧ (Submodule.topologicalClosure (⨆ (n : ℕ), X n) = ⊤) ∧ (y ∈ AutoIp.mpDomain T) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 1, fun _ => ⊤, fun _ => inferInstance, 1, monotone_const, ?_,
    Submodule.mem_sup_left ⟨1, rfl⟩⟩
  rw [iSup_const]
  exact le_antisymm le_top (Submodule.le_topologicalClosure _)

/-- The hypotheses of `AutoIp.tendsto_opNorm_mul_norm_sub_starProjection` can fail. -/
theorem AutoIp.tendsto_opNorm_mul_norm_sub_starProjection_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (X : ℕ → Submodule 𝕜 E), ∃ (x11 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (X n)), ∃ (y : F), ¬ ((Monotone X) ∧ (Submodule.topologicalClosure (⨆ (n : ℕ), X n) = ⊤) ∧ (y ∈ AutoIp.mpDomain T)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 0, fun _ => ⊥, fun _ => inferInstance, 0, ?_⟩
  rintro ⟨_, h, _⟩
  rw [iSup_const, Witnesses.Zero.topologicalClosure_bot] at h
  exact bot_ne_top h
