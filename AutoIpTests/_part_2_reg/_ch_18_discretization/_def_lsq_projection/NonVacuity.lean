module

import AutoIp._part_2_reg._ch_18_discretization._def_lsq_projection.Spec -- shake: keep
import AutoIpTests.Witnesses.Diagonal

open scoped InnerProductSpace

/-- The hypotheses of `AutoIp.lsqProjection` can hold together. -/
theorem AutoIp.lsqProjection_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (X : ℕ → Submodule 𝕜 E), ∃ (x11 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (X n)), ∃ (y : F), ∃ (n : ℕ), ∀ (n : ℕ), y ∈ AutoIp.mpDomain (T ∘SL Submodule.starProjection (X n)) :=
  by
  exact ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 1, fun _ => ⊤, fun _ => inferInstance, 1, 0, fun _ =>
      Submodule.mem_sup_left ⟨1, by simp [Submodule.starProjection_top]⟩⟩

/-- The hypotheses of `AutoIp.lsqProjection` can fail. -/
theorem AutoIp.lsqProjection_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (X : ℕ → Submodule 𝕜 E), ∃ (x11 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (X n)), ∃ (y : F), ∃ (n : ℕ), ¬ (∀ (n : ℕ), y ∈ AutoIp.mpDomain (T ∘SL Submodule.starProjection (X n))) :=
  by
  refine ⟨ℝ, inferInstance, Witnesses.Diagonal.H, Witnesses.Diagonal.H, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, Witnesses.Diagonal.T,
    fun _ => ⊤, fun _ => inferInstance, Witnesses.Diagonal.y, 0, fun h => ?_⟩
  have h0 := h 0
  rw [Submodule.starProjection_top, ContinuousLinearMap.comp_id] at h0
  exact Witnesses.Diagonal.notMem_sup_orthogonal_range h0
