module

import AutoIp._part_2_reg._ch_13_regularization._thm_reg_diverges_outside_domain.Spec -- shake: keep
import AutoIpTests.Witnesses.Diagonal
import AutoIpTests.Witnesses.DiagonalCutoff

open Filter Topology

/-- The hypotheses of `AutoIp.tendsto_norm_atTop_of_notMem_mpDomain` can hold together. -/
theorem AutoIp.tendsto_norm_atTop_of_notMem_mpDomain_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), ∃ (y : F), (AutoIp.IsRegularization T R) ∧ (∃ (C : ℝ), ∀ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ‖T ∘SL R α‖ ≤ C) ∧ (y ∉ AutoIp.mpDomain T) :=
  by
  have hmp : ∀ (y : Witnesses.Diagonal.H) (hy : y ∈ AutoIp.mpDomain Witnesses.Diagonal.T)
      (x : Witnesses.Diagonal.H), Witnesses.Diagonal.T x = y →
      AutoIp.moorePenrose Witnesses.Diagonal.T ⟨y, hy⟩ = x := by
    intro y hy x hx
    refine (AutoIp.moorePenrose_isMinimumNorm (T := Witnesses.Diagonal.T) ⟨y, hy⟩).unique ?_
    rw [AutoIp.isMinimumNorm_iff]
    refine ⟨by rw [hx, sub_self]; exact Submodule.zero_mem _, ?_⟩
    rw [LinearMap.ker_eq_bot.2 Witnesses.Diagonal.injective_T, Submodule.bot_orthogonal_eq_top]
    exact Submodule.mem_top
  have hreg : AutoIp.IsRegularization Witnesses.Diagonal.T Witnesses.DiagonalCutoff.R := by
    intro y hy
    have hy' : y ∈ LinearMap.range (Witnesses.Diagonal.T : Witnesses.Diagonal.H →ₗ[ℝ] _) := by
      have h := hy
      unfold AutoIp.mpDomain at h
      rwa [Witnesses.Diagonal.sup_orthogonal_range_eq] at h
    obtain ⟨x, hx⟩ := hy'
    rw [hmp y hy x hx]
    subst hx
    exact Witnesses.DiagonalCutoff.tendsto_R_T x
  exact ⟨ℝ, inferInstance, Witnesses.Diagonal.H, Witnesses.Diagonal.H, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Witnesses.Diagonal.T, Witnesses.DiagonalCutoff.R, Witnesses.Diagonal.y, hreg,
    ⟨1, Witnesses.DiagonalCutoff.norm_T_comp_R_le⟩, Witnesses.Diagonal.notMem_sup_orthogonal_range⟩

/-- The hypotheses of `AutoIp.tendsto_norm_atTop_of_notMem_mpDomain` can fail. -/
theorem AutoIp.tendsto_norm_atTop_of_notMem_mpDomain_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), ∃ (y : F), ¬ ((AutoIp.IsRegularization T R) ∧ (∃ (C : ℝ), ∀ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ‖T ∘SL R α‖ ≤ C) ∧ (y ∉ AutoIp.mpDomain T)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, 0, 0, ?_⟩
  rintro ⟨H, _, _⟩
  exact absurd H (by simp_all)
