module

import AutoIp._part_2_reg._ch_13_regularization._thm_reg_not_uniformly_bounded.Spec -- shake: keep
import AutoIpTests.Witnesses.Diagonal
import AutoIpTests.Witnesses.DiagonalCutoff

open Filter Topology

/-- The hypotheses of `AutoIp.exists_mem_Ioo_lt_opNorm` can hold together. -/
theorem AutoIp.exists_mem_Ioo_lt_opNorm_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), ∃ (C : ℝ), ∃ (ε : ℝ), (AutoIp.IsRegularization T R) ∧ (¬∃ (C : ℝ),
    ∀ (y : F) (hy : y ∈ AutoIp.mpDomain T),
      ‖(↑(AutoIp.moorePenrose T) : ↥(LinearPMap.domain (AutoIp.moorePenrose T)) → E) ⟨y, hy⟩‖ ≤ C * ‖y‖) ∧ ((0 : ℝ) < ε) :=
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
  have hunb : ¬∃ (C : ℝ), ∀ (y : Witnesses.Diagonal.H) (hy : y ∈ AutoIp.mpDomain Witnesses.Diagonal.T),
      ‖(↑(AutoIp.moorePenrose Witnesses.Diagonal.T) :
        ↥(LinearPMap.domain (AutoIp.moorePenrose Witnesses.Diagonal.T)) → Witnesses.Diagonal.H)
          ⟨y, hy⟩‖ ≤ C * ‖y‖ := by
    rintro ⟨C, hC⟩
    refine Witnesses.DiagonalCutoff.not_exists_norm_le_mul_norm_T ⟨C, fun x => ?_⟩
    have hx : Witnesses.Diagonal.T x ∈ AutoIp.mpDomain Witnesses.Diagonal.T :=
      Submodule.mem_sup_left ⟨x, rfl⟩
    have h := hC (Witnesses.Diagonal.T x) hx
    rwa [hmp _ hx x rfl] at h
  exact ⟨ℝ, inferInstance, Witnesses.Diagonal.H, Witnesses.Diagonal.H, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, Witnesses.Diagonal.T,
    Witnesses.DiagonalCutoff.R, 0, 1, hreg, hunb, one_pos⟩

/-- The hypotheses of `AutoIp.exists_mem_Ioo_lt_opNorm` can fail. -/
theorem AutoIp.exists_mem_Ioo_lt_opNorm_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), ∃ (C : ℝ), ∃ (ε : ℝ), ¬ ((AutoIp.IsRegularization T R) ∧ (¬∃ (C : ℝ),
    ∀ (y : F) (hy : y ∈ AutoIp.mpDomain T),
      ‖(↑(AutoIp.moorePenrose T) : ↥(LinearPMap.domain (AutoIp.moorePenrose T)) → E) ⟨y, hy⟩‖ ≤ C * ‖y‖) ∧ ((0 : ℝ) < ε)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 0, fun _ => 0, 0, 0, ?_⟩
  rintro ⟨-, -, h⟩
  exact lt_irrefl _ h

/-- The hypotheses of `AutoIp.exists_tendsto_norm_atTop` can hold together. -/
theorem AutoIp.exists_tendsto_norm_atTop_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), (AutoIp.IsRegularization T R) ∧ (¬∃ (C : ℝ),
    ∀ (y : F) (hy : y ∈ AutoIp.mpDomain T),
      ‖(↑(AutoIp.moorePenrose T) : ↥(LinearPMap.domain (AutoIp.moorePenrose T)) → E) ⟨y, hy⟩‖ ≤ C * ‖y‖) :=
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
  have hunb : ¬∃ (C : ℝ), ∀ (y : Witnesses.Diagonal.H) (hy : y ∈ AutoIp.mpDomain Witnesses.Diagonal.T),
      ‖(↑(AutoIp.moorePenrose Witnesses.Diagonal.T) :
        ↥(LinearPMap.domain (AutoIp.moorePenrose Witnesses.Diagonal.T)) → Witnesses.Diagonal.H)
          ⟨y, hy⟩‖ ≤ C * ‖y‖ := by
    rintro ⟨C, hC⟩
    refine Witnesses.DiagonalCutoff.not_exists_norm_le_mul_norm_T ⟨C, fun x => ?_⟩
    have hx : Witnesses.Diagonal.T x ∈ AutoIp.mpDomain Witnesses.Diagonal.T :=
      Submodule.mem_sup_left ⟨x, rfl⟩
    have h := hC (Witnesses.Diagonal.T x) hx
    rwa [hmp _ hx x rfl] at h
  exact ⟨ℝ, inferInstance, Witnesses.Diagonal.H, Witnesses.Diagonal.H, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Witnesses.Diagonal.T, Witnesses.DiagonalCutoff.R, hreg, hunb⟩

/-- The hypotheses of `AutoIp.exists_tendsto_norm_atTop` can fail. -/
theorem AutoIp.exists_tendsto_norm_atTop_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (R : (↑(Set.Ioi (0 : ℝ)) : Type) → F →L[𝕜] E), ¬ ((AutoIp.IsRegularization T R) ∧ (¬∃ (C : ℝ),
    ∀ (y : F) (hy : y ∈ AutoIp.mpDomain T),
      ‖(↑(AutoIp.moorePenrose T) : ↥(LinearPMap.domain (AutoIp.moorePenrose T)) → E) ⟨y, hy⟩‖ ≤ C * ‖y‖)) :=
  by
  have hZ : ∀ p q : EuclideanSpace ℝ (Fin 0), p = q := fun p q => by ext i; exact i.elim0
  refine ⟨ℝ, inferInstance, EuclideanSpace ℝ (Fin 0), ℝ, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, 0, fun _ => 0, ?_⟩
  rintro ⟨-, h⟩
  refine h ⟨0, fun y hy => le_of_eq ?_⟩
  rw [zero_mul, norm_eq_zero]
  exact hZ _ _
