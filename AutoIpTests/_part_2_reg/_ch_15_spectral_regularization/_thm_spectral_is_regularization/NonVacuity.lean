module

import AutoIp._part_2_reg._ch_15_spectral_regularization._thm_spectral_is_regularization.Spec -- shake: keep
import AutoIpTests.Witnesses.Diagonal
import AutoIpTests.Witnesses.Identity

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.isRegularization_spectralReg` can hold together. -/
theorem AutoIp.isRegularization_spectralReg_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (φ : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (C : ℝ), (IsSingularSystem K σ v u) ∧ (AutoIp.IsRegularizingFilter K φ C) :=
  by
  classical
  have hone : IsSingularSystem (ι := Unit) (1 : ℝ →L[ℝ] ℝ)
      (fun _ => 1) (fun _ => 1) (fun _ => 1) :=
    { pos := fun _ => one_pos
      orthonormal_left := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      orthonormal_right := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      span_left := Witnesses.Identity.span_left _ fun _ => rfl
      span_right := Witnesses.Identity.span_right _ fun _ => rfl
      map_left := fun _ => (one_mul (1 : ℝ)).symm
      map_right := fun _ =>
        (Witnesses.Identity.adjoint_one_apply 1).trans (one_mul (1 : ℝ)).symm }
  set φ : Set.Ioi (0 : ℝ) → ℝ → ℝ := fun α lam => (max (α : ℝ) lam)⁻¹ with hφdef
  have hφa : ∀ (α : Set.Ioi (0 : ℝ)) (lam : ℝ), φ α lam = (max (α : ℝ) lam)⁻¹ :=
    fun _ _ => rfl
  have hmax : ∀ (α : Set.Ioi (0 : ℝ)) (lam : ℝ), 0 < max (α : ℝ) lam := fun α lam =>
    lt_max_of_lt_left α.2
  have habs : ∀ (α : Set.Ioi (0 : ℝ)) (lam : ℝ), |φ α lam| ≤ (α : ℝ)⁻¹ := fun α lam => by
    rw [hφa, abs_of_pos (inv_pos.2 (hmax α lam))]
    exact inv_anti₀ α.2 (le_max_left _ _)
  have hflt : AutoIp.IsRegularizingFilter (1 : ℝ →L[ℝ] ℝ) φ 1 :=
    { const_pos := one_pos
      bddOn := fun α => ⟨(α : ℝ)⁻¹, fun t _ => habs α t⟩
      tendsto_inv := by
        intro lam hlam
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_le_atBot (⟨lam, hlam.1⟩ : Set.Ioi (0 : ℝ))] with α hα
        have hα' : (α : ℝ) ≤ lam := hα
        rw [hφa, max_eq_right hα']
      mul_abs_le := by
        intro α lam hlam
        rw [abs_of_pos (inv_pos.2 (hmax α lam)), ← div_eq_mul_inv, div_le_one (hmax α lam)]
        exact le_max_right _ _ }
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1,
    φ, 1, ?_⟩
  exact ⟨hone, hflt⟩

/-- The hypotheses of `AutoIp.isRegularization_spectralReg` can fail. -/
theorem AutoIp.isRegularization_spectralReg_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (φ : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (C : ℝ), ¬ ((IsSingularSystem K σ v u) ∧ (AutoIp.IsRegularizingFilter K φ C)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, fun _ _ => 0, 1
    , ?_⟩
  rintro ⟨H, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)

/-- The hypotheses of `AutoIp.tendsto_norm_spectralReg_atTop` can hold together. -/
theorem AutoIp.tendsto_norm_spectralReg_atTop_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (φ : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (C : ℝ), ∃ (y : F), (IsSingularSystem K σ v u) ∧ (AutoIp.IsRegularizingFilter K φ C) ∧ (¬∃ (B : ℝ),
    ∀ (y : ↥(LinearPMap.domain (AutoIp.moorePenrose K))),
      ‖(↑(AutoIp.moorePenrose K) : ↥(LinearPMap.domain (AutoIp.moorePenrose K)) → E) y‖ ≤ B * ‖(↑y : F)‖) ∧ (y ∉ AutoIp.mpDomain K) :=
  by
  classical
  have hTe : ∀ n : ℕ, Witnesses.Diagonal.T (Witnesses.Diagonal.e n) =
      (RCLike.ofReal (Witnesses.Diagonal.w n) : ℝ) • Witnesses.Diagonal.e n := by
    intro n
    refine lp.ext (funext fun m => ?_)
    rw [Witnesses.Diagonal.T_apply, lp.coeFn_smul, Pi.smul_apply,
      Witnesses.Diagonal.e_apply, smul_eq_mul]
    split_ifs with h
    · subst h; simp
    · simp
  have hadj : ∀ n : ℕ, ContinuousLinearMap.adjoint Witnesses.Diagonal.T
      (Witnesses.Diagonal.e n) =
      (RCLike.ofReal (Witnesses.Diagonal.w n) : ℝ) • Witnesses.Diagonal.e n := by
    intro n
    refine ext_inner_right ℝ fun x => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, Witnesses.Diagonal.inner_e_left,
      Witnesses.Diagonal.T_apply, real_inner_smul_left, Witnesses.Diagonal.inner_e_left]
    rfl
  have hker : LinearMap.ker (Witnesses.Diagonal.T : Witnesses.Diagonal.H →ₗ[ℝ]
      Witnesses.Diagonal.H) = ⊥ :=
    LinearMap.ker_eq_bot.2 Witnesses.Diagonal.injective_T
  have hss : IsSingularSystem Witnesses.Diagonal.T Witnesses.Diagonal.w
      Witnesses.Diagonal.e Witnesses.Diagonal.e :=
    { pos := Witnesses.Diagonal.w_pos
      orthonormal_left := Witnesses.Diagonal.orthonormal_e
      orthonormal_right := Witnesses.Diagonal.orthonormal_e
      span_left := by
        rw [Witnesses.Diagonal.span_e_dense, hker, Submodule.bot_orthogonal_eq_top]
      span_right := by
        rw [Witnesses.Diagonal.span_e_dense,
          ← Submodule.orthogonal_orthogonal_eq_closure,
          Witnesses.Diagonal.orthogonal_range_eq_bot, Submodule.bot_orthogonal_eq_top]
      map_left := hTe
      map_right := hadj }
  set φ : Set.Ioi (0 : ℝ) → ℝ → ℝ := fun α lam => (max (α : ℝ) lam)⁻¹ with hφdef
  have hφa : ∀ (α : Set.Ioi (0 : ℝ)) (lam : ℝ), φ α lam = (max (α : ℝ) lam)⁻¹ :=
    fun _ _ => rfl
  have hmax : ∀ (α : Set.Ioi (0 : ℝ)) (lam : ℝ), 0 < max (α : ℝ) lam := fun α lam =>
    lt_max_of_lt_left α.2
  have hflt : AutoIp.IsRegularizingFilter Witnesses.Diagonal.T φ 1 :=
    { const_pos := one_pos
      bddOn := fun α => ⟨(α : ℝ)⁻¹, fun t _ => by
        rw [hφa, abs_of_pos (inv_pos.2 (hmax α t))]
        exact inv_anti₀ α.2 (le_max_left _ _)⟩
      tendsto_inv := by
        intro lam hlam
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_le_atBot (⟨lam, hlam.1⟩ : Set.Ioi (0 : ℝ))] with α hα
        have hα' : (α : ℝ) ≤ lam := hα
        rw [hφa, max_eq_right hα']
      mul_abs_le := by
        intro α lam hlam
        rw [hφa, abs_of_pos (inv_pos.2 (hmax α lam)), ← div_eq_mul_inv,
          div_le_one (hmax α lam)]
        exact le_max_right _ _ }
  -- the Moore--Penrose inverse is unbounded: it sends `T (e n)` back to `e n`
  have hunb : ¬ ∃ B : ℝ, ∀ y : (AutoIp.moorePenrose Witnesses.Diagonal.T).domain,
      ‖AutoIp.moorePenrose Witnesses.Diagonal.T y‖ ≤ B * ‖(y : Witnesses.Diagonal.H)‖ := by
    rintro ⟨B, hB⟩
    have hmp : ∀ n : ℕ, ∀ hy : Witnesses.Diagonal.T (Witnesses.Diagonal.e n) ∈
        AutoIp.mpDomain Witnesses.Diagonal.T,
        AutoIp.moorePenrose Witnesses.Diagonal.T ⟨_, hy⟩ = Witnesses.Diagonal.e n := by
      intro n hy
      refine (AutoIp.moorePenrose_isMinimumNorm _).unique
        (AutoIp.isMinimumNorm_iff.2 ⟨?_, ?_⟩)
      · rw [sub_self]; exact Submodule.zero_mem _
      · rw [hker, Submodule.bot_orthogonal_eq_top]; exact Submodule.mem_top
    have hle : ∀ n : ℕ, 1 ≤ B * Witnesses.Diagonal.w n := by
      intro n
      have hy : Witnesses.Diagonal.T (Witnesses.Diagonal.e n) ∈
          AutoIp.mpDomain Witnesses.Diagonal.T :=
        Submodule.mem_sup_left ⟨Witnesses.Diagonal.e n, rfl⟩
      have h := hB ⟨_, hy⟩
      rw [hmp n hy, Witnesses.Diagonal.norm_e] at h
      have hn : ‖Witnesses.Diagonal.T (Witnesses.Diagonal.e n)‖ =
          Witnesses.Diagonal.w n := by
        rw [hTe, norm_smul, Witnesses.Diagonal.norm_e, mul_one]
        exact abs_of_pos (Witnesses.Diagonal.w_pos n)
      simpa [hn] using h
    have hB0 : 0 < B := by
      have h := hle 0
      have hw := Witnesses.Diagonal.w_pos 0
      by_contra hB
      have hB' : B ≤ 0 := not_lt.1 hB
      nlinarith
    have ht := Witnesses.Diagonal.summable_w_sq.tendsto_atTop_zero
    obtain ⟨n, hn⟩ := ((tendsto_order.1 ht).2 (1 / B ^ 2) (by positivity)).exists
    have h1 := hle n
    have hw := Witnesses.Diagonal.w_pos n
    have h2 : (B * Witnesses.Diagonal.w n) ^ 2 < 1 := by
      rw [mul_pow]
      calc B ^ 2 * Witnesses.Diagonal.w n ^ 2 < B ^ 2 * (1 / B ^ 2) :=
            mul_lt_mul_of_pos_left hn (by positivity)
        _ = 1 := by field_simp
    nlinarith
  exact ⟨ℝ, inferInstance, Witnesses.Diagonal.H, Witnesses.Diagonal.H, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Witnesses.Diagonal.T, ℕ, Witnesses.Diagonal.w, Witnesses.Diagonal.e,
    Witnesses.Diagonal.e, φ, 1, Witnesses.Diagonal.y, hss, hflt, hunb,
    Witnesses.Diagonal.notMem_sup_orthogonal_range⟩

/-- The hypotheses of `AutoIp.tendsto_norm_spectralReg_atTop` can fail. -/
theorem AutoIp.tendsto_norm_spectralReg_atTop_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (φ : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (C : ℝ), ∃ (y : F), ¬ ((IsSingularSystem K σ v u) ∧ (AutoIp.IsRegularizingFilter K φ C) ∧ (¬∃ (B : ℝ),
    ∀ (y : ↥(LinearPMap.domain (AutoIp.moorePenrose K))),
      ‖(↑(AutoIp.moorePenrose K) : ↥(LinearPMap.domain (AutoIp.moorePenrose K)) → E) y‖ ≤ B * ‖(↑y : F)‖) ∧ (y ∉ AutoIp.mpDomain K)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, fun _ _ => 0, 1, 0
    , ?_⟩
  rintro ⟨H, _, _, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)
