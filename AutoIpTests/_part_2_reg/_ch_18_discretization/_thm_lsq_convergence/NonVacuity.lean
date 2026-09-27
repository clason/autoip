module

import AutoIp._part_2_reg._ch_18_discretization._thm_lsq_convergence.Spec -- shake: keep
import AutoIpTests.Witnesses.Diagonal
import AutoIpTests.Witnesses.Filtration

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.lsq_tendsto` can hold together. -/
theorem AutoIp.lsq_tendsto_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (X : ℕ → Submodule 𝕜 E), ∃ (x12 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (X n)), ∃ (hmono : Monotone X), ∃ (hfin : ∀ (n : ℕ), Module.finrank 𝕜 ↥(X n) = n), ∃ (y : F), (Submodule.topologicalClosure (⨆ (n : ℕ), X n) = ⊤) ∧ (y ∈ AutoIp.mpDomain T) ∧ (Filter.limsup
    (fun (n : ℕ) =>
      ‖((ContinuousLinearMap.adjoint : (F →L[𝕜] E) → E →L[𝕜] F)
              (AutoIp.moorePenroseL (AutoIp.isClosed_range_lsq T X hmono hfin n)) :
            E → F)
          (AutoIp.lsqProjection T X y (AutoIp.mem_mpDomain_lsq T X hmono hfin y) n)‖ₑ)
    Filter.atTop <
  ⊤) :=
  by
  classical
  have hTx : ∀ h, ContinuousLinearMap.adjoint Witnesses.Filtration.K h =
      ⟪Witnesses.Filtration.b 0, h⟫_ℝ := Witnesses.Filtration.adjoint_K_apply
  have hTn : ∀ n, 0 < n → ∀ h, (ContinuousLinearMap.adjoint Witnesses.Filtration.K ∘L
      (Witnesses.Filtration.X n).starProjection) h = ⟪Witnesses.Filtration.b 0, h⟫_ℝ := by
    intro n hn h
    rw [ContinuousLinearMap.comp_apply, hTx, ← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 (Witnesses.Filtration.b_zero_mem hn)]
  have hT0 : ∀ h, (ContinuousLinearMap.adjoint Witnesses.Filtration.K ∘L
      (Witnesses.Filtration.X 0).starProjection) h = 0 := by
    intro h
    have hX0 : Witnesses.Filtration.X 0 = ⊥ :=
      Submodule.finrank_eq_zero.1 (Witnesses.Filtration.finrank_X 0)
    have hP : (Witnesses.Filtration.X 0).starProjection h = 0 := by
      have hm := (Witnesses.Filtration.X 0).starProjection_apply_mem h
      exact (Submodule.mem_bot ℝ).1 (hX0.le hm)
    rw [ContinuousLinearMap.comp_apply, hP, map_zero]
  have hbb := Witnesses.Filtration.inner_b_zero_self
  -- the discrete Moore–Penrose inverses are `r ↦ r • b 0` (or `0`), so of norm at most one
  have hM : ∀ n (r : ℝ), ‖AutoIp.moorePenroseL (AutoIp.isClosed_range_lsq
      (ContinuousLinearMap.adjoint Witnesses.Filtration.K) Witnesses.Filtration.X
      Witnesses.Filtration.mono Witnesses.Filtration.finrank_X n) r‖ ≤ ‖r‖ := by
    intro n r
    rw [AutoIp.moorePenroseL_apply]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [(AutoIp.moorePenrose_eq_zero_iff _).2, norm_zero]
      · exact norm_nonneg _
      rw [Submodule.mem_orthogonal]
      rintro _ ⟨x, rfl⟩
      rw [ContinuousLinearMap.coe_coe, hT0, inner_zero_left]
    · rw [← AutoIp.eq_moorePenrose_of_apply_eq_of_eq_zero
        (S := fun s : ℝ => s • Witnesses.Filtration.b 0) (fun a _ c _ => add_smul a c _)
        ?_ ?_ _, norm_smul, Witnesses.Filtration.b.orthonormal.1 0, mul_one]
      · intro x hx
        rw [hTn n hn]
        set w := x - ⟪Witnesses.Filtration.b 0, x⟫_ℝ • Witnesses.Filtration.b 0 with hw
        have hbw : ⟪Witnesses.Filtration.b 0, w⟫_ℝ = 0 := by
          rw [hw, inner_sub_right, real_inner_smul_right, hbb, mul_one, sub_self]
        have hwk : w ∈ LinearMap.ker (ContinuousLinearMap.adjoint Witnesses.Filtration.K ∘L
            (Witnesses.Filtration.X n).starProjection).toLinearMap := by
          rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hTn n hn, hbw]
        have hxw : ⟪x, w⟫_ℝ = 0 := by
          rw [real_inner_comm]; exact Submodule.inner_right_of_mem_orthogonal hwk hx
        have hww : ⟪w, w⟫_ℝ = 0 := by
          rw [hw, inner_sub_left, real_inner_smul_left, ← hw, hxw, hbw, mul_zero, sub_zero]
        have h0 : w = 0 := inner_self_eq_zero.1 hww
        rw [hw, sub_eq_zero] at h0
        exact h0.symm
      · intro s hs
        have h1 : (1 : ℝ) ∈ LinearMap.range (ContinuousLinearMap.adjoint
            Witnesses.Filtration.K ∘L (Witnesses.Filtration.X n).starProjection).toLinearMap :=
          ⟨Witnesses.Filtration.b 0, by rw [ContinuousLinearMap.coe_coe, hTn n hn, hbb]⟩
        have hs0 : ⟪(1 : ℝ), s⟫_ℝ = 0 := Submodule.inner_right_of_mem_orthogonal h1 hs
        have hs1 : s = 0 := by simpa using hs0
        rw [hs1, zero_smul]
  have hbound : ∀ n, ‖((ContinuousLinearMap.adjoint (AutoIp.moorePenroseL
      (AutoIp.isClosed_range_lsq (ContinuousLinearMap.adjoint Witnesses.Filtration.K)
        Witnesses.Filtration.X Witnesses.Filtration.mono Witnesses.Filtration.finrank_X n)))
      (AutoIp.lsqProjection (ContinuousLinearMap.adjoint Witnesses.Filtration.K)
        Witnesses.Filtration.X 1 (AutoIp.mem_mpDomain_lsq
          (ContinuousLinearMap.adjoint Witnesses.Filtration.K) Witnesses.Filtration.X
          Witnesses.Filtration.mono Witnesses.Filtration.finrank_X 1) n))‖ ≤ 1 := by
    intro n
    set M := AutoIp.moorePenroseL (AutoIp.isClosed_range_lsq
      (ContinuousLinearMap.adjoint Witnesses.Filtration.K) Witnesses.Filtration.X
      Witnesses.Filtration.mono Witnesses.Filtration.finrank_X n) with hMdef
    have hMn : ‖M‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      fun r => by rw [one_mul]; exact hM n r
    have hx : AutoIp.lsqProjection (ContinuousLinearMap.adjoint Witnesses.Filtration.K)
        Witnesses.Filtration.X 1 (AutoIp.mem_mpDomain_lsq
          (ContinuousLinearMap.adjoint Witnesses.Filtration.K) Witnesses.Filtration.X
          Witnesses.Filtration.mono Witnesses.Filtration.finrank_X 1) n = M 1 := by
      rw [AutoIp.lsqProjection_def, hMdef, AutoIp.moorePenroseL_apply]
    rw [hx]
    calc ‖(ContinuousLinearMap.adjoint M) (M 1)‖ ≤ ‖ContinuousLinearMap.adjoint M‖ * ‖M 1‖ :=
          (ContinuousLinearMap.adjoint M).le_opNorm _
      _ ≤ 1 * 1 := by
          rw [LinearIsometryEquiv.norm_map]
          refine mul_le_mul hMn ?_ (norm_nonneg _) zero_le_one
          simpa using hM n 1
      _ = 1 := one_mul 1
  have hlim : Filter.limsup (fun n : ℕ => ‖((ContinuousLinearMap.adjoint (AutoIp.moorePenroseL
      (AutoIp.isClosed_range_lsq (ContinuousLinearMap.adjoint Witnesses.Filtration.K)
        Witnesses.Filtration.X Witnesses.Filtration.mono Witnesses.Filtration.finrank_X n)))
      (AutoIp.lsqProjection (ContinuousLinearMap.adjoint Witnesses.Filtration.K)
        Witnesses.Filtration.X 1 (AutoIp.mem_mpDomain_lsq
          (ContinuousLinearMap.adjoint Witnesses.Filtration.K) Witnesses.Filtration.X
          Witnesses.Filtration.mono Witnesses.Filtration.finrank_X 1) n))‖ₑ) atTop < ⊤ := by
    refine lt_of_le_of_lt (Filter.limsup_le_iSup.trans (iSup_le fun n => ?_))
      (ENNReal.one_lt_top)
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  refine ⟨ℝ, inferInstance, Witnesses.Filtration.H, ℝ, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    ContinuousLinearMap.adjoint Witnesses.Filtration.K, Witnesses.Filtration.X,
    fun _ => inferInstance, Witnesses.Filtration.mono, Witnesses.Filtration.finrank_X, 1,
    Witnesses.Filtration.dense,
    Submodule.mem_sup_left ⟨Witnesses.Filtration.b 0, by
      rw [ContinuousLinearMap.coe_coe, hTx, hbb]⟩, hlim⟩

/-- The hypotheses of `AutoIp.lsq_tendsto` can fail. -/
theorem AutoIp.lsq_tendsto_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (T : E →L[𝕜] F), ∃ (X : ℕ → Submodule 𝕜 E), ∃ (x12 : ∀ (n : ℕ), Submodule.HasOrthogonalProjection (X n)), ∃ (hmono : Monotone X), ∃ (hfin : ∀ (n : ℕ), Module.finrank 𝕜 ↥(X n) = n), ∃ (y : F), ¬ ((Submodule.topologicalClosure (⨆ (n : ℕ), X n) = ⊤) ∧ (y ∈ AutoIp.mpDomain T) ∧ (Filter.limsup
    (fun (n : ℕ) =>
      ‖((ContinuousLinearMap.adjoint : (F →L[𝕜] E) → E →L[𝕜] F)
              (AutoIp.moorePenroseL (AutoIp.isClosed_range_lsq T X hmono hfin n)) :
            E → F)
          (AutoIp.lsqProjection T X y (AutoIp.mem_mpDomain_lsq T X hmono hfin y) n)‖ₑ)
    Filter.atTop <
  ⊤)) :=
  by
  refine ⟨ℝ, inferInstance, Witnesses.Filtration.H, Witnesses.Filtration.H, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Witnesses.Diagonal.T, Witnesses.Filtration.X, fun _ => inferInstance,
    Witnesses.Filtration.mono, Witnesses.Filtration.finrank_X, Witnesses.Diagonal.y, ?_⟩
  rintro ⟨_, hy, _⟩
  exact Witnesses.Diagonal.notMem_sup_orthogonal_range hy
