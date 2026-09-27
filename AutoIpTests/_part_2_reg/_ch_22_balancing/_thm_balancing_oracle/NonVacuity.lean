module

import AutoIp._part_2_reg._ch_22_balancing._thm_balancing_oracle.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity
import AutoIpTests.Witnesses.Zero

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.balancing_oracle` can hold together. -/
theorem AutoIp.balancing_oracle_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (flt : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (Cflt : ℝ), ∃ (CF : ℝ), ∃ (φ : ℝ → ℝ), ∃ (ρ : ℝ), ∃ (hφ : AutoIp.IsIndexFunction (‖K‖ ^ (2 : ℕ)) φ), ∃ (hρ : (0 : ℝ) < ρ), ∃ (y : F), ∃ (hy : y ∈ AutoIp.mpDomain K), ∃ (δ : ℝ), ∃ (z : F), ∃ (N : ℕ), ∃ (grid : ℕ → (↑(Set.Ioi (0 : ℝ)) : Type)), ∃ (q : ℝ), (AutoIp.IsRegularizingFilter K flt Cflt) ∧ (AutoIp.HasFilterBound K flt CF) ∧ ((↑(AutoIp.moorePenrose K) : ↥(LinearPMap.domain (AutoIp.moorePenrose K)) → E) ⟨y, hy⟩ ∈
  AutoIp.sourceSetIndex hs φ (AutoIp.IsIndexFunction.exists_bound_on_spectrum hs hφ) ρ hρ) ∧ ((0 : ℝ) ≤ δ) ∧ (‖y - z‖ ≤ δ) ∧ ((1 : ℝ) < q) ∧ (∀ (i : ℕ), i + (1 : ℕ) ≤ N → (↑(grid i) : ℝ) = q * (↑(grid (i + (1 : ℕ))) : ℝ)) ∧ (∀ (i j : ℕ),
  i ≤ j →
    j ≤ N →
      ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), φ lam * |(1 : ℝ) - lam * flt (grid j) lam| ≤
        ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), φ lam * |(1 : ℝ) - lam * flt (grid i) lam|) ∧ (∃ i ≤ N,
  ∀ (j : ℕ),
    i ≤ j →
      j ≤ N →
        (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), φ lam * |(1 : ℝ) - lam * flt (grid j) lam|) * ρ ≤
          √(Cflt * CF) * δ * (↑(grid j) : ℝ) ^ (-1 / 2 : ℝ)) :=
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
  have hmp : ∀ (y : ℝ) (hy : y ∈ AutoIp.mpDomain (1 : ℝ →L[ℝ] ℝ)),
      AutoIp.moorePenrose (1 : ℝ →L[ℝ] ℝ) ⟨y, hy⟩ = y := by
    intro y hy
    have h := AutoIp.sub_apply_moorePenrose_mem_orthogonal (T := (1 : ℝ →L[ℝ] ℝ)) ⟨y, hy⟩
    have hr : LinearMap.range ((1 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) = ⊤ := LinearMap.range_id
    simp only [hr, Submodule.top_orthogonal_eq_bot, Submodule.mem_bot, sub_eq_zero] at h
    simpa using h.symm
  have hfc : ∀ (φ : ℝ → ℝ) (hφ : ∃ C, ∀ i : Unit, |φ ((fun _ => (1 : ℝ)) i ^ 2)| ≤ C),
      φ 0 = 0 → ∀ x : ℝ, hone.funCalc φ hφ x = φ 1 * x := by
    intro φ hφ h0 x
    have h := hone.hasSum_funCalc_sub_starProjection hφ x
    rw [h0] at h
    simp only [RCLike.ofReal_real_eq_id, id, zero_smul, sub_zero] at h
    have h2 := h.unique (hasSum_fintype _)
    simpa using h2
  have hy1 : (1 : ℝ) ∈ AutoIp.mpDomain (1 : ℝ →L[ℝ] ℝ) :=
    Submodule.mem_sup_left ⟨1, rfl⟩
  let flt : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ := fun α t => if (α : ℝ) ≤ t then t⁻¹ else 0
  have hflt_le : ∀ (α : (↑(Set.Ioi (0 : ℝ)) : Type)) (t : ℝ), 0 ≤ t →
      |flt α t| ≤ (α : ℝ)⁻¹ := by
    intro α t ht
    have hα : (0 : ℝ) < α := α.2
    simp only [flt]
    split_ifs with h
    · rw [abs_of_pos (inv_pos.2 (hα.trans_le h))]
      exact inv_anti₀ hα h
    · simp only [abs_zero]
      exact (inv_pos.2 hα).le
  have hreg : AutoIp.IsRegularizingFilter (1 : ℝ →L[ℝ] ℝ) flt 1 := by
    refine ⟨one_pos, fun α => ⟨(α : ℝ)⁻¹, fun t ht => hflt_le α t ht.1⟩, fun lam hlam => ?_,
      fun α lam hlam => ?_⟩
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_atBot.2 ⟨⟨lam, hlam.1⟩, fun b hb => hb⟩] with b hb
      have hb' : (b : ℝ) ≤ lam := hb
      simp only [flt]
      rw [if_pos hb']
    · simp only [flt]
      split_ifs with h
      · rw [abs_of_pos (inv_pos.2 hlam.1), mul_inv_cancel₀ hlam.1.ne']
      · simp
  have hFB : AutoIp.HasFilterBound (1 : ℝ →L[ℝ] ℝ) flt 1 := by
    refine ⟨⟨1, hreg⟩, one_pos, fun α => ?_⟩
    have hα : (0 : ℝ) < α := α.2
    rw [one_mul]
    exact Real.iSup_le (fun lam => Real.iSup_le (fun hlam => hflt_le α lam hlam.1.le)
      (inv_pos.2 hα).le) (inv_pos.2 hα).le
  have hbias : ∀ α : (↑(Set.Ioi (0 : ℝ)) : Type),
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ)),
        (fun t : ℝ => t) lam * |1 - lam * flt α lam|) ≤ α := by
    intro α
    have hα : (0 : ℝ) < α := α.2
    refine Real.iSup_le (fun lam => Real.iSup_le (fun hlam => ?_) hα.le) hα.le
    simp only [flt]
    split_ifs with h
    · rw [mul_inv_cancel₀ hlam.1.ne', sub_self, abs_zero, mul_zero]
      exact hα.le
    · rw [mul_zero, sub_zero, abs_one, mul_one]
      exact (not_le.1 h).le
  have hφ : AutoIp.IsIndexFunction (‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ)) (fun t => t) :=
    ⟨rfl, continuousOn_id, fun _ _ _ _ h => h⟩
  let grid : ℕ → (↑(Set.Ioi (0 : ℝ)) : Type) := fun i =>
    ⟨(1 / 2 : ℝ) ^ i, Set.mem_Ioi.2 (pow_pos (by norm_num) i)⟩
  have hgrid_le : ∀ j, ((grid j : ℝ)) ≤ 1 := fun j => pow_le_one₀ (by norm_num) (by norm_num)
  have hgeom : ∀ (i : ℕ), i + (1 : ℕ) ≤ 1 → (↑(grid i) : ℝ) = 2 * (↑(grid (i + (1 : ℕ))) : ℝ) := by
    intro i _
    simp only [grid, pow_succ]
    ring
  have hstar : ∀ (j : ℕ), 0 ≤ j → j ≤ 1 →
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ)),
        (fun t : ℝ => t) lam * |(1 : ℝ) - lam * flt (grid j) lam|) * 1 ≤
        √(1 * 1) * 1 * (↑(grid j) : ℝ) ^ (-1 / 2 : ℝ) := by
    intro j _ _
    rw [mul_one, mul_one, mul_one, Real.sqrt_one, one_mul]
    refine (hbias (grid j)).trans ((hgrid_le j).trans ?_)
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (grid j).2 (hgrid_le j) (by norm_num)
  have hsrc : (AutoIp.moorePenrose (1 : ℝ →L[ℝ] ℝ)) ⟨1, hy1⟩ ∈
      AutoIp.sourceSetIndex hone (fun t => t)
        (AutoIp.IsIndexFunction.exists_bound_on_spectrum hone hφ) 1 one_pos := by
    refine (AutoIp.mem_sourceSetIndex_iff _ _ _ _ _).2 ⟨1, by simp, ?_⟩
    rw [hfc _ _ rfl, hmp]
    norm_num
  have hpt : ∀ (α : (↑(Set.Ioi (0 : ℝ)) : Type)) (lam : ℝ),
      lam ∈ Set.Ioc (0 : ℝ) (‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ)) →
        (fun t : ℝ => t) lam * |1 - lam * flt α lam| ≤ α := by
    intro α lam hlam
    simp only [flt]
    split_ifs with h
    · rw [mul_inv_cancel₀ hlam.1.ne', sub_self, abs_zero, mul_zero]
      exact α.2.le
    · rw [mul_zero, sub_zero, abs_one, mul_one]
      exact (not_le.1 h).le
  have hmono : ∀ (i j : ℕ), i ≤ j → j ≤ 1 →
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ)),
        (fun t : ℝ => t) lam * |(1 : ℝ) - lam * flt (grid j) lam|) ≤
      ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ)),
        (fun t : ℝ => t) lam * |(1 : ℝ) - lam * flt (grid i) lam| := by
    intro i j hij _
    have hα : ((grid j : ℝ)) ≤ grid i := pow_le_pow_of_le_one (by norm_num) (by norm_num) hij
    have hnn : 0 ≤ ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ)),
        (fun t : ℝ => t) lam * |(1 : ℝ) - lam * flt (grid i) lam| :=
      Real.iSup_nonneg fun lam => Real.iSup_nonneg fun hlam =>
        mul_nonneg hlam.1.le (abs_nonneg _)
    have hbdd : BddAbove (Set.range fun lam =>
        ⨆ (_ : lam ∈ Set.Ioc (0 : ℝ) (‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ))),
          (fun t : ℝ => t) lam * |(1 : ℝ) - lam * flt (grid i) lam|) := by
      refine ⟨grid i, ?_⟩
      rintro _ ⟨lam, rfl⟩
      exact Real.iSup_le (fun hlam => hpt (grid i) lam hlam) (grid i).2.le
    refine Real.iSup_le (fun lam => Real.iSup_le (fun hlam => ?_) hnn) hnn
    have hp : (fun t : ℝ => t) lam * |(1 : ℝ) - lam * flt (grid j) lam| ≤
        (fun t : ℝ => t) lam * |(1 : ℝ) - lam * flt (grid i) lam| := by
      simp only [flt]
      split_ifs with h1 h2 h2
      · exact le_rfl
      · rw [mul_inv_cancel₀ hlam.1.ne', sub_self, abs_zero, mul_zero]
        exact mul_nonneg hlam.1.le (abs_nonneg _)
      · exact absurd (hα.trans h2) h1
      · exact le_rfl
    refine hp.trans ?_
    rw [← ciSup_pos (f := fun _ : lam ∈ Set.Ioc (0 : ℝ) (‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ)) =>
      (fun t : ℝ => t) lam * |(1 : ℝ) - lam * flt (grid i) lam|) hlam]
    exact le_ciSup hbdd lam
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1, hone,
    flt, 1, 1, fun t => t, 1, hφ, one_pos, 1, hy1, 1, 0, 1, grid, 2, ?_⟩
  exact ⟨hreg, hFB, hsrc, zero_le_one, by norm_num, by norm_num, hgeom, hmono,
    ⟨0, zero_le_one, hstar⟩⟩

/-- The hypotheses of `AutoIp.balancing_oracle` can fail. -/
theorem AutoIp.balancing_oracle_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (flt : (↑(Set.Ioi (0 : ℝ)) : Type) → ℝ → ℝ), ∃ (Cflt : ℝ), ∃ (CF : ℝ), ∃ (φ : ℝ → ℝ), ∃ (ρ : ℝ), ∃ (hφ : AutoIp.IsIndexFunction (‖K‖ ^ (2 : ℕ)) φ), ∃ (hρ : (0 : ℝ) < ρ), ∃ (y : F), ∃ (hy : y ∈ AutoIp.mpDomain K), ∃ (δ : ℝ), ∃ (z : F), ∃ (N : ℕ), ∃ (grid : ℕ → (↑(Set.Ioi (0 : ℝ)) : Type)), ∃ (q : ℝ), ¬ ((AutoIp.IsRegularizingFilter K flt Cflt) ∧ (AutoIp.HasFilterBound K flt CF) ∧ ((↑(AutoIp.moorePenrose K) : ↥(LinearPMap.domain (AutoIp.moorePenrose K)) → E) ⟨y, hy⟩ ∈
  AutoIp.sourceSetIndex hs φ (AutoIp.IsIndexFunction.exists_bound_on_spectrum hs hφ) ρ hρ) ∧ ((0 : ℝ) ≤ δ) ∧ (‖y - z‖ ≤ δ) ∧ ((1 : ℝ) < q) ∧ (∀ (i : ℕ), i + (1 : ℕ) ≤ N → (↑(grid i) : ℝ) = q * (↑(grid (i + (1 : ℕ))) : ℝ)) ∧ (∀ (i j : ℕ),
  i ≤ j →
    j ≤ N →
      ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), φ lam * |(1 : ℝ) - lam * flt (grid j) lam| ≤
        ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), φ lam * |(1 : ℝ) - lam * flt (grid i) lam|) ∧ (∃ i ≤ N,
  ∀ (j : ℕ),
    i ≤ j →
      j ≤ N →
        (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), φ lam * |(1 : ℝ) - lam * flt (grid j) lam|) * ρ ≤
          √(Cflt * CF) * δ * (↑(grid j) : ℝ) ^ (-1 / 2 : ℝ))) :=
  by
  classical
  have hss : IsSingularSystem (ι := Empty) (0 : ℝ →L[ℝ] ℝ)
      (fun _ => 0) (fun _ => 0) (fun _ => 0) :=
    { pos := fun i => i.elim
      orthonormal_left := ⟨fun i => i.elim, fun {i _} _ => i.elim⟩
      orthonormal_right := ⟨fun i => i.elim, fun {i _} _ => i.elim⟩
      span_left := Witnesses.Zero.span_left _
      span_right := Witnesses.Zero.span_right _
      map_left := fun i => i.elim
      map_right := fun i => i.elim }
  have hφ : AutoIp.IsIndexFunction (‖(0 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ)) (fun t => t) :=
    ⟨rfl, continuousOn_id, fun _ _ _ _ h => h⟩
  have hy : (0 : ℝ) ∈ AutoIp.mpDomain (0 : ℝ →L[ℝ] ℝ) := Submodule.zero_mem _
  have hsup : ∀ f : ℝ → ℝ,
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖(0 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ)), f lam) = 0 := by
    intro f
    simp [Real.iSup_of_isEmpty]
  have hreg : AutoIp.IsRegularizingFilter (0 : ℝ →L[ℝ] ℝ) (fun _ _ => 0) 1 :=
    ⟨by norm_num, fun _ => ⟨0, fun t _ => by simp⟩,
      fun lam hlam => absurd hlam (by simp),
      fun _ lam hlam => absurd hlam (by simp)⟩
  have hF : AutoIp.HasFilterBound (0 : ℝ →L[ℝ] ℝ) (fun _ _ => 0) 1 :=
    ⟨⟨1, hreg⟩, one_pos, fun α => by
      rw [hsup]
      exact mul_nonneg zero_le_one (inv_nonneg.2 (le_of_lt α.2))⟩
  have hsrc : (AutoIp.moorePenrose (0 : ℝ →L[ℝ] ℝ)) ⟨0, hy⟩ ∈
      AutoIp.sourceSetIndex hss (fun t => t) (AutoIp.IsIndexFunction.exists_bound_on_spectrum hss hφ)
        1 one_pos := by
    refine (AutoIp.mem_sourceSetIndex_iff _ _ _ _ _).2 ⟨0, by simp, ?_⟩
    rw [map_zero]
    exact (LinearPMap.map_zero _).symm
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Empty, fun _ => 0, fun _ => 0, fun _ => 0, hss,
    fun _ _ => 0, 0, 1, fun t => t, 1, hφ, one_pos, 0, hy, 0, 0, 0,
    fun _ => ⟨1, Set.mem_Ioi.2 one_pos⟩, 2, ?_⟩
  rintro ⟨H, _⟩
  exact absurd H.const_pos (lt_irrefl 0)
