module

import AutoIp._part_2_reg._ch_20_iterated_tikhonov._thm_semi_iterative_regularization.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity

open Filter Topology

/-- The hypotheses of `AutoIp.semiIterativeFilter_isRegularizingFilter` can hold together. -/
theorem AutoIp.semiIterativeFilter_isRegularizingFilter_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (q : ℕ → Polynomial ℝ), ∃ (Cq : ℝ), ∃ (κ : ℝ → ℕ), (AutoIp.IsResidualPolynomialFamily q) ∧ (∀ (k : ℕ), ∀ lam ∈ Set.Icc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |Polynomial.eval lam (q k)| ≤ Cq) ∧ (∀ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ (2 : ℕ)),
  Filter.Tendsto (fun (k : ℕ) => Polynomial.eval lam (q k)) Filter.atTop (nhds (0 : ℝ))) ∧ (Filter.Tendsto κ (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) Filter.atTop) :=
  by
  classical
  have hq : AutoIp.IsResidualPolynomialFamily
      (fun k => (1 - Polynomial.C (1 / 2 : ℝ) * Polynomial.X) ^ k) := by
    refine ⟨fun k => by simp, fun k => Polynomial.degree_le_of_natDegree_le ?_⟩
    have h1 : (1 - Polynomial.C (1 / 2 : ℝ) * Polynomial.X).natDegree ≤ 1 := by
      compute_degree!
    simpa using Polynomial.natDegree_pow_le_of_le k h1
  have hK : ‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ) = 1 := by
    rw [Witnesses.Identity.norm_one']
    norm_num
  have hev : ∀ (k : ℕ) (lam : ℝ),
      Polynomial.eval lam ((1 - Polynomial.C (1 / 2 : ℝ) * Polynomial.X) ^ k) =
        (1 - lam / 2) ^ k := by
    intro k lam
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  have hb : ∀ (k : ℕ), ∀ lam ∈ Set.Icc (0 : ℝ) (‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ)),
      |Polynomial.eval lam ((fun k => (1 - Polynomial.C (1 / 2 : ℝ) * Polynomial.X) ^ k) k)|
        ≤ 1 := by
    intro k lam hlam
    rw [hK] at hlam
    simp only [hev, abs_pow]
    refine pow_le_one₀ (abs_nonneg _) ?_
    rw [abs_le]
    constructor <;> linarith [hlam.1, hlam.2]
  have hc : ∀ lam ∈ Set.Ioc (0 : ℝ) (‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ)),
      Filter.Tendsto (fun (k : ℕ) => Polynomial.eval lam
        ((fun k => (1 - Polynomial.C (1 / 2 : ℝ) * Polynomial.X) ^ k) k))
        Filter.atTop (nhds (0 : ℝ)) := by
    intro lam hlam
    rw [hK] at hlam
    simp only [hev]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith [hlam.2]) (by linarith [hlam.1])
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    1, fun k => (1 - Polynomial.C (1 / 2 : ℝ) * Polynomial.X) ^ k, 1, fun t => ⌈t⁻¹⌉₊,
    hq, hb, hc, ?_⟩
  exact tendsto_nat_ceil_atTop.comp tendsto_inv_nhdsGT_zero

/-- The hypotheses of `AutoIp.semiIterativeFilter_isRegularizingFilter` can fail. -/
theorem AutoIp.semiIterativeFilter_isRegularizingFilter_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : NormedAddCommGroup F), ∃ (x7 : InnerProductSpace 𝕜 F), ∃ (K : E →L[𝕜] F), ∃ (q : ℕ → Polynomial ℝ), ∃ (Cq : ℝ), ∃ (κ : ℝ → ℕ), ¬ ((AutoIp.IsResidualPolynomialFamily q) ∧ (∀ (k : ℕ), ∀ lam ∈ Set.Icc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |Polynomial.eval lam (q k)| ≤ Cq) ∧ (∀ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ (2 : ℕ)),
  Filter.Tendsto (fun (k : ℕ) => Polynomial.eval lam (q k)) Filter.atTop (nhds (0 : ℝ))) ∧ (Filter.Tendsto κ (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) Filter.atTop)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    0, fun _ => 0, 1, fun _ => 0, ?_⟩
  rintro ⟨H, _⟩
  have h := H.eval_zero_eq_one 0
  simp at h

/-- The hypotheses of `AutoIp.isRegularization_semiIterativeFilter` can hold together. -/
theorem AutoIp.isRegularization_semiIterativeFilter_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (q : ℕ → Polynomial ℝ), ∃ (Cq : ℝ), (IsSingularSystem K σ v u) ∧ (AutoIp.IsResidualPolynomialFamily q) ∧ (∀ (k : ℕ), ∀ lam ∈ Set.Icc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |Polynomial.eval lam (q k)| ≤ Cq) ∧ (∀ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ (2 : ℕ)),
  Filter.Tendsto (fun (k : ℕ) => Polynomial.eval lam (q k)) Filter.atTop (nhds (0 : ℝ))) :=
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
  have hq : AutoIp.IsResidualPolynomialFamily
      (fun k => (1 - Polynomial.C (1 / 2 : ℝ) * Polynomial.X) ^ k) := by
    refine ⟨fun k => by simp, fun k => Polynomial.degree_le_of_natDegree_le ?_⟩
    have h1 : (1 - Polynomial.C (1 / 2 : ℝ) * Polynomial.X).natDegree ≤ 1 := by
      compute_degree!
    simpa using Polynomial.natDegree_pow_le_of_le k h1
  have hK : ‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ) = 1 := by
    rw [Witnesses.Identity.norm_one']
    norm_num
  have hev : ∀ (k : ℕ) (lam : ℝ),
      Polynomial.eval lam ((1 - Polynomial.C (1 / 2 : ℝ) * Polynomial.X) ^ k) =
        (1 - lam / 2) ^ k := by
    intro k lam
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  have hb : ∀ (k : ℕ), ∀ lam ∈ Set.Icc (0 : ℝ) (‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ)),
      |Polynomial.eval lam ((fun k => (1 - Polynomial.C (1 / 2 : ℝ) * Polynomial.X) ^ k) k)|
        ≤ 1 := by
    intro k lam hlam
    rw [hK] at hlam
    simp only [hev, abs_pow]
    refine pow_le_one₀ (abs_nonneg _) ?_
    rw [abs_le]
    constructor <;> linarith [hlam.1, hlam.2]
  have hc : ∀ lam ∈ Set.Ioc (0 : ℝ) (‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ)),
      Filter.Tendsto (fun (k : ℕ) => Polynomial.eval lam
        ((fun k => (1 - Polynomial.C (1 / 2 : ℝ) * Polynomial.X) ^ k) k))
        Filter.atTop (nhds (0 : ℝ)) := by
    intro lam hlam
    rw [hK] at hlam
    simp only [hev]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith [hlam.2]) (by linarith [hlam.1])
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1,
    fun k => (1 - Polynomial.C (1 / 2 : ℝ) * Polynomial.X) ^ k, 1, ?_⟩
  exact ⟨hone, hq, hb, hc⟩

/-- The hypotheses of `AutoIp.isRegularization_semiIterativeFilter` can fail. -/
theorem AutoIp.isRegularization_semiIterativeFilter_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (q : ℕ → Polynomial ℝ), ∃ (Cq : ℝ), ¬ ((IsSingularSystem K σ v u) ∧ (AutoIp.IsResidualPolynomialFamily q) ∧ (∀ (k : ℕ), ∀ lam ∈ Set.Icc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), |Polynomial.eval lam (q k)| ≤ Cq) ∧ (∀ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ (2 : ℕ)),
  Filter.Tendsto (fun (k : ℕ) => Polynomial.eval lam (q k)) Filter.atTop (nhds (0 : ℝ)))) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, 0, ?_⟩
  rintro ⟨H, _, _, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)
