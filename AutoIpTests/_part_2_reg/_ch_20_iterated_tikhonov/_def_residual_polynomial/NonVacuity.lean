module

import AutoIp._part_2_reg._ch_20_iterated_tikhonov._def_residual_polynomial.Spec -- shake: keep

/-- The hypotheses of `AutoIp.semiIterativeFilter_of_ne_zero` can hold together. -/
theorem AutoIp.semiIterativeFilter_of_ne_zero_satisfiable : ∃ (lam : ℝ), ∃ (q : ℕ → Polynomial ℝ), ∃ (k : ℕ), lam ≠ (0 : ℝ) :=
  by
  refine ⟨1, fun _ => 0, 0, ?_⟩
  exact by norm_num

/-- The hypotheses of `AutoIp.semiIterativeFilter_of_ne_zero` can fail. -/
theorem AutoIp.semiIterativeFilter_of_ne_zero_nontrivial : ∃ (lam : ℝ), ∃ (q : ℕ → Polynomial ℝ), ∃ (k : ℕ), ¬ (lam ≠ (0 : ℝ)) :=
  by
  refine ⟨0, fun _ => 0, 0, ?_⟩
  intro H
  exact H rfl

/-- The hypotheses of `AutoIp.exists_eq_eval_of_isResidualPolynomialFamily` can hold together. -/
theorem AutoIp.exists_eq_eval_of_isResidualPolynomialFamily_satisfiable : ∃ (q : ℕ → Polynomial ℝ), ∃ (k : ℕ), AutoIp.IsResidualPolynomialFamily q :=
  by
  refine ⟨fun _ => 1, 0, ⟨fun k => by simp, fun k => ?_⟩⟩
  exact le_trans Polynomial.degree_one_le (by exact_mod_cast Nat.zero_le k)

/-- The hypotheses of `AutoIp.exists_eq_eval_of_isResidualPolynomialFamily` can fail. -/
theorem AutoIp.exists_eq_eval_of_isResidualPolynomialFamily_nontrivial : ∃ (q : ℕ → Polynomial ℝ), ∃ (k : ℕ), ¬ (AutoIp.IsResidualPolynomialFamily q) :=
  by
  refine ⟨fun _ => 0, 0, ?_⟩
  intro H
  have h := H.eval_zero_eq_one 0
  simp at h
