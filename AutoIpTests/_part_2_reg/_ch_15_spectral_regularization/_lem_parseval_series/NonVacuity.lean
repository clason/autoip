module

import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_parseval_series.Spec -- shake: keep

/-- The hypotheses of `Orthonormal.exists_hasSum_of_summable_norm_sq` can hold together. -/
theorem Orthonormal.exists_hasSum_of_summable_norm_sq_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (x3 : NormedAddCommGroup E), ∃ (x4 : InnerProductSpace 𝕜 E), ∃ (ι : Type), ∃ (x6 : CompleteSpace E), ∃ (e : ι → E), ∃ (c : ι → 𝕜), (Orthonormal 𝕜 e) ∧ (Summable fun (n : ι) => ‖c n‖ ^ (2 : ℕ)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, Unit, inferInstance, fun _ => 1,
    fun _ => 1, ?_⟩
  exact ⟨⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩,
    (hasSum_fintype _).summable⟩

/-- The hypotheses of `Orthonormal.exists_hasSum_of_summable_norm_sq` can fail. -/
theorem Orthonormal.exists_hasSum_of_summable_norm_sq_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (x3 : NormedAddCommGroup E), ∃ (x4 : InnerProductSpace 𝕜 E), ∃ (ι : Type), ∃ (x6 : CompleteSpace E), ∃ (e : ι → E), ∃ (c : ι → 𝕜), ¬ ((Orthonormal 𝕜 e) ∧ (Summable fun (n : ι) => ‖c n‖ ^ (2 : ℕ))) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, Unit, inferInstance, fun _ => 0,
    fun _ => 0, ?_⟩
  rintro ⟨h, -⟩
  have h1 := h.1 ()
  simp at h1
