module

import AutoIp._part_1_funcanal._ch_04_orthonormal_series._lem_riesz_fischer.Spec -- shake: keep

/-- The hypotheses of `Orthonormal.inner_right_of_hasSum` can hold together. -/
theorem Orthonormal.inner_right_of_hasSum_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (x3 : NormedAddCommGroup E), ∃ (x4 : InnerProductSpace 𝕜 E), ∃ (ι : Type), ∃ (e : ι → E), ∃ (c : ι → 𝕜), ∃ (x : E), ∃ (j : ι), (Orthonormal 𝕜 e) ∧ (HasSum (fun (i : ι) => c i • e i) x) :=
  ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, Unit, fun _ => (1 : ℝ),
    fun _ => (0 : ℝ), 0, (),
    ⟨⟨fun _ => by simp, fun {i j} hij => absurd (Subsingleton.elim i j) hij⟩, by simpa using hasSum_zero⟩⟩

/-- The hypotheses of `Orthonormal.inner_right_of_hasSum` can fail. -/
theorem Orthonormal.inner_right_of_hasSum_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (x3 : NormedAddCommGroup E), ∃ (x4 : InnerProductSpace 𝕜 E), ∃ (ι : Type), ∃ (e : ι → E), ∃ (c : ι → 𝕜), ∃ (x : E), ∃ (j : ι), ¬ ((Orthonormal 𝕜 e) ∧ (HasSum (fun (i : ι) => c i • e i) x)) :=
  ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, Unit, fun _ => (0 : ℝ),
    fun _ => (0 : ℝ), 0, (), by
      rintro ⟨⟨h, -⟩, -⟩
      simpa using h ()⟩

/-- The hypotheses of `Orthonormal.norm_sq_eq_tsum_norm_sq` can hold together. -/
theorem Orthonormal.norm_sq_eq_tsum_norm_sq_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (x3 : NormedAddCommGroup E), ∃ (x4 : InnerProductSpace 𝕜 E), ∃ (ι : Type), ∃ (e : ι → E), ∃ (c : ι → 𝕜), ∃ (x : E), (Orthonormal 𝕜 e) ∧ (HasSum (fun (i : ι) => c i • e i) x) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, Empty, fun _ => 0, fun _ => 0, 0, ?_⟩
  exact ⟨⟨fun i => i.elim, fun {i _} _ => i.elim⟩, by simp⟩

/-- The hypotheses of `Orthonormal.norm_sq_eq_tsum_norm_sq` can fail. -/
theorem Orthonormal.norm_sq_eq_tsum_norm_sq_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (x3 : NormedAddCommGroup E), ∃ (x4 : InnerProductSpace 𝕜 E), ∃ (ι : Type), ∃ (e : ι → E), ∃ (c : ι → 𝕜), ∃ (x : E), ¬ ((Orthonormal 𝕜 e) ∧ (HasSum (fun (i : ι) => c i • e i) x)) :=
  ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, Unit, fun _ => (0 : ℝ),
    fun _ => (0 : ℝ), 0, by
      rintro ⟨⟨h, -⟩, -⟩
      simpa using h ()⟩

/-- The hypotheses of `Orthonormal.summable_iff_norm_sq_summable` can hold together. -/
theorem Orthonormal.summable_iff_norm_sq_summable_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (x3 : NormedAddCommGroup E), ∃ (x4 : InnerProductSpace 𝕜 E), ∃ (ι : Type), ∃ (x6 : CompleteSpace E), ∃ (e : ι → E), ∃ (c : ι → 𝕜), Orthonormal 𝕜 e :=
  by
  refine ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, Empty, inferInstance, fun _ => 0,
    fun _ => 0, ?_⟩
  exact ⟨fun i => i.elim, fun {i _} _ => i.elim⟩

/-- The hypotheses of `Orthonormal.summable_iff_norm_sq_summable` can fail. -/
theorem Orthonormal.summable_iff_norm_sq_summable_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (x3 : NormedAddCommGroup E), ∃ (x4 : InnerProductSpace 𝕜 E), ∃ (ι : Type), ∃ (x6 : CompleteSpace E), ∃ (e : ι → E), ∃ (c : ι → 𝕜), ¬ (Orthonormal 𝕜 e) :=
  ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, Unit, inferInstance,
    fun _ => (0 : ℝ), fun _ => (0 : ℝ), by
      rintro ⟨h, -⟩
      simpa using h ()⟩
