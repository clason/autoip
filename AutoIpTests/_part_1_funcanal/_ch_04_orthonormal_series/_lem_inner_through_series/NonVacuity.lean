module

import AutoIp._part_1_funcanal._ch_04_orthonormal_series._lem_inner_through_series.Spec -- shake: keep

/-- The hypotheses of `HasSum.inner_right` can hold together. -/
theorem HasSum.inner_right_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (x3 : NormedAddCommGroup E), ∃ (x4 : InnerProductSpace 𝕜 E), ∃ (ι : Type), ∃ (f : ι → E), ∃ (x : E), ∃ (z : E), HasSum f x :=
  by
  classical
  refine ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, Empty, fun _ => 0, 0, 0, ?_⟩
  exact by simp

/-- The hypotheses of `HasSum.inner_right` can fail. -/
theorem HasSum.inner_right_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (x3 : NormedAddCommGroup E), ∃ (x4 : InnerProductSpace 𝕜 E), ∃ (ι : Type), ∃ (f : ι → E), ∃ (x : E), ∃ (z : E), ¬ (HasSum f x) :=
  ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, ℕ, fun _ => 1, 0, 0, by
      intro h
      exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h.summable.tendsto_atTop_zero)⟩

/-- The hypotheses of `HasSum.inner_left` can hold together. -/
theorem HasSum.inner_left_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (x3 : NormedAddCommGroup E), ∃ (x4 : InnerProductSpace 𝕜 E), ∃ (ι : Type), ∃ (f : ι → E), ∃ (x : E), ∃ (z : E), HasSum f x :=
  by
  classical
  refine ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, Empty, fun _ => 0, 0, 0, ?_⟩
  exact by simp

/-- The hypotheses of `HasSum.inner_left` can fail. -/
theorem HasSum.inner_left_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (x3 : NormedAddCommGroup E), ∃ (x4 : InnerProductSpace 𝕜 E), ∃ (ι : Type), ∃ (f : ι → E), ∃ (x : E), ∃ (z : E), ¬ (HasSum f x) :=
  ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, ℕ, fun _ => 1, 0, 0, by
      intro h
      exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h.summable.tendsto_atTop_zero)⟩

/-- The hypotheses of `Orthonormal.eq_of_hasSum_smul` can hold together. -/
theorem Orthonormal.eq_of_hasSum_smul_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (x3 : NormedAddCommGroup E), ∃ (x4 : InnerProductSpace 𝕜 E), ∃ (ι : Type), ∃ (e : ι → E), ∃ (c : ι → 𝕜), ∃ (d : ι → 𝕜), ∃ (x : E), (Orthonormal 𝕜 e) ∧ (HasSum (fun (i : ι) => c i • e i) x) ∧ (HasSum (fun (i : ι) => d i • e i) x) :=
  by
  classical
  refine ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, Empty, fun _ => 0, fun _ => 0, fun _ => 0,
    0, ?_⟩
  exact ⟨⟨fun i => i.elim, fun {i _} _ => i.elim⟩, hasSum_empty, hasSum_empty⟩

/-- The hypotheses of `Orthonormal.eq_of_hasSum_smul` can fail. -/
theorem Orthonormal.eq_of_hasSum_smul_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (x3 : NormedAddCommGroup E), ∃ (x4 : InnerProductSpace 𝕜 E), ∃ (ι : Type), ∃ (e : ι → E), ∃ (c : ι → 𝕜), ∃ (d : ι → 𝕜), ∃ (x : E), ¬ ((Orthonormal 𝕜 e) ∧ (HasSum (fun (i : ι) => c i • e i) x) ∧ (HasSum (fun (i : ι) => d i • e i) x)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, Unit, fun _ => 0, fun _ => 0, fun _ => 0,
    0, ?_⟩
  rintro ⟨h, -, -⟩
  have := h.1 ()
  simp at this
