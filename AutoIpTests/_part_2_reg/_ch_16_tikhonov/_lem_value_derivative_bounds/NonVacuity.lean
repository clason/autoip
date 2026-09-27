module

import AutoIp._part_2_reg._ch_16_tikhonov._lem_value_derivative_bounds.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity
import AutoIpTests.Witnesses.Zero
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.tikhonovValue_deriv_bounds` can hold together. -/
theorem AutoIp.tikhonovValue_deriv_bounds_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (z : F), ∃ (j : ℝ → ℝ), ∃ (f : ℝ → ℝ), ∃ (g : ℝ → ℝ), ∃ (α : ℝ), ∃ (dr : ℝ), ∃ (dl : ℝ), (∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), j b = AutoIp.tikhonovValue hs z ⟨b, hb⟩) ∧ (∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), f b = AutoIp.tikhonovResidualValue hs z ⟨b, hb⟩) ∧ (∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), g b = AutoIp.tikhonovNormValue hs z ⟨b, hb⟩) ∧ (α ∈ Set.Ioi (0 : ℝ)) ∧ (HasDerivWithinAt j dr (Set.Ioi α) α) ∧ (HasDerivWithinAt j dl (Set.Iio α) α) :=
  by
  classical
  have hss : IsSingularSystem (ι := Unit) (1 : ℝ →L[ℝ] ℝ)
      (fun _ => 1) (fun _ => 1) (fun _ => 1) :=
    { pos := fun _ => one_pos
      orthonormal_left := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      orthonormal_right := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      span_left := Witnesses.Identity.span_left _ fun _ => rfl
      span_right := Witnesses.Identity.span_right _ fun _ => rfl
      map_left := fun _ => (one_mul (1 : ℝ)).symm
      map_right := fun _ =>
        (Witnesses.Identity.adjoint_one_apply 1).trans (one_mul (1 : ℝ)).symm }
  have hR : ∀ (α : (↑(Set.Ioi (0 : ℝ)) : Type)),
      AutoIp.spectralReg hss AutoIp.tikhonovFilter
        (AutoIp.tikhonovFilter_exists_bound_on_spectrum hss) α 1 = (1 + (α : ℝ))⁻¹ := by
    intro α
    have h := AutoIp.hasSum_spectralReg hss AutoIp.tikhonovFilter
      (AutoIp.tikhonovFilter_exists_bound_on_spectrum hss) α 1
    rw [h.unique (hasSum_fintype _)]
    simp [AutoIp.tikhonovFilter, add_comm]
  have hf : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)),
      AutoIp.tikhonovResidualValue hss 1 ⟨b, hb⟩ = 1 / 2 * ((1 + b)⁻¹ - 1) ^ 2 := by
    intro b hb
    rw [AutoIp.tikhonovResidualValue_def, hR]
    simp
  have hg : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)),
      AutoIp.tikhonovNormValue hss 1 ⟨b, hb⟩ = 1 / 2 * ((1 + b)⁻¹) ^ 2 := by
    intro b hb
    rw [AutoIp.tikhonovNormValue_def, hR]
    simp
  have hj : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)),
      AutoIp.tikhonovValue hss 1 ⟨b, hb⟩ = 1 / 2 - 1 / 2 * (1 + b)⁻¹ := by
    intro b hb
    have hb' : (1 + b) ≠ 0 := by have := Set.mem_Ioi.1 hb; positivity
    rw [AutoIp.tikhonovValue_def, hf, hg]
    field_simp
    ring
  have hd : HasDerivAt (fun b : ℝ => 1 / 2 - 1 / 2 * (1 + b)⁻¹)
      (1 / 2 * (((1 : ℝ) + 1) ^ 2)⁻¹) 1 :=
    by
      have h1 : HasDerivAt (fun b : ℝ => 1 + b) 1 1 := (hasDerivAt_id (1 : ℝ)).const_add 1
      have h2 : HasDerivAt (fun b : ℝ => 1 / 2 - 1 / 2 * (1 + b)⁻¹)
          (-(1 / 2 * (-1 / (1 + 1) ^ 2))) 1 :=
        HasDerivAt.const_sub (1 / 2 : ℝ)
          (HasDerivAt.const_mul (1 / 2 : ℝ) (HasDerivAt.inv h1 (by norm_num)))
      have he : (1 / 2 : ℝ) * (((1 : ℝ) + 1) ^ 2)⁻¹ = -(1 / 2 * (-1 / (1 + 1) ^ 2)) := by ring
      rw [he]
      exact h2
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1, hss, 1,
    fun b => 1 / 2 - 1 / 2 * (1 + b)⁻¹, fun b => 1 / 2 * ((1 + b)⁻¹ - 1) ^ 2,
    fun b => 1 / 2 * ((1 + b)⁻¹) ^ 2, 1, 1 / 2 * (((1 : ℝ) + 1) ^ 2)⁻¹,
    1 / 2 * (((1 : ℝ) + 1) ^ 2)⁻¹, fun b hb => (hj b hb).symm, fun b hb => (hf b hb).symm,
    fun b hb => (hg b hb).symm, Set.mem_Ioi.2 one_pos, hd.hasDerivWithinAt, hd.hasDerivWithinAt⟩

/-- The hypotheses of `AutoIp.tikhonovValue_deriv_bounds` can fail. -/
theorem AutoIp.tikhonovValue_deriv_bounds_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (z : F), ∃ (j : ℝ → ℝ), ∃ (f : ℝ → ℝ), ∃ (g : ℝ → ℝ), ∃ (α : ℝ), ∃ (dr : ℝ), ∃ (dl : ℝ), ¬ ((∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), j b = AutoIp.tikhonovValue hs z ⟨b, hb⟩) ∧ (∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), f b = AutoIp.tikhonovResidualValue hs z ⟨b, hb⟩) ∧ (∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), g b = AutoIp.tikhonovNormValue hs z ⟨b, hb⟩) ∧ (α ∈ Set.Ioi (0 : ℝ)) ∧ (HasDerivWithinAt j dr (Set.Ioi α) α) ∧ (HasDerivWithinAt j dl (Set.Iio α) α)) :=
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
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Empty, fun _ => 0, fun _ => 0, fun _ => 0, hss, 0,
    fun _ => 1, fun _ => 1, fun _ => 1, 1, 0, 0, ?_⟩
  rintro ⟨hone, -⟩
  have h1 := hone 1 (Set.mem_Ioi.2 one_pos)
  simp [AutoIp.tikhonovValue_def, AutoIp.tikhonovResidualValue_def, AutoIp.tikhonovNormValue_def] at h1

/-- The hypotheses of `AutoIp.tikhonovResidualValue_bounds_of_deriv` can hold together. -/
theorem AutoIp.tikhonovResidualValue_bounds_of_deriv_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (z : F), ∃ (j : ℝ → ℝ), ∃ (f : ℝ → ℝ), ∃ (g : ℝ → ℝ), ∃ (α : ℝ), ∃ (dr : ℝ), ∃ (dl : ℝ), (∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), j b = AutoIp.tikhonovValue hs z ⟨b, hb⟩) ∧ (∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), f b = AutoIp.tikhonovResidualValue hs z ⟨b, hb⟩) ∧ (∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), g b = AutoIp.tikhonovNormValue hs z ⟨b, hb⟩) ∧ (α ∈ Set.Ioi (0 : ℝ)) ∧ (HasDerivWithinAt j dr (Set.Ioi α) α) ∧ (HasDerivWithinAt j dl (Set.Iio α) α) :=
  by
  classical
  have hss : IsSingularSystem (ι := Unit) (1 : ℝ →L[ℝ] ℝ)
      (fun _ => 1) (fun _ => 1) (fun _ => 1) :=
    { pos := fun _ => one_pos
      orthonormal_left := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      orthonormal_right := ⟨fun _ => norm_one, fun {i j} h => absurd (Subsingleton.elim i j) h⟩
      span_left := Witnesses.Identity.span_left _ fun _ => rfl
      span_right := Witnesses.Identity.span_right _ fun _ => rfl
      map_left := fun _ => (one_mul (1 : ℝ)).symm
      map_right := fun _ =>
        (Witnesses.Identity.adjoint_one_apply 1).trans (one_mul (1 : ℝ)).symm }
  have hR : ∀ (α : (↑(Set.Ioi (0 : ℝ)) : Type)),
      AutoIp.spectralReg hss AutoIp.tikhonovFilter
        (AutoIp.tikhonovFilter_exists_bound_on_spectrum hss) α 1 = (1 + (α : ℝ))⁻¹ := by
    intro α
    have h := AutoIp.hasSum_spectralReg hss AutoIp.tikhonovFilter
      (AutoIp.tikhonovFilter_exists_bound_on_spectrum hss) α 1
    rw [h.unique (hasSum_fintype _)]
    simp [AutoIp.tikhonovFilter, add_comm]
  have hf : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)),
      AutoIp.tikhonovResidualValue hss 1 ⟨b, hb⟩ = 1 / 2 * ((1 + b)⁻¹ - 1) ^ 2 := by
    intro b hb
    rw [AutoIp.tikhonovResidualValue_def, hR]
    simp
  have hg : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)),
      AutoIp.tikhonovNormValue hss 1 ⟨b, hb⟩ = 1 / 2 * ((1 + b)⁻¹) ^ 2 := by
    intro b hb
    rw [AutoIp.tikhonovNormValue_def, hR]
    simp
  have hj : ∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)),
      AutoIp.tikhonovValue hss 1 ⟨b, hb⟩ = 1 / 2 - 1 / 2 * (1 + b)⁻¹ := by
    intro b hb
    have hb' : (1 + b) ≠ 0 := by have := Set.mem_Ioi.1 hb; positivity
    rw [AutoIp.tikhonovValue_def, hf, hg]
    field_simp
    ring
  have hd : HasDerivAt (fun b : ℝ => 1 / 2 - 1 / 2 * (1 + b)⁻¹)
      (1 / 2 * (((1 : ℝ) + 1) ^ 2)⁻¹) 1 :=
    by
      have h1 : HasDerivAt (fun b : ℝ => 1 + b) 1 1 := (hasDerivAt_id (1 : ℝ)).const_add 1
      have h2 : HasDerivAt (fun b : ℝ => 1 / 2 - 1 / 2 * (1 + b)⁻¹)
          (-(1 / 2 * (-1 / (1 + 1) ^ 2))) 1 :=
        HasDerivAt.const_sub (1 / 2 : ℝ)
          (HasDerivAt.const_mul (1 / 2 : ℝ) (HasDerivAt.inv h1 (by norm_num)))
      have he : (1 / 2 : ℝ) * (((1 : ℝ) + 1) ^ 2)⁻¹ = -(1 / 2 * (-1 / (1 + 1) ^ 2)) := by ring
      rw [he]
      exact h2
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1, hss, 1,
    fun b => 1 / 2 - 1 / 2 * (1 + b)⁻¹, fun b => 1 / 2 * ((1 + b)⁻¹ - 1) ^ 2,
    fun b => 1 / 2 * ((1 + b)⁻¹) ^ 2, 1, 1 / 2 * (((1 : ℝ) + 1) ^ 2)⁻¹,
    1 / 2 * (((1 : ℝ) + 1) ^ 2)⁻¹, fun b hb => (hj b hb).symm, fun b hb => (hf b hb).symm,
    fun b hb => (hg b hb).symm, Set.mem_Ioi.2 one_pos, hd.hasDerivWithinAt, hd.hasDerivWithinAt⟩

/-- The hypotheses of `AutoIp.tikhonovResidualValue_bounds_of_deriv` can fail. -/
theorem AutoIp.tikhonovResidualValue_bounds_of_deriv_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (z : F), ∃ (j : ℝ → ℝ), ∃ (f : ℝ → ℝ), ∃ (g : ℝ → ℝ), ∃ (α : ℝ), ∃ (dr : ℝ), ∃ (dl : ℝ), ¬ ((∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), j b = AutoIp.tikhonovValue hs z ⟨b, hb⟩) ∧ (∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), f b = AutoIp.tikhonovResidualValue hs z ⟨b, hb⟩) ∧ (∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), g b = AutoIp.tikhonovNormValue hs z ⟨b, hb⟩) ∧ (α ∈ Set.Ioi (0 : ℝ)) ∧ (HasDerivWithinAt j dr (Set.Ioi α) α) ∧ (HasDerivWithinAt j dl (Set.Iio α) α)) :=
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
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Empty, fun _ => 0, fun _ => 0, fun _ => 0, hss, 0,
    fun _ => 1, fun _ => 1, fun _ => 1, 1, 0, 0, ?_⟩
  rintro ⟨hone, -⟩
  have h1 := hone 1 (Set.mem_Ioi.2 one_pos)
  simp [AutoIp.tikhonovValue_def, AutoIp.tikhonovResidualValue_def, AutoIp.tikhonovNormValue_def] at h1
