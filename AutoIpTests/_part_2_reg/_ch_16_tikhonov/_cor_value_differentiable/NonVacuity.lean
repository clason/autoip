module

import AutoIp._part_2_reg._ch_16_tikhonov._cor_value_differentiable.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity
import AutoIpTests.Witnesses.Zero

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.tikhonovValue_ae_hasDerivAt` can hold together. -/
theorem AutoIp.tikhonovValue_ae_hasDerivAt_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (z : F), ∃ (j : ℝ → ℝ), ∃ (f : ℝ → ℝ), ∃ (g : ℝ → ℝ), (∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), j b = AutoIp.tikhonovValue hs z ⟨b, hb⟩) ∧ (∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), f b = AutoIp.tikhonovResidualValue hs z ⟨b, hb⟩) ∧ (∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), g b = AutoIp.tikhonovNormValue hs z ⟨b, hb⟩) :=
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
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1, hss, 1,
    (fun b => if hb : b ∈ Set.Ioi (0 : ℝ) then AutoIp.tikhonovValue hss 1 ⟨b, hb⟩ else 0),
    (fun b => if hb : b ∈ Set.Ioi (0 : ℝ) then AutoIp.tikhonovResidualValue hss 1 ⟨b, hb⟩ else 0),
    (fun b => if hb : b ∈ Set.Ioi (0 : ℝ) then AutoIp.tikhonovNormValue hss 1 ⟨b, hb⟩ else 0),
    fun _ hb => dif_pos hb, fun _ hb => dif_pos hb, fun _ hb => dif_pos hb⟩

/-- The hypotheses of `AutoIp.tikhonovValue_ae_hasDerivAt` can fail. -/
theorem AutoIp.tikhonovValue_ae_hasDerivAt_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (hs : IsSingularSystem K σ v u), ∃ (z : F), ∃ (j : ℝ → ℝ), ∃ (f : ℝ → ℝ), ∃ (g : ℝ → ℝ), ¬ ((∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), j b = AutoIp.tikhonovValue hs z ⟨b, hb⟩) ∧ (∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), f b = AutoIp.tikhonovResidualValue hs z ⟨b, hb⟩) ∧ (∀ (b : ℝ) (hb : b ∈ Set.Ioi (0 : ℝ)), g b = AutoIp.tikhonovNormValue hs z ⟨b, hb⟩)) :=
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
    fun _ => 1,
    fun _ => 1,
    fun _ => 1, ?_⟩
  rintro ⟨hone, -, -⟩
  have h1 := hone 1 (Set.mem_Ioi.2 one_pos)
  simp [AutoIp.tikhonovValue_def, AutoIp.tikhonovResidualValue_def, AutoIp.tikhonovNormValue_def] at h1
