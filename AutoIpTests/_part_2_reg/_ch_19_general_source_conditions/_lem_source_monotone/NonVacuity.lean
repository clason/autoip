module

import AutoIp._part_2_reg._ch_19_general_source_conditions._lem_source_monotone.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.sourceSetIndex_mono_index` can hold together. -/
theorem AutoIp.sourceSetIndex_mono_index_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (φ : ℝ → ℝ), ∃ (ψ : ℝ → ℝ), ∃ (c : ℝ), ∃ (ρ : ℝ), (IsSingularSystem K σ v u) ∧ (AutoIp.IsIndexFunction (‖K‖ ^ (2 : ℕ)) φ) ∧ (AutoIp.IsIndexFunction (‖K‖ ^ (2 : ℕ)) ψ) ∧ ((0 : ℝ) < c) ∧ ((0 : ℝ) < ρ) ∧ (∀ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), φ lam ≤ c * ψ lam) :=
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
  have hK : ‖(1 : ℝ →L[ℝ] ℝ)‖ ^ (2 : ℕ) = 1 := by
    rw [Witnesses.Identity.norm_one']
    norm_num
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1, fun t => t ^ 2,
    fun t => t, 1, 1, ?_⟩
  refine ⟨hone, ⟨by norm_num, (continuous_pow 2).continuousOn,
    fun a ha b hb hab => pow_lt_pow_left₀ hab ha.1 two_ne_zero⟩,
    ⟨rfl, continuousOn_id, fun _ _ _ _ h => h⟩, by norm_num, by norm_num, ?_⟩
  intro lam hlam
  rw [hK] at hlam
  nlinarith [hlam.1, hlam.2]

/-- The hypotheses of `AutoIp.sourceSetIndex_mono_index` can fail. -/
theorem AutoIp.sourceSetIndex_mono_index_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (φ : ℝ → ℝ), ∃ (ψ : ℝ → ℝ), ∃ (c : ℝ), ∃ (ρ : ℝ), ¬ ((IsSingularSystem K σ v u) ∧ (AutoIp.IsIndexFunction (‖K‖ ^ (2 : ℕ)) φ) ∧ (AutoIp.IsIndexFunction (‖K‖ ^ (2 : ℕ)) ψ) ∧ ((0 : ℝ) < c) ∧ ((0 : ℝ) < ρ) ∧ (∀ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ (2 : ℕ)), φ lam ≤ c * ψ lam)) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, fun t => t,
    fun t => t, 0, 0, ?_⟩
  rintro ⟨H, _, _, _, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)
