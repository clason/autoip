module

import AutoIp._part_2_reg._ch_20_iterated_tikhonov._lem_iterated_tikhonov_recursion.Spec -- shake: keep
import AutoIpTests.Witnesses.Identity

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The hypotheses of `AutoIp.iteratedTikhonov_eq_spectralReg` can hold together. -/
theorem AutoIp.iteratedTikhonov_eq_spectralReg_satisfiable : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ∃ (y : F), ∃ (z : ℕ → E), ∃ (m : ℕ), (IsSingularSystem K σ v u) ∧ (z (0 : ℕ) = (0 : E)) ∧ (∀ k < m,
  ((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K ∘SL K + (↑(↑α : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E :
        E → E)
      (z (k + (1 : ℕ)) - z k) =
    ((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K : F → E) (y - (K : E → F) (z k))) :=
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
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 1, Unit, fun _ => 1, fun _ => 1, fun _ => 1,
    ⟨1, Set.mem_Ioi.2 one_pos⟩, 2, fun k => (k : ℝ), 1, hone, by simp, ?_⟩
  intro k hk
  obtain rfl : k = 0 := Nat.lt_one_iff.1 hk
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, Witnesses.Identity.adjoint_one_apply]
  norm_num

/-- The hypotheses of `AutoIp.iteratedTikhonov_eq_spectralReg` can fail. -/
theorem AutoIp.iteratedTikhonov_eq_spectralReg_nontrivial : ∃ (𝕜 : Type), ∃ (x1 : RCLike 𝕜), ∃ (E : Type), ∃ (F : Type), ∃ (x4 : NormedAddCommGroup E), ∃ (x5 : InnerProductSpace 𝕜 E), ∃ (x6 : CompleteSpace E), ∃ (x7 : NormedAddCommGroup F), ∃ (x8 : InnerProductSpace 𝕜 F), ∃ (x9 : CompleteSpace F), ∃ (K : E →L[𝕜] F), ∃ (ι : Type), ∃ (σ : ι → ℝ), ∃ (v : ι → E), ∃ (u : ι → F), ∃ (α : (↑(Set.Ioi (0 : ℝ)) : Type)), ∃ (y : F), ∃ (z : ℕ → E), ∃ (m : ℕ), ¬ ((IsSingularSystem K σ v u) ∧ (z (0 : ℕ) = (0 : E)) ∧ (∀ k < m,
  ((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K ∘SL K + (↑(↑α : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E :
        E → E)
      (z (k + (1 : ℕ)) - z k) =
    ((ContinuousLinearMap.adjoint : (E →L[𝕜] F) → F →L[𝕜] E) K : F → E) (y - (K : E → F) (z k)))) :=
  by
  refine ⟨ℝ, inferInstance, ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 0, Unit, fun _ => 0, fun _ => 0, fun _ => 0, ⟨1, Set.mem_Ioi.2 one_pos⟩, 0, fun _ => 0, 0
    , ?_⟩
  rintro ⟨H, _, _⟩
  exact absurd (H.pos ()) (lt_irrefl 0)
