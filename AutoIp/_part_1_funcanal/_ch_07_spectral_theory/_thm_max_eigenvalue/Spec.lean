/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

section _thm_max_eigenvalue

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [CompleteSpace H]

/-- A nonzero compact self-adjoint operator K on a Hilbert space has an eigenvalue λ₁ with
|λ₁| = ‖K‖: there is u ≠ 0 with Ku = λ₁u. The statement holds over the real and the
complex scalars alike. -/
public theorem IsSelfAdjoint.exists_eigenvalue_norm_eq_norm {K : H →L[𝕜] H}
    (hsa : IsSelfAdjoint K) (hc : IsCompactOperator K) (hne : K ≠ 0) :
    ∃ (lam : 𝕜) (u : H), u ≠ 0 ∧ K u = lam • u ∧ ‖lam‖ = ‖K‖ := by
  have : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  have hK0 : 0 < ‖K‖ := norm_pos_iff.mpr hne
  have hrad : spectralRadius 𝕜 K = ‖K‖₊ := ContinuousLinearMap.spectralRadius_eq_nnnorm K hsa
  have hnonempty : (spectrum 𝕜 K).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro h
    rw [spectralRadius, h] at hrad
    simp only [iSup_emptyset] at hrad
    exact hK0.ne' (by exact_mod_cast congrArg ENNReal.toReal hrad.symm)
  obtain ⟨lam, hlam, hnorm⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty hnonempty
  have hlamnorm : ‖lam‖ = ‖K‖ := by
    have h1 : ‖lam‖₊ = ‖K‖₊ := by exact_mod_cast hnorm.trans hrad
    exact congrArg NNReal.toReal h1
  have hlam0 : lam ≠ 0 := by
    intro h; rw [h] at hlamnorm; simp at hlamnorm; exact hK0.ne' hlamnorm.symm
  have hev : Module.End.HasEigenvalue (K : Module.End 𝕜 H) lam :=
    (hc.hasEigenvalue_iff_mem_spectrum hlam0).mpr hlam
  obtain ⟨u, hmem, hu0⟩ := hev.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hmem
  exact ⟨lam, u, hu0, hmem, hlamnorm⟩

end _thm_max_eigenvalue
