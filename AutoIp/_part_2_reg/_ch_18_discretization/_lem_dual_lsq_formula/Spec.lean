/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_18_discretization._def_dual_lsq_projection
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_equations
import AutoIp._part_2_reg._ch_11_moore_penrose._thm_mp_minnorm

section _lem_dual_lsq_formula

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The dual method is a projection: for `y ∈ Dom(T†)`, the dual least-squares projection
satisfies `xₙ = Pₙ x†`, where `Pₙ` is the orthogonal projection onto `Xₙ = T* Yₙ`.

The statement is for a single `n`, and of the subspaces it assumes only
`Yₙ ⊆ Ker(T*)ᗮ`. -/
public theorem dualLsqProjection_eq_starProjection (T : E →L[𝕜] F) (Y : ℕ → Submodule 𝕜 F)
    [∀ n, (Y n).HasOrthogonalProjection] (X : ℕ → Submodule 𝕜 E)
    [∀ n, (X n).HasOrthogonalProjection] (n : ℕ)
    (hX : X n = (Y n).map T.adjoint.toLinearMap)
    (hsub : Y n ≤ (T.adjoint.toLinearMap.ker)ᗮ)
    {y : F} (hy : y ∈ mpDomain T)
    (hyd : ∀ m, (Y m).starProjection y ∈ mpDomain ((Y m).starProjection ∘L T)) :
    dualLsqProjection T Y y hyd n = (X n).starProjection (moorePenrose T ⟨y, hy⟩) := by
  classical
  have hQzero : ∀ z : F, (Y n).starProjection z = 0 ↔ z ∈ (Y n)ᗮ :=
    fun z => Submodule.starProjection_apply_eq_zero_iff _
  have hker : LinearMap.ker ((Y n).starProjection ∘L T).toLinearMap = (X n)ᗮ := by
    ext x
    have hiff : ((Y n).starProjection ∘L T) x = 0 ↔ T x ∈ (Y n)ᗮ := by
      rw [ContinuousLinearMap.comp_apply, hQzero]
    constructor
    · intro hx
      have hTx : T x ∈ (Y n)ᗮ := hiff.1 hx
      rw [hX, Submodule.mem_orthogonal]
      rintro z ⟨w, hw, rfl⟩
      have hz := (Submodule.mem_orthogonal _ _).1 hTx w hw
      rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.adjoint_inner_left]
      exact hz
    · intro hx
      rw [hX, Submodule.mem_orthogonal] at hx
      refine hiff.2 ?_
      rw [Submodule.mem_orthogonal]
      intro w hw
      have := hx (ContinuousLinearMap.adjoint T w) ⟨w, hw, rfl⟩
      rwa [ContinuousLinearMap.adjoint_inner_left] at this
  -- `Qₙ y = Qₙ P_R y = Qₙ T x† = Tₙ x†`, because `Yₙ ⊆ Ker(T*)ᗮ = closure (Ran T)`.
  have hdatum : (Y n).starProjection y = ((Y n).starProjection ∘L T) (moorePenrose T ⟨y, hy⟩) := by
    have hPR : T (moorePenrose T ⟨y, hy⟩) =
        (LinearMap.range T.toLinearMap).topologicalClosure.starProjection y :=
      apply_moorePenrose ⟨_, hy⟩
    have hkerT : y - (LinearMap.range T.toLinearMap).topologicalClosure.starProjection y
        ∈ LinearMap.ker (ContinuousLinearMap.adjoint T).toLinearMap := by
      have h1 := (LinearMap.range T.toLinearMap).topologicalClosure
        |>.sub_starProjection_mem_orthogonal y
      rwa [Submodule.orthogonal_closure, T.orthogonal_range] at h1
    have hperp : y - (LinearMap.range T.toLinearMap).topologicalClosure.starProjection y
        ∈ (Y n)ᗮ :=
      Submodule.orthogonal_le hsub
        (Submodule.le_orthogonal_orthogonal _ hkerT)
    have hzero : (Y n).starProjection
        (y - (LinearMap.range T.toLinearMap).topologicalClosure.starProjection y) = 0 :=
      (hQzero _).2 hperp
    rw [map_sub, sub_eq_zero] at hzero
    rw [ContinuousLinearMap.comp_apply, hPR, hzero]
  -- `Tₙ Pₙ = Tₙ` because `Id - Pₙ` lands in `Xₙᗮ = Ker Tₙ`.
  have hTnP : ((Y n).starProjection ∘L T) ((X n).starProjection (moorePenrose T ⟨y, hy⟩))
      = ((Y n).starProjection ∘L T) (moorePenrose T ⟨y, hy⟩) := by
    have hmem : moorePenrose T ⟨y, hy⟩ - (X n).starProjection (moorePenrose T ⟨y, hy⟩) ∈ (X n)ᗮ :=
      (X n).sub_starProjection_mem_orthogonal _
    rw [← hker] at hmem
    have h0 : ((Y n).starProjection ∘L T)
        (moorePenrose T ⟨y, hy⟩ - (X n).starProjection (moorePenrose T ⟨y, hy⟩)) = 0 := hmem
    rw [map_sub, sub_eq_zero] at h0
    exact h0.symm
  have hmn : IsMinimumNorm ((Y n).starProjection ∘L T) ((Y n).starProjection y)
      ((X n).starProjection (moorePenrose T ⟨y, hy⟩)) := by
    refine isMinimumNorm_iff.2 ⟨?_, ?_⟩
    · rw [hTnP, ← hdatum, sub_self]
      exact Submodule.zero_mem _
    · rw [hker]
      exact Submodule.le_orthogonal_orthogonal _ ((X n).starProjection_apply_mem _)
  have hmemdom : (Y n).starProjection y ∈ mpDomain ((Y n).starProjection ∘L T) := by
    have h1 := (isMinimumNorm_iff.1 hmn).1
    have he : (Y n).starProjection y
        = ((Y n).starProjection ∘L T) ((X n).starProjection (moorePenrose T ⟨y, hy⟩))
          + ((Y n).starProjection y
            - ((Y n).starProjection ∘L T) ((X n).starProjection (moorePenrose T ⟨y, hy⟩))) := by
      abel
    rw [mpDomain, he]
    exact Submodule.add_mem_sup ⟨_, rfl⟩ h1
  rw [dualLsqProjection_def]
  exact (moorePenrose_isMinimumNorm ⟨_, hmemdom⟩).unique hmn

end AutoIp

end _lem_dual_lsq_formula
