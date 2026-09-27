/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_18_discretization._def_dual_lsq_projection
import AutoIp._part_2_reg._ch_18_discretization._lem_dual_lsq_formula

section _thm_dual_lsq_rate

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Rate for the dual least-squares projection: for `y ∈ Dom(T†)` with `x† = T* w`,
`‖xₙ - x†‖ ≤ ‖w‖ ‖(Id - Pₙ) T*‖`, where `Pₙ` is the orthogonal projection onto `Xₙ = T* Yₙ`.

The statement is for a single `n`, and of the subspaces it assumes only
`Yₙ ⊆ Ker(T*)ᗮ`. -/
public theorem norm_dualLsqProjection_sub_le (T : E →L[𝕜] F) (Y : ℕ → Submodule 𝕜 F)
    [∀ n, (Y n).HasOrthogonalProjection] (X : ℕ → Submodule 𝕜 E)
    [∀ n, (X n).HasOrthogonalProjection] (n : ℕ)
    (hX : X n = (Y n).map T.adjoint.toLinearMap)
    (hsub : Y n ≤ (T.adjoint.toLinearMap.ker)ᗮ)
    {y : F} (hy : y ∈ mpDomain T)
    (hyd : ∀ m, (Y m).starProjection y ∈ mpDomain ((Y m).starProjection ∘L T)) {w : F}
    (hw : moorePenrose T ⟨y, hy⟩ = T.adjoint w) :
    ‖dualLsqProjection T Y y hyd n - moorePenrose T ⟨y, hy⟩‖ ≤
      ‖w‖ * ‖(ContinuousLinearMap.id 𝕜 E - (X n).starProjection) ∘L
        T.adjoint‖ := by
  rw [dualLsqProjection_eq_starProjection T Y X n hX hsub hy hyd]
  set A : F →L[𝕜] E := (ContinuousLinearMap.id 𝕜 E - (X n).starProjection) ∘L
    ContinuousLinearMap.adjoint T with hA
  have h1 : (X n).starProjection (moorePenrose T ⟨y, hy⟩) - moorePenrose T ⟨y, hy⟩ = -(A w) := by
    rw [hA]
    simp only [ContinuousLinearMap.comp_apply, sub_apply,
      ContinuousLinearMap.id_apply, ← hw]
    abel
  rw [h1, norm_neg]
  calc ‖A w‖ ≤ ‖A‖ * ‖w‖ := A.le_opNorm w
    _ = ‖w‖ * ‖A‖ := mul_comm _ _

end AutoIp

end _thm_dual_lsq_rate
