/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose_bounded
public import AutoIp._part_1_funcanal._ch_03_hilbert_spaces._lem_closed_range_adjoint
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_characterisation
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_equations
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_adjoint.Helpers

section _lem_mp_adjoint

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- If `Ran(T)` is closed, then `(T†)* = (T*)†`, with `T† ∈ L(Y,X)` and `(T†)*` its
Hilbert-space adjoint, stated pointwise on `X`. -/
public theorem adjoint_moorePenroseL_apply {T : E →L[𝕜] F}
    (hclosed : IsClosed (T.toLinearMap.range : Set F))
    (x : E) :
    (moorePenroseL hclosed).adjoint x =
      moorePenrose T.adjoint ⟨x, (mem_mpDomain_of_isClosed_range
          (T.isClosed_range_adjoint_of_isClosed_range hclosed) x)⟩ := by
  have hmem : ∀ y : F, y ∈ mpDomain T := mem_mpDomain_of_isClosed_range hclosed
  have hD : ∀ y : F, moorePenroseL hclosed y = moorePenrose T ⟨y, (hmem y)⟩ :=
    moorePenroseL_apply hclosed
  have hTDeq : T ∘L moorePenroseL hclosed
      = (LinearMap.range T.toLinearMap).topologicalClosure.starProjection := by
    refine ContinuousLinearMap.ext fun y => ?_
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hD]
    exact apply_moorePenrose ⟨_, (hmem y)⟩
  have hDTeq : moorePenroseL hclosed ∘L T
      = 1 - (LinearMap.ker T.toLinearMap).starProjection := by
    refine ContinuousLinearMap.ext fun z => ?_
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hD,
      sub_apply, one_apply_eq_self]
    exact moorePenrose_apply_apply z
  have hTDsa : IsSelfAdjoint (T ∘L moorePenroseL hclosed) := by
    rw [hTDeq]; exact isSelfAdjoint_starProjection _
  have hDTsa : IsSelfAdjoint (moorePenroseL hclosed ∘L T) := by
    rw [hDTeq]
    exact (IsSelfAdjoint.one (R := E →L[𝕜] E)).sub (isSelfAdjoint_starProjection _)
  have hTDT : (T ∘L moorePenroseL hclosed) ∘L T = T := by
    refine ContinuousLinearMap.ext fun z => ?_
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hD]
    exact self_comp_moorePenrose_comp_self z
  have hDTD : (moorePenroseL hclosed ∘L T) ∘L moorePenroseL hclosed
      = moorePenroseL hclosed := by
    refine ContinuousLinearMap.ext fun y => ?_
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hD]
    exact moorePenrose_comp_self_comp_moorePenrose (hmem y)
  have h1 : ContinuousLinearMap.adjoint T ∘L
      ContinuousLinearMap.adjoint (moorePenroseL hclosed) ∘L
      ContinuousLinearMap.adjoint T = ContinuousLinearMap.adjoint T := by
    rw [← ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.adjoint_comp, hTDT]
  have h2 : ContinuousLinearMap.adjoint (moorePenroseL hclosed) ∘L
      ContinuousLinearMap.adjoint T ∘L
      ContinuousLinearMap.adjoint (moorePenroseL hclosed)
      = ContinuousLinearMap.adjoint (moorePenroseL hclosed) := by
    rw [← ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.adjoint_comp, hDTD]
  have h3 : IsSelfAdjoint (ContinuousLinearMap.adjoint (moorePenroseL hclosed) ∘L
      ContinuousLinearMap.adjoint T) := by
    rw [← ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.star_eq_adjoint,
      hTDsa.star_eq]
    exact hTDsa
  have h4 : IsSelfAdjoint (ContinuousLinearMap.adjoint T ∘L
      ContinuousLinearMap.adjoint (moorePenroseL hclosed)) := by
    rw [← ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.star_eq_adjoint,
      hDTsa.star_eq]
    exact hDTsa
  exact eq_moorePenrose_of_comp_eq_of_isSelfAdjoint (T := ContinuousLinearMap.adjoint T)
    (ContinuousLinearMap.adjoint (moorePenroseL hclosed))
    (ContinuousLinearMap.isClosed_range_adjoint_of_isClosed_range T hclosed) h1 h2 h3 h4 x

/-- If `Ran(T)` is closed, then `(T†)* = (T*)†` as partially defined operators. Here the
adjoint of `T†` is the adjoint of a partially defined operator. -/
public theorem adjoint_moorePenrose {T : E →L[𝕜] F}
    (hclosed : IsClosed (T.toLinearMap.range : Set F)) :
    (moorePenrose T).adjoint = moorePenrose T.adjoint := by
  have hclosed' := ContinuousLinearMap.isClosed_range_adjoint_of_isClosed_range T hclosed
  have hCLM : ContinuousLinearMap.adjoint (moorePenroseL hclosed) = moorePenroseL hclosed' := by
    refine ContinuousLinearMap.ext fun x => ?_
    rw [adjoint_moorePenroseL_apply hclosed x, moorePenroseL_apply hclosed' x]
  rw [moorePenrose_eq_toPMap hclosed,
    ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense _ (p := ⊤) (by simp),
    hCLM, ← moorePenrose_eq_toPMap hclosed']

end AutoIp

end _lem_mp_adjoint
