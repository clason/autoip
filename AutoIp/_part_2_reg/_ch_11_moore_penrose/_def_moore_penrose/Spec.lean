/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._lem_minnorm_unique
public import Mathlib.Analysis.InnerProductSpace.LinearPMap -- shake: keep
import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose.Helpers

section _def_moore_penrose

namespace AutoIp

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The Moore–Penrose domain `Dom(T†) := Ran(T) ⊕ Ran(T)ᗮ ⊆ Y`. The sum is written as the
supremum `⊔` of the two subspaces; that it is direct is not recorded here. -/
@[expose]
public def mpDomain (T : E →L[𝕜] F) : Submodule 𝕜 F :=
  LinearMap.range T.toLinearMap ⊔ (LinearMap.range T.toLinearMap)ᗮ

/-- The Moore–Penrose inverse as a linear map on `Dom(T†)`, sending `y` to the minimum norm
solution of `T x = y`. -/
public noncomputable def moorePenroseLinear [CompleteSpace E] (T : E →L[𝕜] F) :
    mpDomain T →ₗ[𝕜] E where
    toFun := fun y => (exists_isMinimumNorm_of_mem_sup y.2).choose
    map_add' := fun y z => by
      set a := (exists_isMinimumNorm_of_mem_sup y.2).choose with ha
      set b := (exists_isMinimumNorm_of_mem_sup z.2).choose with hb
      have hy : IsMinimumNorm T (y : F) a := (exists_isMinimumNorm_of_mem_sup y.2).choose_spec
      have hz : IsMinimumNorm T (z : F) b := (exists_isMinimumNorm_of_mem_sup z.2).choose_spec
      obtain ⟨h1, h2⟩ := isMinimumNorm_iff.1 hy
      obtain ⟨h1', h2'⟩ := isMinimumNorm_iff.1 hz
      refine ((exists_isMinimumNorm_of_mem_sup (y + z).2).choose_spec).unique
        (isMinimumNorm_iff.2 ⟨?_, Submodule.add_mem _ h2 h2'⟩)
      have he : ((y + z : mpDomain T) : F) - T (a + b)
          = ((y : F) - T a) + ((z : F) - T b) := by
        rw [Submodule.coe_add, map_add]; abel
      rw [he]
      exact Submodule.add_mem _ h1 h1'
    map_smul' := fun c y => by
      set a := (exists_isMinimumNorm_of_mem_sup y.2).choose with ha
      have hy : IsMinimumNorm T (y : F) a := (exists_isMinimumNorm_of_mem_sup y.2).choose_spec
      obtain ⟨h1, h2⟩ := isMinimumNorm_iff.1 hy
      refine ((exists_isMinimumNorm_of_mem_sup (c • y).2).choose_spec).unique
        (isMinimumNorm_iff.2 ⟨?_, Submodule.smul_mem _ c h2⟩)
      simp only [RingHom.id_apply]
      have he : ((c • y : mpDomain T) : F) - T (c • a) = c • ((y : F) - T a) := by
        rw [Submodule.coe_smul, map_smul, smul_sub]
      rw [he]
      exact Submodule.smul_mem _ c h1

/-- The Moore–Penrose inverse `T†`: the linear map with domain `Dom(T†)` sending `y` to the
minimum norm solution of `T x = y`, taking no value outside that domain. It is a partially
defined linear map `F →ₗ.[𝕜] E`. -/
@[expose]
public noncomputable def moorePenrose [CompleteSpace E] (T : E →L[𝕜] F) : F →ₗ.[𝕜] E :=
  ⟨mpDomain T, moorePenroseLinear T⟩

end AutoIp

end _def_moore_penrose
