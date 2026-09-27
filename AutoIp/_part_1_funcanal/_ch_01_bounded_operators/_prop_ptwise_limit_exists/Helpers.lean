/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.RCLike.Basic
import AutoIp._part_1_funcanal._ch_01_bounded_operators._prop_dense_ptwise_filter
import Mathlib.Analysis.Normed.Operator.Extend

section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Existence of the limit operator along a nontrivial filter, under an eventual norm bound. -/
public
theorem exists_tendsto_of_dense_span_filter_of_eventually_norm_le [CompleteSpace F] {ι : Type*}
    (ℱ : Filter ι) [ℱ.NeBot] (T : ι → E →L[𝕜] F) (C : ℝ) (hC : ∀ᶠ i in ℱ, ‖T i‖ ≤ C)
    (M : Set E) (hM : Dense (Submodule.span 𝕜 M : Set E))
    (hTM : ∀ x ∈ M, ∃ y : F, Filter.Tendsto (fun i => T i x) ℱ (nhds y)) :
    ∃ S : E →L[𝕜] F, ‖S‖ ≤ C ∧
      ∀ x : E, Filter.Tendsto (fun i => T i x) ℱ (nhds (S x)) := by
  obtain ⟨i₀, hi₀⟩ := hC.exists
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (T i₀)) hi₀
  let V : Submodule 𝕜 E :=
    { carrier := {x | ∃ y, Filter.Tendsto (fun i => T i x) ℱ (nhds y)}
      add_mem' := by
        rintro a b ⟨ya, ha⟩ ⟨yb, hb⟩
        exact ⟨ya + yb, by simpa only [map_add] using ha.add hb⟩
      zero_mem' := ⟨0, by simpa only [map_zero] using tendsto_const_nhds⟩
      smul_mem' := by
        rintro c a ⟨ya, ha⟩
        exact ⟨c • ya, by simpa only [map_smul] using ha.const_smul c⟩ }
  have hMV : Submodule.span 𝕜 M ≤ V := Submodule.span_le.mpr hTM
  set W := Submodule.span 𝕜 M with hW
  have hex : ∀ u : W, ∃ y, Filter.Tendsto (fun i => T i (u : E)) ℱ (nhds y) :=
    fun u => hMV u.2
  choose g hg using hex
  let S₀ : W →ₗ[𝕜] F :=
    { toFun := g
      map_add' := fun a b =>
        tendsto_nhds_unique (hg (a + b))
          (by simpa only [Submodule.coe_add, map_add] using (hg a).add (hg b))
      map_smul' := fun c a =>
        tendsto_nhds_unique (hg (c • a))
          (by
            simpa only [Submodule.coe_smul, map_smul, RingHom.id_apply] using
              (hg a).const_smul c) }
  have hbound : ∀ u : W, ‖S₀ u‖ ≤ C * ‖u‖ := fun u =>
    le_of_tendsto (hg u).norm
      (hC.mono fun i hi => (T i).le_of_opNorm_le hi _)
  let S : W →L[𝕜] F := S₀.mkContinuous C hbound
  let e : W →L[𝕜] E := W.subtypeL
  have hdense : DenseRange e := by
    have hr : Set.range e = (W : Set E) := by simp [e]
    rw [DenseRange, hr]
    exact hM
  have he : ∀ u : W, ‖u‖ ≤ (1 : NNReal) * ‖e u‖ := by
    intro u; simp [e]
  refine ⟨S.extend e, ?_, ?_⟩
  · calc ‖S.extend e‖ ≤ (1 : NNReal) * ‖S‖ := ContinuousLinearMap.opNorm_extend_le S hdense he
      _ ≤ C := by simpa using S₀.mkContinuous_norm_le hC0 hbound
  · refine tendsto_of_dense_span_filter_of_eventually_norm_le ℱ T (S.extend e) C hC M hM ?_
    intro x hx
    have hxW : x ∈ W := Submodule.subset_span hx
    have huni : IsUniformInducing e := isometry_subtype_coe.isUniformInducing
    have hval : (S.extend e) x = g ⟨x, hxW⟩ := by
      have h := ContinuousLinearMap.extend_eq S hdense huni ⟨x, hxW⟩
      simpa [e, S, S₀] using h
    rw [hval]
    exact hg ⟨x, hxW⟩

end ContinuousLinearMap

end
