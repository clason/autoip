/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import AutoIp._part_1_funcanal._ch_06_compact_operators._lem_compact_seq
import AutoIp._part_1_funcanal._ch_06_compact_operators._thm_schauder.Helpers

section _thm_schauder

section

open Metric
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If T ∈ 𝓛(E, F) is compact then so is its dual operator T′ ∈ 𝓛(F′, E′), g ↦ g ∘ T.
This direction does not assume `F` complete. -/
public theorem IsCompactOperator.dualMap {T : E →L[𝕜] F} (hT : IsCompactOperator T) :
    IsCompactOperator
      (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) := by
  refine isCompactOperator_of_totallyBounded_image_closedBall ?_
  rw [Metric.totallyBounded_iff]
  intro ε hε
  have hS : IsCompact (closure ((T : E →ₗ[𝕜] F) '' closedBall 0 1)) :=
    hT.isCompact_closure_image_closedBall 1
  set S := closure ((T : E →ₗ[𝕜] F) '' closedBall (0 : E) 1) with hSdef
  obtain ⟨t, ht, htS⟩ := Metric.totallyBounded_iff.1 hS.totallyBounded (ε / 8) (by positivity)
  have : Fintype ↥t := ht.fintype
  have : ProperSpace (↥t → 𝕜) := FiniteDimensional.proper_rclike 𝕜 _
  obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le).1 ht.isBounded
  set C' : ℝ := max C 0 with hC'
  set Θ : StrongDual 𝕜 F → (↥t → 𝕜) := fun g y => g (y : F) with hΘ
  have hΘmem : ∀ g : StrongDual 𝕜 F, ‖g‖ ≤ 1 → Θ g ∈ closedBall (0 : ↥t → 𝕜) C' := by
    intro g hg
    rw [mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun y => ?_
    calc ‖g (y : F)‖ ≤ 1 * C' := g.le_of_opNorm_le_of_le hg ((hC _ y.2).trans (le_max_left _ _))
      _ = C' := one_mul _
  obtain ⟨N, hN, hNcov⟩ :=
    Metric.totallyBounded_iff.1 (isCompact_closedBall (0 : ↥t → 𝕜) C').totallyBounded
      (ε / 8) (by positivity)
  have main : ∀ g₁ g₂ : StrongDual 𝕜 F, ‖g₁‖ ≤ 1 → ‖g₂‖ ≤ 1 →
      (∀ y ∈ t, ‖g₁ y - g₂ y‖ ≤ ε / 4) →
      ‖ContinuousLinearMap.precomp 𝕜 T g₁ - ContinuousLinearMap.precomp 𝕜 T g₂‖ ≤ ε / 2 := by
    intro g₁ g₂ h1 h2 hcl
    have hsub : ContinuousLinearMap.precomp 𝕜 T g₁ - ContinuousLinearMap.precomp 𝕜 T g₂
        = ContinuousLinearMap.precomp 𝕜 T (g₁ - g₂) := (map_sub _ _ _).symm
    rw [hsub]
    refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) ?_
    intro x hx
    have hTx : T x ∈ S := subset_closure ⟨x, by simp [hx], rfl⟩
    obtain ⟨y, hyt, hy⟩ : ∃ y ∈ t, T x ∈ ball y (ε / 8) := by
      simpa using htS hTx
    have hdist : ‖T x - y‖ < ε / 8 := by
      rw [mem_ball, dist_eq_norm] at hy; exact hy
    have hval : ContinuousLinearMap.precomp 𝕜 T (g₁ - g₂) x = (g₁ - g₂) (T x) := rfl
    rw [hval]
    have hsplit : (g₁ - g₂) (T x) = (g₁ - g₂) (T x - y) + (g₁ - g₂) y := by
      rw [← map_add]; congr 1; abel
    rw [hsplit]
    have e1 : ‖(g₁ - g₂) (T x - y)‖ ≤ ε / 4 := by
      have : ‖(g₁ - g₂) (T x - y)‖ ≤ ‖g₁ (T x - y)‖ + ‖g₂ (T x - y)‖ := by
        simpa using norm_sub_le (g₁ (T x - y)) (g₂ (T x - y))
      have b1 : ‖g₁ (T x - y)‖ ≤ ε / 8 := by
        simpa using g₁.le_of_opNorm_le_of_le h1 hdist.le
      have b2 : ‖g₂ (T x - y)‖ ≤ ε / 8 := by
        simpa using g₂.le_of_opNorm_le_of_le h2 hdist.le
      linarith
    have e2 : ‖(g₁ - g₂) y‖ ≤ ε / 4 := by
      have : (g₁ - g₂) y = g₁ y - g₂ y := by simp
      rw [this]; exact hcl y hyt
    calc ‖(g₁ - g₂) (T x - y) + (g₁ - g₂) y‖
        ≤ ‖(g₁ - g₂) (T x - y)‖ + ‖(g₁ - g₂) y‖ := norm_add_le _ _
      _ ≤ ε / 4 + ε / 4 := by linarith
      _ = ε / 2 := by ring
  have key : ∀ v : ↥t → 𝕜, ∃ w : StrongDual 𝕜 E,
      ∀ g : StrongDual 𝕜 F, ‖g‖ ≤ 1 → dist (Θ g) v < ε / 8 →
        dist (ContinuousLinearMap.precomp 𝕜 T g) w < ε := by
    intro v
    by_cases hne : ∃ g₀ : StrongDual 𝕜 F, ‖g₀‖ ≤ 1 ∧ dist (Θ g₀) v < ε / 8
    · obtain ⟨g₀, hg₀, hd₀⟩ := hne
      refine ⟨ContinuousLinearMap.precomp 𝕜 T g₀, fun g hg hgd => ?_⟩
      have hΘd : dist (Θ g) (Θ g₀) < ε / 4 := by
        have := dist_triangle (Θ g) v (Θ g₀)
        rw [dist_comm v (Θ g₀)] at this
        linarith
      have hcl : ∀ y ∈ t, ‖g y - g₀ y‖ ≤ ε / 4 := by
        intro y hy
        have h1 : dist (Θ g ⟨y, hy⟩) (Θ g₀ ⟨y, hy⟩) ≤ dist (Θ g) (Θ g₀) :=
          dist_le_pi_dist _ _ _
        have h2 : dist (Θ g ⟨y, hy⟩) (Θ g₀ ⟨y, hy⟩) = ‖g y - g₀ y‖ := dist_eq_norm _ _
        rw [h2] at h1
        linarith
      have := main g g₀ hg hg₀ hcl
      rw [dist_eq_norm]
      linarith
    · exact ⟨0, fun g hg hgd => absurd ⟨g, hg, hgd⟩ hne⟩
  choose w hw using key
  refine ⟨w '' N, hN.image w, ?_⟩
  rintro a ⟨g, hg, rfl⟩
  have hgb : ‖g‖ ≤ 1 := mem_closedBall_zero_iff.1 hg
  obtain ⟨v, hvN, hv⟩ : ∃ v ∈ N, Θ g ∈ ball v (ε / 8) := by
    simpa using Set.mem_iUnion₂.1 (hNcov (hΘmem g hgb))
  refine Set.mem_iUnion₂.2 ⟨w v, ⟨v, hvN, rfl⟩, ?_⟩
  exact hw v g hgb hv

/-- Let `E` be a normed space, `F` a Banach space and T ∈ 𝓛(E, F). Then the dual operator
T′ ∈ 𝓛(F′, E′), g ↦ g ∘ T, is compact if and only if T is. -/
public theorem IsCompactOperator.dualMap_iff [CompleteSpace F] (T : E →L[𝕜] F) :
    IsCompactOperator
        (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E)
      ↔ IsCompactOperator T := by
  refine ⟨fun h => ?_, fun h => h.dualMap⟩
  have h2 : IsCompactOperator (ContinuousLinearMap.precomp 𝕜
      (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E)
      : StrongDual 𝕜 (StrongDual 𝕜 E) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F)) :=
    h.dualMap
  set JE : E →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) := NormedSpace.inclusionInDoubleDual 𝕜 E with hJE
  set JF : F →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F) := NormedSpace.inclusionInDoubleDual 𝕜 F with hJF
  set R : E →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F) :=
    (ContinuousLinearMap.precomp 𝕜 (ContinuousLinearMap.precomp 𝕜 T)).comp JE with hR
  have hRcomp : IsCompactOperator R := h2.comp_clm JE
  have hcomm : (⇑R) = (⇑JF) ∘ (⇑T) := by
    rw [hR, hJE, hJF, ← ContinuousLinearMap.coe_comp,
      precomp_precomp_comp_inclusionInDoubleDual]
  have htb : TotallyBounded ((R : E →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F)) '' closedBall 0 1) :=
    (hRcomp.isCompact_closure_image_closedBall 1).totallyBounded.subset subset_closure
  have himg : (R : E →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F)) '' closedBall (0 : E) 1
      = (⇑JF) '' ((T : E →ₗ[𝕜] F) '' closedBall (0 : E) 1) := by
    rw [Set.image_image]
    exact Set.image_congr' (fun x => congrFun hcomm x)
  rw [himg] at htb
  have hiso : Isometry (⇑JF) :=
    (NormedSpace.inclusionInDoubleDualLi (E := F) 𝕜).isometry
  have htb2 : TotallyBounded ((T : E →ₗ[𝕜] F) '' closedBall (0 : E) 1) :=
    TotallyBounded.subset (Set.subset_preimage_image _ _)
      (totallyBounded_preimage hiso.isUniformInducing htb)
  exact isCompactOperator_of_totallyBounded_image_closedBall htb2


end

section

variable {𝕜 : Type*} [RCLike 𝕜]

/-- For T ∈ 𝓛(H, K) between Hilbert spaces, the adjoint T* is compact if and only if T
is. -/
public theorem IsCompactOperator.adjoint_iff
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K] (T : H →L[𝕜] K) :
    IsCompactOperator T.adjoint ↔ IsCompactOperator T := by
  rw [← IsCompactOperator.dualMap_iff T]
  set A := (InnerProductSpace.toDual 𝕜 H).toLinearIsometry.toContinuousLinearMap with hA
  set A' := (InnerProductSpace.toDual 𝕜 H).symm.toLinearIsometry.toContinuousLinearMap with hA'
  set B := (InnerProductSpace.toDual 𝕜 K).toLinearIsometry.toContinuousLinearMap with hB
  set B' := (InnerProductSpace.toDual 𝕜 K).symm.toLinearIsometry.toContinuousLinearMap with hB'
  have hid : ∀ g : StrongDual 𝕜 K, ContinuousLinearMap.precomp 𝕜 T g
      = InnerProductSpace.toDual 𝕜 H
          (ContinuousLinearMap.adjoint T ((InnerProductSpace.toDual 𝕜 K).symm g)) := by
    intro g
    ext x
    rw [ContinuousLinearMap.precomp_apply, ContinuousLinearMap.comp_apply,
      InnerProductSpace.toDual_apply_apply,
      ContinuousLinearMap.adjoint_inner_left, InnerProductSpace.toDual_symm_apply]
  constructor
  · intro h
    have h1 : IsCompactOperator ((⇑(ContinuousLinearMap.adjoint T)) ∘ (⇑B')) := h.comp_clm B'
    have h2 : IsCompactOperator ((⇑A) ∘ ((⇑(ContinuousLinearMap.adjoint T)) ∘ (⇑B'))) :=
      h1.clm_comp A
    have : (⇑(ContinuousLinearMap.precomp 𝕜 T))
        = (⇑A) ∘ ((⇑(ContinuousLinearMap.adjoint T)) ∘ (⇑B')) := funext hid
    rw [this]
    exact h2
  · intro h
    have h1 : IsCompactOperator ((⇑(ContinuousLinearMap.precomp 𝕜 T)) ∘ (⇑B)) := h.comp_clm B
    have h2 : IsCompactOperator ((⇑A') ∘ ((⇑(ContinuousLinearMap.precomp 𝕜 T)) ∘ (⇑B))) :=
      h1.clm_comp A'
    have : (⇑(ContinuousLinearMap.adjoint T))
        = (⇑A') ∘ ((⇑(ContinuousLinearMap.precomp 𝕜 T)) ∘ (⇑B)) := by
      funext y
      change _ = (InnerProductSpace.toDual 𝕜 H).symm
        (ContinuousLinearMap.precomp 𝕜 T (InnerProductSpace.toDual 𝕜 K y))
      rw [hid, LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply]
    rw [this]
    exact h2


end

end _thm_schauder
