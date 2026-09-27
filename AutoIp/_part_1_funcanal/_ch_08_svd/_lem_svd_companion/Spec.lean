/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_08_svd._def_singular_system
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import AutoIp._part_1_funcanal._ch_03_hilbert_spaces._lem_kernel_normal
import AutoIp._part_1_funcanal._ch_04_orthonormal_series._lem_riesz_fischer
import Mathlib.Analysis.InnerProductSpace.l2Space

section _lem_svd_companion

section

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The expansion `K x = ∑ₙ σₙ ⟨vₙ, x⟩ uₙ` for every `x ∈ X`. It is stated for a singular system
without the ordering conditions, over an arbitrary index type, and the series as an unconditional
sum. -/
public theorem IsSingularSystem.hasSum {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E}
    {u : ι → F} (hs : IsSingularSystem K σ v u) (x : E) :
    HasSum (fun i => ((σ i : 𝕜) * inner 𝕜 (v i) x) • u i) (K x) := by
  classical
  set U : Submodule 𝕜 E := (LinearMap.ker K.toLinearMap)ᗮ with hUdef
  have : CompleteSpace U :=
    (Submodule.isClosed_orthogonal (LinearMap.ker K.toLinearMap)).completeSpace_coe
  have hUperp : Uᗮ = LinearMap.ker K.toLinearMap := by
    rw [hUdef, Submodule.orthogonal_orthogonal]
  -- The `v i` lie in `U = (ker K)ᗮ`, by `span_left`.
  have hvU : ∀ i, v i ∈ U := fun i => by
    rw [hUdef, ← hs.span_left]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)
  set w : ι → U := fun i => ⟨v i, hvU i⟩ with hwdef
  -- `w` is an orthonormal basis of `U`: orthonormality is inherited from the ambient
  -- space, and totality is `span_left` again.
  have hwon : Orthonormal 𝕜 w := by
    rw [orthonormal_iff_ite]
    have hv := hs.orthonormal_left
    rw [orthonormal_iff_ite] at hv
    intro i j
    simpa [hwdef] using hv i j
  have hwsp : (Submodule.span 𝕜 (Set.range w))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    have hz0 : ∀ i, inner 𝕜 (v i) (z : E) = 0 := by
      intro i
      simpa [hwdef] using hz (w i) (Submodule.subset_span ⟨i, rfl⟩)
    have hzperp : (z : E) ∈ (Submodule.span 𝕜 (Set.range v))ᗮ :=
      (Submodule.isOrtho_span (𝕜 := 𝕜) (s := {(z : E)}) (t := Set.range v)).mpr
        (by rintro u rfl y ⟨i, rfl⟩; exact inner_eq_zero_symm.mp (hz0 i))
        |>.le (Submodule.mem_span_singleton_self _)
    rw [← Submodule.orthogonal_closure, hs.span_left, ← hUdef, hUperp] at hzperp
    have : (z : E) = 0 := by
      have hmem : (z : E) ∈ LinearMap.ker K.toLinearMap ⊓ (LinearMap.ker K.toLinearMap)ᗮ :=
        ⟨hzperp, z.2⟩
      rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hmem
    exact Submodule.coe_eq_zero.mp this
  have hb : ⇑(HilbertBasis.mkOfOrthogonalEqBot hwon hwsp) = w :=
    HilbertBasis.coe_mkOfOrthogonalEqBot _ _
  -- Expand the projection, then push `K` through the series.
  have hproj := (HilbertBasis.mkOfOrthogonalEqBot hwon hwsp).hasSum_orthogonalProjectionOnto x
  have hmap := hproj.mapL (K ∘L U.subtypeL)
  -- `K` does not see the kernel component of `x`.
  have hKproj : K ((U.orthogonalProjectionOnto x : U) : E) = K x := by
    have hmem : x - U.starProjection x ∈ Uᗮ := U.sub_starProjection_mem_orthogonal x
    rw [hUperp, LinearMap.mem_ker] at hmem
    simp only [ContinuousLinearMap.coe_coe, map_sub, sub_eq_zero] at hmem
    exact hmem.symm
  simpa only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, map_smul, hb, hwdef,
    hs.map_left, smul_smul, mul_comm, hKproj] using hmap


end

section

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F}

/-- The eigenrelation `K*K vₙ = σₙ² vₙ` for every index `n`. It is stated for a singular system
without the ordering conditions, over an arbitrary index type. -/
public theorem IsSingularSystem.adjoint_comp_self_apply
    {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F} (hs : IsSingularSystem K σ v u)
    (i : ι) :
    (K.adjoint ∘L K) (v i) = ((σ i ^ 2 : ℝ) : 𝕜) • v i := by
  rw [ContinuousLinearMap.comp_apply, hs.map_left, map_smul, hs.map_right, smul_smul,
    ← RCLike.ofReal_mul, ← sq]

/-- `{(σₙ, uₙ, vₙ)}` satisfies the conditions of a singular system of `K*` that do not concern the
order of the singular values. -/
public theorem IsSingularSystem.adjoint
    {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F} (hs : IsSingularSystem K σ v u) :
    IsSingularSystem K.adjoint σ u v where
  pos := hs.pos
  orthonormal_left := hs.orthonormal_right
  orthonormal_right := hs.orthonormal_left
  span_left := by
    rw [hs.span_right, ContinuousLinearMap.orthogonal_ker,
      ContinuousLinearMap.adjoint_adjoint]
  span_right := by
    rw [hs.span_left, ContinuousLinearMap.orthogonal_ker]
  map_left := hs.map_right
  map_right := by
    simpa only [ContinuousLinearMap.adjoint_adjoint] using hs.map_left

/-- `{(σₙ², vₙ, vₙ)}` satisfies the conditions of a singular system of `K*K` that do not concern
the order of the singular values. -/
public theorem IsSingularSystem.adjoint_comp_self
    {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F} (hs : IsSingularSystem K σ v u) :
    IsSingularSystem (K.adjoint ∘L K) (fun i => σ i ^ 2) v v where
  pos i := pow_pos (hs.pos i) 2
  orthonormal_left := hs.orthonormal_left
  orthonormal_right := hs.orthonormal_left
  span_left := by
    rw [hs.span_left, ContinuousLinearMap.ker_adjoint_comp_self]
  span_right := by
    rw [hs.span_left, ContinuousLinearMap.topologicalClosure_range_adjoint_comp_self,
      ContinuousLinearMap.orthogonal_ker]
  map_left := hs.adjoint_comp_self_apply
  map_right i := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
    exact hs.adjoint_comp_self_apply i

/-- The expansion `K* y = ∑ₙ σₙ ⟨uₙ, y⟩ vₙ` for every `y ∈ Y`. It is stated for a singular system
without the ordering conditions, over an arbitrary index type, and the series as an unconditional
sum. -/
public theorem IsSingularSystem.hasSum_adjoint
    {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F} (hs : IsSingularSystem K σ v u) (y : F) :
    HasSum (fun i => ((σ i : 𝕜) * inner 𝕜 (u i) y) • v i)
      (K.adjoint y) :=
  hs.adjoint.hasSum y

/-- The expansion `K*K x = ∑ₙ σₙ² ⟨vₙ, x⟩ vₙ` for every `x ∈ X`. It is stated for a singular
system without the ordering conditions, over an arbitrary index type, and the series as an
unconditional sum. -/
public theorem IsSingularSystem.hasSum_adjoint_comp_self
    {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F} (hs : IsSingularSystem K σ v u) (x : E) :
    HasSum (fun i => (((σ i ^ 2 : ℝ) : 𝕜) * inner 𝕜 (v i) x) • v i)
      ((K.adjoint ∘L K) x) :=
  hs.adjoint_comp_self.hasSum x

/-- The eigenrelation `KK* uₙ = σₙ² uₙ` for every index `n`. It is stated for a singular system
without the ordering conditions, over an arbitrary index type. -/
public theorem IsSingularSystem.self_comp_adjoint_apply
    {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F} (hs : IsSingularSystem K σ v u) (i : ι) :
    (K ∘L K.adjoint) (u i) = ((σ i ^ 2 : ℝ) : 𝕜) • u i := by
  rw [ContinuousLinearMap.comp_apply, hs.map_right, map_smul, hs.map_left, smul_smul,
    ← RCLike.ofReal_mul, ← sq]

/-- A real `λ ≠ 0` is an eigenvalue of `K*K` if and only if `λ = σₙ²` for some index `n`. It is
stated for a singular system without the ordering conditions, over an arbitrary index type. -/
public
theorem IsSingularSystem.hasEigenvalue_sq_iff_of_ne_zero
    {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F} (hs : IsSingularSystem K σ v u) {lam : ℝ}
    (hlam : lam ≠ 0) :
    Module.End.HasEigenvalue (K.adjoint ∘L K).toLinearMap
        (lam : 𝕜) ↔ ∃ i, σ i ^ 2 = lam := by
  have hlam' : (RCLike.ofReal lam : 𝕜) ≠ 0 := by
    simpa using hlam
  constructor
  · intro hev
    obtain ⟨w, hwmem, hw0⟩ := hev.exists_hasEigenvector
    rw [Module.End.mem_eigenspace_iff] at hwmem
    simp only [ContinuousLinearMap.coe_coe] at hwmem
    by_contra hcon
    push Not at hcon
    -- Testing the eigenrelation against `v i` and using `K*K v i = σ i ² v i`, every
    -- coefficient `⟪v i, w⟫` vanishes, since `σ i ² ≠ lam`.
    have hzero : ∀ i, inner 𝕜 (v i) w = 0 := by
      intro i
      have h1 : inner 𝕜 (v i) ((ContinuousLinearMap.adjoint K ∘L K) w)
          = (RCLike.ofReal (σ i ^ 2) : 𝕜) * inner 𝕜 (v i) w := by
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
          ← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply,
          hs.adjoint_comp_self_apply i, inner_smul_left, RCLike.conj_ofReal]
      have h2 : inner 𝕜 (v i) ((ContinuousLinearMap.adjoint K ∘L K) w)
          = (RCLike.ofReal lam : 𝕜) * inner 𝕜 (v i) w := by
        rw [hwmem, inner_smul_right]
      have h3 : ((RCLike.ofReal (σ i ^ 2) : 𝕜) - RCLike.ofReal lam) * inner 𝕜 (v i) w = 0 := by
        rw [sub_mul, ← h1, ← h2, sub_self]
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd (by exact_mod_cast sub_eq_zero.mp h) (hcon i)
      · exact h
    -- So `w` is orthogonal to every `v i`, hence lies in `ker K`.
    have hwperp : w ∈ (Submodule.span 𝕜 (Set.range v))ᗮ :=
      (Submodule.isOrtho_span (𝕜 := 𝕜) (s := {w}) (t := Set.range v)).mpr
        (by rintro y rfl x ⟨i, rfl⟩; exact inner_eq_zero_symm.mp (hzero i))
        |>.le (Submodule.mem_span_singleton_self _)
    rw [← Submodule.orthogonal_closure, hs.span_left, Submodule.orthogonal_orthogonal] at hwperp
    -- But `lam ≠ 0` puts `w` in the range of `K*`, hence in `(ker K)ᗮ`.
    have hwU : w ∈ (LinearMap.ker K.toLinearMap)ᗮ := by
      have hrange : LinearMap.range (ContinuousLinearMap.adjoint K).toLinearMap
          ≤ (LinearMap.ker K.toLinearMap)ᗮ := by
        rw [ContinuousLinearMap.orthogonal_ker]
        exact Submodule.le_topologicalClosure _
      have hw : w = (RCLike.ofReal lam : 𝕜)⁻¹ • ContinuousLinearMap.adjoint K (K w) := by
        rw [← ContinuousLinearMap.comp_apply, hwmem, smul_smul, inv_mul_cancel₀ hlam', one_smul]
      rw [hw]
      exact Submodule.smul_mem _ _ (hrange ⟨K w, rfl⟩)
    refine hw0 ?_
    have hmem : w ∈ LinearMap.ker K.toLinearMap ⊓ (LinearMap.ker K.toLinearMap)ᗮ :=
      ⟨hwperp, hwU⟩
    rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hmem
  · rintro ⟨i, rfl⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := v i) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact hs.adjoint_comp_self_apply i
    · intro h
      have hn := hs.orthonormal_left.1 i
      rw [h, norm_zero] at hn
      exact one_ne_zero hn.symm

/-- `{(σₙ², uₙ, uₙ)}` satisfies the conditions of a singular system of `KK*` that do not concern
the order of the singular values. -/
public theorem IsSingularSystem.self_comp_adjoint
    {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F} (hs : IsSingularSystem K σ v u) :
    IsSingularSystem (K ∘L K.adjoint) (fun i => σ i ^ 2) u u := by
  simpa only [ContinuousLinearMap.adjoint_adjoint] using hs.adjoint.adjoint_comp_self

/-- `{(σₙ, uₙ, vₙ)}_{n ∈ I}` is a singular system of `K*`. -/
public theorem IsOrderedSingularSystem.adjoint {I : Set ℕ} {σ : I → ℝ} {v : I → E} {u : I → F}
    (hs : IsOrderedSingularSystem K σ v u) :
    IsOrderedSingularSystem K.adjoint σ u v :=
  { hs.toIsSingularSystem.adjoint with
    isLowerSet := hs.isLowerSet
    antitone := hs.antitone
    tendsto_zero := hs.tendsto_zero }

/-- `{(σₙ², vₙ, vₙ)}_{n ∈ I}` is a singular system of `K*K`. -/
public theorem IsOrderedSingularSystem.adjoint_comp_self {I : Set ℕ} {σ : I → ℝ} {v : I → E}
    {u : I → F} (hs : IsOrderedSingularSystem K σ v u) :
    IsOrderedSingularSystem (K.adjoint ∘L K) (fun i => σ i ^ 2) v v :=
  { hs.toIsSingularSystem.adjoint_comp_self with
    isLowerSet := hs.isLowerSet
    antitone := fun _ _ hij => pow_le_pow_left₀ (hs.pos _).le (hs.antitone hij) 2
    tendsto_zero := fun h => by simpa using (hs.tendsto_zero h).pow 2 }

/-- `{(σₙ², uₙ, uₙ)}_{n ∈ I}` is a singular system of `KK*`. -/
public theorem IsOrderedSingularSystem.self_comp_adjoint {I : Set ℕ} {σ : I → ℝ} {v : I → E}
    {u : I → F} (hs : IsOrderedSingularSystem K σ v u) :
    IsOrderedSingularSystem (K ∘L K.adjoint) (fun i => σ i ^ 2) u u :=
  { hs.toIsSingularSystem.self_comp_adjoint with
    isLowerSet := hs.isLowerSet
    antitone := fun _ _ hij => pow_le_pow_left₀ (hs.pos _).le (hs.antitone hij) 2
    tendsto_zero := fun h => by simpa using (hs.tendsto_zero h).pow 2 }

end

end _lem_svd_companion
