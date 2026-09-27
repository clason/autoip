/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_08_svd._def_singular_system
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import AutoIp._part_1_funcanal._ch_03_hilbert_spaces._lem_kernel_normal
import AutoIp._part_1_funcanal._ch_07_spectral_theory._thm_spectral_diagonal
import AutoIp._part_1_funcanal._ch_08_svd._lem_svd_companion

section _thm_svd

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Every `K ∈ 𝒦(X,Y)` admits a singular system `{(σₙ, vₙ, uₙ)}_{n ∈ I}`, indexed by an initial
segment `I ⊆ ℕ` and ordered, and `K x = ∑ₙ σₙ ⟨vₙ, x⟩ uₙ` for all `x ∈ X`. The series is stated
as an unconditional sum. -/
public theorem IsCompactOperator.exists_isOrderedSingularSystem {K : E →L[𝕜] F}
    (hK : IsCompactOperator K) :
    ∃ (I : Set ℕ) (σ : I → ℝ) (v : I → E) (u : I → F),
      IsOrderedSingularSystem K σ v u ∧
      ∀ x : E,
        HasSum (fun i => ((σ i : 𝕜) * inner 𝕜 (v i) x) • u i) (K x) := by
  classical
  -- `T := K* K` is compact, self-adjoint and positive; diagonalise it.
  have hTsa : IsSelfAdjoint (ContinuousLinearMap.adjoint K ∘L K) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff', ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
  have hTc : IsCompactOperator (ContinuousLinearMap.adjoint K ∘L K) :=
    hK.clm_comp (ContinuousLinearMap.adjoint K)
  obtain ⟨I, lam, v, hinit, hvon, hlamne, hanti, htend, hsumT, hspanT, -⟩ :=
    hTsa.exists_ordered_hasSum_smul_inner hTc
  -- The expansion of `T` at `v j` collapses to a single term: the eigenrelation.
  have heig : ∀ j, (ContinuousLinearMap.adjoint K ∘L K) (v j) =
      (RCLike.ofReal (lam j) : 𝕜) • v j := by
    intro j
    have h := hsumT (v j)
    have hfun : (fun i => ((RCLike.ofReal (lam i) : 𝕜) * inner 𝕜 (v i) (v j)) • v i)
        = fun i => if i = j then (RCLike.ofReal (lam j) : 𝕜) • v j else 0 := by
      funext i
      rw [orthonormal_iff_ite.mp hvon i j]
      rcases eq_or_ne i j with rfl | hij
      · simp
      · simp [hij]
    rw [hfun] at h
    exact h.unique (hasSum_ite_eq j _)
  -- `lam j = ‖K (v j)‖ ^ 2 > 0`, with no reference to the system under construction.
  have hlamsq0 : ∀ j, lam j = ‖K (v j)‖ ^ 2 := by
    intro j
    have hv1 : ‖v j‖ = 1 := hvon.1 j
    have h1 : (inner 𝕜 ((ContinuousLinearMap.adjoint K ∘L K) (v j)) (v j) : 𝕜)
        = inner 𝕜 (K (v j)) (K (v j)) := by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
    rw [heig j, inner_smul_left, RCLike.conj_ofReal, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K, hv1] at h1
    have h2 : (RCLike.ofReal (lam j) : 𝕜) = RCLike.ofReal (‖K (v j)‖ ^ 2) := by
      push_cast
      simpa using h1
    exact_mod_cast h2
  have hlampos : ∀ j, 0 < lam j := by
    intro j
    rcases (hlamsq0 j) ▸ (sq_nonneg ‖K (v j)‖) with h
    exact lt_of_le_of_ne h (Ne.symm (hlamne j))
  -- The singular values and the right family.
  obtain ⟨σ, hσdef⟩ : ∃ σ : I → ℝ, ∀ i, σ i = Real.sqrt (lam i) := ⟨_, fun _ => rfl⟩
  obtain ⟨u, hudef⟩ : ∃ u : I → F, ∀ i, u i = ((RCLike.ofReal (σ i) : 𝕜))⁻¹ • K (v i) :=
    ⟨_, fun _ => rfl⟩
  have hσpos : ∀ i, 0 < σ i := fun i => by rw [hσdef]; exact Real.sqrt_pos.mpr (hlampos i)
  have hσne : ∀ i, (RCLike.ofReal (σ i) : 𝕜) ≠ 0 := fun i => by
    simpa using (hσpos i).ne'
  have hlamsq : ∀ i, lam i = σ i ^ 2 := fun i => by
    rw [hσdef, Real.sq_sqrt (hlampos i).le]
  -- Condition (4) of a singular system.
  have hmapl : ∀ i, K (v i) = (RCLike.ofReal (σ i) : 𝕜) • u i := by
    intro i
    rw [hudef i, smul_inv_smul₀ (hσne i)]
  have hmapr : ∀ i, ContinuousLinearMap.adjoint K (u i) = (RCLike.ofReal (σ i) : 𝕜) • v i := by
    intro i
    rw [hudef i, map_smul, ← ContinuousLinearMap.comp_apply, heig i, smul_smul]
    congr 1
    rw [hlamsq i]
    push_cast
    field_simp
  have huon : Orthonormal 𝕜 u := by
    rw [orthonormal_iff_ite]
    intro i j
    have h1 : (inner 𝕜 (K (v i)) (K (v j)) : 𝕜)
        = (RCLike.ofReal (lam i) : 𝕜) * inner 𝕜 (v i) (v j) := by
      rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply, heig i,
        inner_smul_left, RCLike.conj_ofReal]
    rw [hudef i, hudef j, inner_smul_left, inner_smul_right, map_inv₀, RCLike.conj_ofReal, h1,
      orthonormal_iff_ite.mp hvon i j]
    rcases eq_or_ne i j with rfl | hij
    · rw [hlamsq i]
      have := hσne i
      push_cast
      field_simp
    · simp [hij]
  -- Condition (2), the closed span of the `v i`.
  have hspanv : (Submodule.span 𝕜 (Set.range v)).topologicalClosure
      = (LinearMap.ker K.toLinearMap)ᗮ := by
    rw [hspanT, ContinuousLinearMap.topologicalClosure_range_adjoint_comp_self,
      ← ContinuousLinearMap.orthogonal_ker]
  -- Condition (3): the closed spans agree.  `⊆` because every `u i` is in the
  -- range of `K`; `⊇` by testing against the orthogonal complement.
  have hspanu : (Submodule.span 𝕜 (Set.range u)).topologicalClosure
      = (LinearMap.range K.toLinearMap).topologicalClosure := by
    have hle : (Submodule.span 𝕜 (Set.range u)).topologicalClosure
        ≤ (LinearMap.range K.toLinearMap).topologicalClosure := by
      refine Submodule.topologicalClosure_minimal _ ?_
        (Submodule.isClosed_topologicalClosure _)
      rw [Submodule.span_le]
      rintro y ⟨i, rfl⟩
      refine Submodule.le_topologicalClosure _ ?_
      exact ⟨((RCLike.ofReal (σ i) : 𝕜))⁻¹ • v i, by rw [map_smul]; exact (hudef i).symm⟩
    have hperp : (Submodule.span 𝕜 (Set.range u))ᗮ ≤ (LinearMap.range K.toLinearMap)ᗮ := by
      intro y hy
      have hyu : ∀ i, (inner 𝕜 (u i) y : 𝕜) = 0 := fun i =>
        hy (u i) (Submodule.subset_span ⟨i, rfl⟩)
      -- `K* y` is orthogonal to every `v i`, hence lies in `ker K`; but it also lies in
      -- `(ker K)ᗮ`, so it vanishes.
      have hadj : ContinuousLinearMap.adjoint K y = 0 := by
        have hperpv : ContinuousLinearMap.adjoint K y ∈ (Submodule.span 𝕜 (Set.range v))ᗮ :=
          (Submodule.isOrtho_span (𝕜 := 𝕜) (s := {ContinuousLinearMap.adjoint K y})
              (t := Set.range v)).mpr
            (by
              rintro w rfl x ⟨i, rfl⟩
              rw [← inner_conj_symm, ContinuousLinearMap.adjoint_inner_right, hmapl i,
                inner_smul_left, hyu i, mul_zero, map_zero])
            |>.le (Submodule.mem_span_singleton_self _)
        rw [← Submodule.orthogonal_closure, hspanv, Submodule.orthogonal_orthogonal] at hperpv
        have hmem : ContinuousLinearMap.adjoint K y ∈
            LinearMap.ker K.toLinearMap ⊓ (LinearMap.ker K.toLinearMap)ᗮ := by
          refine ⟨hperpv, ?_⟩
          have hrange : LinearMap.range (ContinuousLinearMap.adjoint K).toLinearMap
              ≤ (LinearMap.ker K.toLinearMap)ᗮ := by
            rw [ContinuousLinearMap.orthogonal_ker]
            exact Submodule.le_topologicalClosure _
          exact hrange ⟨y, rfl⟩
        rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hmem
      rw [Submodule.mem_orthogonal]
      rintro w ⟨x, rfl⟩
      rw [ContinuousLinearMap.coe_coe]
      rw [← ContinuousLinearMap.adjoint_inner_right, hadj, inner_zero_right]
    have hge : (LinearMap.range K.toLinearMap).topologicalClosure
        ≤ (Submodule.span 𝕜 (Set.range u)).topologicalClosure := by
      have := Submodule.orthogonal_le hperp
      rwa [Submodule.orthogonal_orthogonal_eq_closure,
        Submodule.orthogonal_orthogonal_eq_closure] at this
    exact le_antisymm hle hge
  have hsys : IsSingularSystem K σ v u :=
    { pos := hσpos
      orthonormal_left := hvon
      orthonormal_right := huon
      span_left := hspanv
      span_right := hspanu
      map_left := hmapl
      map_right := hmapr }
  refine ⟨I, σ, v, u, ⟨hsys, hinit, ?_, ?_⟩, fun x => hsys.hasSum x⟩
  · intro i j hij
    rw [hσdef, hσdef]
    refine Real.sqrt_le_sqrt ?_
    have h : |lam j| ≤ |lam i| := hanti hij
    rwa [abs_of_pos (hlampos i), abs_of_pos (hlampos j)] at h
  · intro hI
    have hfun : σ = fun i => Real.sqrt (lam i) := funext hσdef
    rw [hfun]
    simpa using (htend hI).sqrt

end _thm_svd
