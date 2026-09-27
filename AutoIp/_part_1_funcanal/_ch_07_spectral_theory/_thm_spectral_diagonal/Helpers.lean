/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import AutoIp._part_1_funcanal._ch_04_orthonormal_series._lem_riesz_fischer
import AutoIp._part_1_funcanal._ch_06_compact_operators._lem_compact_seq
import AutoIp._part_1_funcanal._ch_06_compact_operators._lem_finrank_compact
import AutoIp._part_1_funcanal._ch_07_spectral_theory._thm_max_eigenvalue

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- A rank-one operator `x ↦ a ⟪v, x⟫ • v` with a **real** coefficient is self-adjoint. -/
public theorem isSelfAdjoint_of_apply_eq_smul_inner [CompleteSpace H] {T : H →L[𝕜] H} {a : ℝ}
    {v : H}
    (hT : ∀ x, T x = ((a : 𝕜) * inner 𝕜 v x) • v) : IsSelfAdjoint T := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  change (inner 𝕜 (T x) y : 𝕜) = inner 𝕜 x (T y)
  rw [hT, hT, inner_smul_left, inner_smul_right, map_mul, RCLike.conj_ofReal,
    inner_conj_symm]
  ring

/-- A rank-one operator is compact. -/
public theorem isCompactOperator_of_apply_eq_smul_inner {T : H →L[𝕜] H} {a : ℝ} {v : H}
    (hT : ∀ x, T x = ((a : 𝕜) * inner 𝕜 v x) • v) : IsCompactOperator T := by
  refine IsCompactOperator.of_finiteDimensional_range _ ?_
  have hle : LinearMap.range T.toLinearMap ≤ Submodule.span 𝕜 {v} := by
    rintro y ⟨x, rfl⟩
    change T x ∈ _
    rw [hT]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have : FiniteDimensional 𝕜 (Submodule.span 𝕜 ({v} : Set H)) :=
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_singleton _)
  exact Submodule.finiteDimensional_of_le hle

/-- Every compact self-adjoint operator on a nontrivial space has a **unit** eigenvector
whose eigenvalue is real and has modulus the operator norm. -/
public theorem exists_unit_eigenvector_norm_eq_norm [CompleteSpace H] [Nontrivial H] {T : H →L[𝕜] H}
    (hTc : IsCompactOperator T) (hTs : IsSelfAdjoint T) :
    ∃ p : ℝ × H, ‖p.2‖ = 1 ∧ T p.2 = ((p.1 : 𝕜)) • p.2 ∧ |p.1| = ‖T‖ := by
  obtain ⟨z₀, hz₀⟩ := exists_ne (0 : H)
  have hunit : ∀ z : H, z ≠ 0 → ‖((‖z‖ : 𝕜))⁻¹ • z‖ = 1 := by
    intro z hz
    rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    field_simp [norm_ne_zero_iff.mpr hz]
  rcases eq_or_ne T 0 with rfl | hT0
  · exact ⟨(0, ((‖z₀‖ : 𝕜))⁻¹ • z₀), hunit z₀ hz₀, by simp, by simp⟩
  · obtain ⟨mu, v, hv0, hTv, hmun⟩ := hTs.exists_eigenvalue_norm_eq_norm hTc hT0
    have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hTs
    have hvv : (inner 𝕜 v v : 𝕜) ≠ 0 := by
      simpa [inner_self_eq_zero] using hv0
    have hconj : (starRingEnd 𝕜) mu = mu := by
      have h1 : (inner 𝕜 (T v) v : 𝕜) = inner 𝕜 v (T v) := hsym v v
      rw [hTv, inner_smul_left, inner_smul_right] at h1
      exact mul_right_cancel₀ hvv h1
    have hre : ((RCLike.re mu : ℝ) : 𝕜) = mu := RCLike.conj_eq_iff_re.mp hconj
    refine ⟨(RCLike.re mu, ((‖v‖ : 𝕜))⁻¹ • v), hunit v hv0, ?_, ?_⟩
    · dsimp only
      rw [hre, map_smul, hTv, smul_comm]
    · dsimp only
      conv_rhs => rw [← hmun, ← hre]
      exact (RCLike.norm_ofReal _).symm

/-- In an expansion `K x = ∑ λᵢ ⟪uᵢ, x⟫ uᵢ` over an orthonormal family with `λᵢ → 0`, each
nonzero `μ` is taken by finitely many `λᵢ`, its eigenspace is finite-dimensional, and its
dimension is the number of indices with `λᵢ = μ`. -/
public theorem finite_and_finrank_eigenspace_eq_card {K : H →L[𝕜] H} {I : Set ℕ}
    {lam : I → ℝ} {u : I → H} (hon : Orthonormal 𝕜 u)
    (htend : I.Infinite → Filter.Tendsto lam Filter.atTop (nhds 0))
    (hsum : ∀ x : H, HasSum (fun i => ((lam i : 𝕜) * inner 𝕜 (u i) x) • u i)
      (K x)) {μ : ℝ} (hμ : μ ≠ 0) :
    {i | lam i = μ}.Finite ∧
      FiniteDimensional 𝕜 (Module.End.eigenspace (K : Module.End 𝕜 H) (μ : 𝕜)) ∧
      Module.finrank 𝕜 (Module.End.eigenspace (K : Module.End 𝕜 H) (μ : 𝕜)) =
        Nat.card {i // lam i = μ} := by
  classical
  set S : Set I := {i | lam i = μ} with hSdef
  have hSfin : S.Finite := by
    by_cases hI : I.Infinite
    · have : Nonempty I := hI.nonempty.to_subtype
      have hev := (htend hI).eventually (Metric.ball_mem_nhds 0 (abs_pos.mpr hμ))
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
      refine (Set.finite_Iio N).subset fun i hi => ?_
      by_contra hlt
      have h := hN i (not_lt.mp hlt)
      rw [Real.dist_eq, sub_zero] at h
      have hi' : lam i = μ := hi
      rw [hi'] at h
      exact lt_irrefl _ h
    · have : Finite I := Set.not_infinite.mp hI |>.to_subtype
      exact Set.toFinite S
  have hcoef : ∀ (x : H) (j : I),
      inner 𝕜 (u j) (K x) = (RCLike.ofReal (lam j) : 𝕜) * inner 𝕜 (u j) x :=
    fun x j => hon.inner_right_of_hasSum (hsum x) j
  have heig : ∀ j : I, K (u j) = (RCLike.ofReal (lam j) : 𝕜) • u j := by
    intro j
    have h := hsum (u j)
    have hfun : (fun i => ((RCLike.ofReal (lam i) : 𝕜) * inner 𝕜 (u i) (u j)) • u i)
        = fun i => if i = j then (RCLike.ofReal (lam j) : 𝕜) • u j else 0 := by
      funext i
      rw [orthonormal_iff_ite.mp hon i j]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [hfun] at h
    exact h.unique (hasSum_ite_eq j _)
  have hspan : Module.End.eigenspace (K : Module.End 𝕜 H) (RCLike.ofReal μ)
      = Submodule.span 𝕜 (Set.range (fun i : S => u i)) := by
    apply le_antisymm
    · intro x hx
      rw [Module.End.mem_eigenspace_iff] at hx
      have hx' : K x = (RCLike.ofReal μ : 𝕜) • x := hx
      have hzero : ∀ j : I, j ∉ S → inner 𝕜 (u j) x = 0 := by
        intro j hj
        have h1 := hcoef x j
        rw [hx', inner_smul_right] at h1
        have hne : (RCLike.ofReal μ : 𝕜) - RCLike.ofReal (lam j) ≠ 0 := by
          rw [sub_ne_zero, Ne, RCLike.ofReal_inj]
          exact fun h => hj h.symm
        have h2 : ((RCLike.ofReal μ : 𝕜) - RCLike.ofReal (lam j)) * inner 𝕜 (u j) x = 0 := by
          rw [sub_mul, h1, sub_self]
        exact (mul_eq_zero.mp h2).resolve_left hne
      have hfs := hsum x
      have hsupp : ∀ j ∉ hSfin.toFinset,
          ((RCLike.ofReal (lam j) : 𝕜) * inner 𝕜 (u j) x) • u j = 0 := by
        intro j hj
        rw [Set.Finite.mem_toFinset] at hj
        rw [hzero j hj, mul_zero, zero_smul]
      have hKx := hfs.unique (hasSum_sum_of_ne_finset_zero hsupp)
      have hμ' : (RCLike.ofReal μ : 𝕜) ≠ 0 := by simpa using hμ
      have hxeq : x = (RCLike.ofReal μ : 𝕜)⁻¹ • K x := by
        rw [hx', smul_smul, inv_mul_cancel₀ hμ', one_smul]
      rw [hxeq, hKx]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j hj => ?_)
      rw [Set.Finite.mem_toFinset] at hj
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨⟨j, hj⟩, rfl⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      change K (u j) = (RCLike.ofReal μ : 𝕜) • u j
      have hj' : lam j = μ := hj
      rw [heig j, hj']
  have : Fintype S := hSfin.fintype
  have hli : LinearIndependent 𝕜 (fun i : S => u i) :=
    hon.linearIndependent.comp _ Subtype.val_injective
  refine ⟨hSfin, ?_, ?_⟩
  · rw [hspan]
    exact FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)
  · rw [hspan, finrank_span_eq_card hli, ← Nat.card_eq_fintype_card]
    rfl
