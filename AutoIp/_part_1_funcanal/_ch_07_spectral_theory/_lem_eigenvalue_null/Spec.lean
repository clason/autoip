/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
import Cite.Attribute
import Std.Tactic.BVDecide.Normalize.Prop

section _lem_eigenvalue_null

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [CompleteSpace H]

/-- Clause (1): for a compact operator K on a Hilbert space and every ε > 0, the set
{λ ∈ σ(K) : |λ| ≥ ε} is finite. -/
public theorem IsCompactOperator.finite_spectrum_norm_ge {K : H →L[𝕜] H}
    (hK : IsCompactOperator K) {ε : ℝ} (hε : 0 < ε) :
    {μ ∈ spectrum 𝕜 K | ε ≤ ‖μ‖}.Finite := by
  classical
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨f, hfinj⟩ := hinf.natEmbedding
  set lam : ℕ → 𝕜 := fun n => (f n : 𝕜) with hlam
  have hlaminj : Function.Injective lam := Subtype.coe_injective.comp hfinj
  have hmem : ∀ n, lam n ∈ spectrum 𝕜 K := fun n => (f n).2.1
  have hnorm : ∀ n, ε ≤ ‖lam n‖ := fun n => (f n).2.2
  have hne : ∀ n, lam n ≠ 0 := fun n h => by
    have := hnorm n; rw [h, norm_zero] at this; linarith
  have hev : ∀ n, Module.End.HasEigenvalue (K : H →ₗ[𝕜] H) (lam n) := fun n =>
    (hK.hasEigenvalue_iff_mem_spectrum (hne n)).2 (hmem n)
  choose x hx using fun n => (hev n).exists_hasEigenvector
  have hKx : ∀ n, K (x n) = lam n • x n := fun n => (hx n).apply_eq_smul
  have hind : LinearIndependent 𝕜 x :=
    Module.End.eigenvectors_linearIndependent' (K : H →ₗ[𝕜] H) lam hlaminj x hx
  set U : ℕ → Submodule 𝕜 H := fun n => Submodule.span 𝕜 (x '' Set.Iio n) with hU
  have hUmono : Monotone U := fun a b hab =>
    Submodule.span_mono (Set.image_mono fun _ h => lt_of_lt_of_le h hab)
  have hUfd : ∀ n, FiniteDimensional 𝕜 (U n) := fun n => by
    rw [hU]; exact FiniteDimensional.span_of_finite 𝕜 ((Set.finite_Iio n).image x)
  have hxU : ∀ n, x n ∈ U (n + 1) := fun n => Submodule.subset_span ⟨n, by simp, rfl⟩
  have hxnot : ∀ n, x n ∉ U n := fun n => hind.notMem_span_image (by simp)
  have hKU : ∀ n, ∀ u ∈ U n, K u ∈ U n := by
    intro n u hu
    have hle : Submodule.map (K : H →ₗ[𝕜] H) (U n) ≤ U n := by
      rw [hU, Submodule.map_span, Submodule.span_le]
      rintro w ⟨-, ⟨j, hj, rfl⟩, rfl⟩
      change K (x j) ∈ U n
      rw [hKx j]
      exact (U n).smul_mem _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    exact hle ⟨u, hu, rfl⟩
  -- `lam m • id - K` kills `x m` and scales the earlier generators, so it drops a
  -- level.
  have hshift : ∀ m, ∀ u ∈ U (m + 1), lam m • u - K u ∈ U m := by
    intro m u hu
    have hle : Submodule.map ((lam m • ContinuousLinearMap.id 𝕜 H - K) : H →ₗ[𝕜] H)
        (U (m + 1)) ≤ U m := by
      rw [hU, Submodule.map_span, Submodule.span_le]
      rintro w ⟨-, ⟨j, hj, rfl⟩, rfl⟩
      change (lam m • ContinuousLinearMap.id 𝕜 H - K) (x j) ∈ U m
      simp only [sub_apply, smul_apply, ContinuousLinearMap.id_apply, hKx j, ← sub_smul]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hlt | rfl
      · exact (U m).smul_mem _ (Submodule.subset_span ⟨j, hlt, rfl⟩)
      · simp
    exact hle ⟨u, hu, rfl⟩
  -- A unit vector in `U (m+1)` orthogonal to `U m`: the normalized component of
  -- `x m` off `U m`, which is nonzero because `x m ∉ U m`.
  have hproj : ∀ n, (U n).HasOrthogonalProjection := fun n => by
    have := hUfd n; infer_instance
  set w : ℕ → H := fun n => x n - (U n).starProjection (x n) with hw
  have hwne : ∀ n, w n ≠ 0 := by
    intro n h
    refine hxnot n ?_
    have : x n = (U n).starProjection (x n) := by
      rw [hw] at h; simpa using sub_eq_zero.mp h
    rw [this]
    exact (U n).starProjection_apply_mem (x n)
  set y : ℕ → H := fun n => (‖w n‖⁻¹ : 𝕜) • w n with hy
  have hy1 : ∀ n, ‖y n‖ = 1 := fun n => norm_smul_inv_norm (hwne n)
  have hyU : ∀ n, y n ∈ U (n + 1) := by
    intro n
    refine (U (n + 1)).smul_mem _ (sub_mem (hxU n) ?_)
    exact hUmono (Nat.le_succ n) ((U n).starProjection_apply_mem (x n))
  have hyperp : ∀ n, y n ∈ (U n)ᗮ := fun n =>
    (U n)ᗮ.smul_mem _ ((U n).sub_starProjection_mem_orthogonal (x n))
  -- Separation: for `l < m` the two images are `ε` apart.
  have hsep : ∀ l m, l < m → ε ≤ ‖K (y m) - K (y l)‖ := by
    intro l m hlm
    have hz : (lam m • y m - K (y m)) + K (y l) ∈ U m := by
      refine add_mem (hshift m (y m) (hyU m)) ?_
      exact hUmono hlm (hKU (l + 1) (y l) (hyU l))
    set z : H := (lam m • y m - K (y m)) + K (y l) with hzdef
    have hrewrite : K (y m) - K (y l) = lam m • y m - z := by rw [hzdef]; abel
    have hinner : (inner 𝕜 (lam m • y m) z : 𝕜) = 0 := by
      have h0 : (inner 𝕜 z (y m) : 𝕜) = 0 :=
        (Submodule.mem_orthogonal _ _).1 (hyperp m) z hz
      rw [inner_smul_left, ← inner_conj_symm, h0, map_zero, mul_zero]
    rw [hrewrite]
    have hpyth : ‖lam m • y m - z‖ ^ 2 = ‖lam m • y m‖ ^ 2 + ‖z‖ ^ 2 := by
      rw [norm_sub_sq (𝕜 := 𝕜), hinner]
      simp
    have hnm : ‖lam m • y m‖ = ‖lam m‖ := by rw [norm_smul, hy1 m, mul_one]
    nlinarith [hnorm m, norm_nonneg z, norm_nonneg (lam m • y m - z), hε,
      norm_nonneg (lam m)]
  -- `{y n}` is bounded, so `{K (y n)}` lies in a compact set and has a convergent,
  -- hence Cauchy, subsequence — contradicting the separation.
  have hcpt : IsCompact (closure (K '' Metric.ball 0 2)) :=
    (isCompactOperator_iff_isCompact_closure_image_ball (K : H →ₗ[𝕜] H)
      (by norm_num)).1 hK
  have hmemc : ∀ n, K (y n) ∈ closure (K '' Metric.ball 0 2) := by
    intro n
    refine subset_closure ⟨y n, ?_, rfl⟩
    simp [Metric.mem_ball, dist_zero_right, hy1 n]
  obtain ⟨a, -, φ, hφ, hconv⟩ := hcpt.tendsto_subseq hmemc
  have hcauchy : CauchySeq (fun i => K (y (φ i))) := hconv.cauchySeq
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hcauchy ε hε
  have hlt := hN (N + 1) (Nat.le_succ N)
  rw [dist_eq_norm] at hlt
  exact absurd (hsep (φ N) (φ (N + 1)) (hφ (Nat.lt_succ_self N))) (by linarith)

/-- Clause (2), first half: the spectrum σ(K) of a compact operator K on a Hilbert space is
at most countable. -/
public theorem IsCompactOperator.countable_spectrum {K : H →L[𝕜] H}
    (hK : IsCompactOperator K) : (spectrum 𝕜 K).Countable := by
  have hcover : spectrum 𝕜 K ⊆
      {0} ∪ ⋃ k : ℕ, {μ ∈ spectrum 𝕜 K | 1 / (k + 1 : ℝ) ≤ ‖μ‖} := by
    intro μ hμ
    rcases eq_or_ne μ 0 with rfl | hne
    · exact Set.mem_union_left _ rfl
    · obtain ⟨k, hk⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hne)
      exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨k, hμ, hk.le⟩)
  refine Set.Countable.mono hcover ?_
  exact (Set.countable_singleton 0).union
    (Set.countable_iUnion fun k =>
      (hK.finite_spectrum_norm_ge (by positivity)).countable)

/-- Clause (2), second half: the only possible accumulation point of the spectrum σ(K) of a
compact operator K on a Hilbert space is 0. -/
public theorem IsCompactOperator.eq_zero_of_accPt_spectrum {K : H →L[𝕜] H}
    (hK : IsCompactOperator K) {μ : 𝕜}
    (h : AccPt μ (Filter.principal (spectrum 𝕜 K))) : μ = 0 := by
  by_contra hne
  have hμ0 : 0 < ‖μ‖ := norm_pos_iff.mpr hne
  have hpos : 0 < ‖μ‖ / 2 := by linarith
  set S := {ν ∈ spectrum 𝕜 K | ‖μ‖ / 2 ≤ ‖ν‖} with hS
  have hclosed : IsClosed (S \ {μ}) :=
    ((hK.finite_spectrum_norm_ge hpos).sdiff).isClosed
  have hUnhds : Metric.ball μ (‖μ‖ / 2) ∩ (S \ {μ})ᶜ ∈ nhds μ :=
    Filter.inter_mem (Metric.ball_mem_nhds _ hpos)
      (hclosed.isOpen_compl.mem_nhds (by simp))
  obtain ⟨ν, ⟨⟨hνball, hνout⟩, hνspec⟩, hνne⟩ := accPt_iff_nhds.1 h _ hUnhds
  have hνS : ν ∈ S := by
    refine ⟨hνspec, ?_⟩
    have hd : ‖ν - μ‖ < ‖μ‖ / 2 := by
      rw [← dist_eq_norm]; exact Metric.mem_ball.1 hνball
    have hle := norm_sub_norm_le μ ν
    have h2 : ‖μ - ν‖ = ‖ν - μ‖ := norm_sub_rev μ ν
    linarith [h2 ▸ hle]
  exact hνne (by simpa [hνS] using hνout)


attribute [cite] ContinuousLinearMap.finite_dimensional_eigenspace
attribute [cite] IsCompactOperator.hasEigenvalue_iff_mem_spectrum

end _lem_eigenvalue_null
