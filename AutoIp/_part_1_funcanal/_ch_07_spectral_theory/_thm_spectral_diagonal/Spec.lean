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
import Mathlib.Algebra.Order.Ring.Star
import AutoIp._part_1_funcanal._ch_07_spectral_theory._thm_spectral_diagonal.Helpers

section _thm_spectral_diagonal

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [CompleteSpace H]

/-- Let K be compact and self-adjoint on a Hilbert space `H`. Then there are an initial
segment I ⊆ ℕ, an orthonormal system (uₙ)_{n ∈ I} and nonzero reals (λₙ)_{n ∈ I} with
|λ₁| ≥ |λ₂| ≥ ⋯ such that Kx = ∑_{n ∈ I} λₙ⟨uₙ, x⟩uₙ for all x ∈ H, and the closed span of
(uₙ) is the closure of 𝓡(K), so that (uₙ) is an orthonormal basis of it. If I is infinite then
λₙ → 0. Each nonzero real μ occurs among the λₙ exactly dim 𝒩(K − μ Id) < ∞ times. -/
public theorem IsSelfAdjoint.exists_ordered_hasSum_smul_inner {K : H →L[𝕜] H}
    (hsa : IsSelfAdjoint K) (hc : IsCompactOperator K) :
    ∃ (I : Set ℕ) (lam : I → ℝ) (u : I → H),
      (∀ ⦃m n : ℕ⦄, n ∈ I → m ≤ n → m ∈ I) ∧
      Orthonormal 𝕜 u ∧
      (∀ i, lam i ≠ 0) ∧
      Antitone (fun i => |lam i|) ∧
      (I.Infinite → Filter.Tendsto lam Filter.atTop (nhds 0)) ∧
      (∀ x : H, HasSum (fun i => ((lam i : 𝕜) * inner 𝕜 (u i) x) • u i)
        (K x)) ∧
      (Submodule.span 𝕜 (Set.range u)).topologicalClosure =
        K.toLinearMap.range.topologicalClosure ∧
      (∀ μ : ℝ, μ ≠ 0 → {i | lam i = μ}.Finite ∧
        FiniteDimensional 𝕜 (Module.End.eigenspace (K : Module.End 𝕜 H) (μ : 𝕜)) ∧
        Module.finrank 𝕜 (Module.End.eigenspace (K : Module.End 𝕜 H) (μ : 𝕜)) =
          Nat.card {i // lam i = μ}) := by
  have aux :
      ∃ (I : Set ℕ) (lam : I → ℝ) (u : I → H),
        (∀ ⦃m n : ℕ⦄, n ∈ I → m ≤ n → m ∈ I) ∧
        Orthonormal 𝕜 u ∧
        (∀ i, lam i ≠ 0) ∧
        Antitone (fun i => |lam i|) ∧
        (I.Infinite → Filter.Tendsto lam Filter.atTop (nhds 0)) ∧
        (∀ x : H, HasSum (fun i => ((RCLike.ofReal (lam i) : 𝕜) * inner 𝕜 (u i) x) • u i)
          (K x)) ∧
        (Submodule.span 𝕜 (Set.range u)).topologicalClosure =
          (LinearMap.range K.toLinearMap).topologicalClosure := by
    classical
    rcases eq_or_ne K 0 with rfl | hK0
    · -- `K = 0`: the empty index set works, and every clause is vacuous.
      have : IsEmpty ((∅ : Set ℕ) : Type) := Set.isEmpty_coe_sort.mpr rfl
      refine ⟨∅, isEmptyElim, isEmptyElim, ?_,
        ⟨fun i => isEmptyElim i, fun {i j} _ => isEmptyElim i⟩, fun i => isEmptyElim i,
        fun i j _ => isEmptyElim i, ?_, ?_, ?_⟩
      · intro m n hn _; simp at hn
      · intro h; simp at h
      · intro x
        show HasSum _ ((0 : H →L[𝕜] H) x)
        rw [show ((0 : H →L[𝕜] H) x) = 0 from rfl]
        exact hasSum_empty
      · have h1 : Set.range (isEmptyElim : ((∅ : Set ℕ) : Type) → H) = ∅ := Set.range_eq_empty _
        rw [h1, Submodule.span_empty]
        congr 1
        simp
    -- `K ≠ 0` forces `H` to be nontrivial, which is what the step below needs.
    obtain ⟨z₀, hz₀⟩ : ∃ z : H, z ≠ 0 := by
      by_contra hcon
      have hall : ∀ z : H, z = 0 := fun z => not_not.mp fun h => hcon ⟨z, h⟩
      exact hK0 (by ext z; rw [hall z]; simp)
    have : Nontrivial H := ⟨⟨z₀, 0, hz₀⟩⟩
    -- Step 1: a unit eigenvector at each stage of the recursion.
    have hstep : ∀ T : H →L[𝕜] H, IsCompactOperator T → IsSelfAdjoint T →
        ∃ p : ℝ × H, ‖p.2‖ = 1 ∧ T p.2 = ((p.1 : 𝕜)) • p.2 ∧ |p.1| = ‖T‖ :=
      fun _ hTc hTs => exists_unit_eigenvector_norm_eq_norm hTc hTs
    choose! g hg1 hg2 hg3 using hstep
    -- The rank-one operator `x ↦ (a ⟪v, x⟫) • v` subtracted at each step.
    obtain ⟨rk1, hrk1⟩ : ∃ rk1 : ℝ × H → (H →L[𝕜] H),
        ∀ p x, rk1 p x = ((p.1 : 𝕜) * inner 𝕜 p.2 x) • p.2 :=
      ⟨fun p => ((p.1 : 𝕜) • (innerSL 𝕜 p.2)).smulRight p.2, fun p x => by simp⟩
    have hrk1sa : ∀ p : ℝ × H, IsSelfAdjoint (rk1 p) :=
      fun p => isSelfAdjoint_of_apply_eq_smul_inner (hrk1 p)
    have hrk1c : ∀ p : ℝ × H, IsCompactOperator (rk1 p) :=
      fun p => isCompactOperator_of_apply_eq_smul_inner (hrk1 p)
    -- Step 2: the recursion.  `A n` is `K` with the first `n` rank-one pieces removed.
    obtain ⟨A, hA0, hAsucc⟩ : ∃ A : ℕ → (H →L[𝕜] H),
        A 0 = K ∧ ∀ n, A (n + 1) = A n - rk1 (g (A n)) :=
      ⟨fun n => Nat.rec K (fun _ T => T - rk1 (g T)) n, rfl, fun _ => rfl⟩
    obtain ⟨lam, u, hlamdef, hudef⟩ : ∃ (lam : ℕ → ℝ) (u : ℕ → H),
        (∀ n, lam n = (g (A n)).1) ∧ ∀ n, u n = (g (A n)).2 :=
      ⟨_, _, fun _ => rfl, fun _ => rfl⟩
    have hrk1n : ∀ (n : ℕ) (x : H),
        rk1 (g (A n)) x = ((lam n : 𝕜) * inner 𝕜 (u n) x) • u n := by
      intro n x
      rw [hrk1, hlamdef, hudef]
    -- The invariant carried along the recursion.
    have hind : ∀ n : ℕ, IsCompactOperator (A n) ∧ IsSelfAdjoint (A n) ∧
        ∀ k, k < n → A n (u k) = 0 := by
      intro n
      induction n with
      | zero => exact ⟨hA0 ▸ hc, hA0 ▸ hsa, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
      | succ n ih =>
        obtain ⟨hAcn, hAsn, hAkn⟩ := ih
        have hn1 : ‖u n‖ = 1 := by rw [hudef]; exact hg1 _ hAcn hAsn
        have hn2 : A n (u n) = ((lam n : 𝕜)) • u n := by
          rw [hudef, hlamdef]; exact hg2 _ hAcn hAsn
        have hsymn := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hAsn
        have horthn : ∀ k, k < n → ((lam n : 𝕜)) * inner 𝕜 (u k) (u n) = 0 := by
          intro k hk
          have h1 : (inner 𝕜 (A n (u k)) (u n) : 𝕜) = inner 𝕜 (u k) (A n (u n)) := hsymn _ _
          rw [hAkn k hk, hn2, inner_zero_left, inner_smul_right] at h1
          exact h1.symm
        refine ⟨?_, ?_, ?_⟩
        · rw [hAsucc n]
          simpa using hAcn.sub (hrk1c (g (A n)))
        · rw [hAsucc n]
          exact hAsn.sub (hrk1sa _)
        · intro k hk
          rw [hAsucc n, sub_apply, hrk1n n]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
          · have h0 : ((lam n : 𝕜)) * inner 𝕜 (u n) (u k) = 0 := by
              have h2 := congrArg (starRingEnd 𝕜) (horthn k hk')
              simpa [map_mul, RCLike.conj_ofReal, inner_conj_symm] using h2
            rw [hAkn k hk', h0, zero_smul, sub_zero]
          · rw [hn2, inner_self_eq_norm_sq_to_K, hn1]
            simp
    have hAc : ∀ n, IsCompactOperator (A n) := fun n => (hind n).1
    have hAs : ∀ n, IsSelfAdjoint (A n) := fun n => (hind n).2.1
    have hun : ∀ n, ‖u n‖ = 1 := fun n => by rw [hudef]; exact hg1 _ (hAc n) (hAs n)
    have hAu : ∀ n, A n (u n) = ((lam n : 𝕜)) • u n := fun n => by
      rw [hudef, hlamdef]; exact hg2 _ (hAc n) (hAs n)
    have hlamnorm : ∀ n, |lam n| = ‖A n‖ := fun n => by
      rw [hlamdef]; exact hg3 _ (hAc n) (hAs n)
    -- Step 3: orthogonality.
    have horth : ∀ m n : ℕ, m < n → lam n ≠ 0 → (inner 𝕜 (u m) (u n) : 𝕜) = 0 := by
      intro m n hmn hne
      have hsymn := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hAs n)
      have h1 : (inner 𝕜 (A n (u m)) (u n) : 𝕜) = inner 𝕜 (u m) (A n (u n)) := hsymn _ _
      rw [(hind n).2.2 m hmn, hAu n, inner_zero_left, inner_smul_right] at h1
      have hne' : ((lam n : 𝕜)) ≠ 0 := by simpa using hne
      exact (mul_eq_zero.mp h1.symm).resolve_left hne'
    have hAapply : ∀ (n : ℕ) (x : H), A n x = K x - ∑ k ∈ Finset.range n,
        ((lam k : 𝕜) * inner 𝕜 (u k) x) • u k := by
      intro n
      induction n with
      | zero => intro x; rw [hA0]; simp
      | succ n ih =>
        intro x
        rw [hAsucc n, sub_apply, ih x, hrk1n n x, Finset.sum_range_succ]
        abel
    have hKu : ∀ n, lam n ≠ 0 → K (u n) = ((lam n : 𝕜)) • u n := by
      intro n hn
      have h := hAapply n (u n)
      rw [hAu n] at h
      have hz : ∑ k ∈ Finset.range n, ((lam k : 𝕜) * inner 𝕜 (u k) (u n)) • u k = 0 :=
        Finset.sum_eq_zero fun k hk => by
          rw [horth k n (Finset.mem_range.mp hk) hn, mul_zero, zero_smul]
      rw [hz, sub_zero] at h
      exact h.symm
    -- Step 4: `‖A n‖` is non-increasing, which is the ordering of the eigenvalues.
    have hAanti : Antitone fun n => ‖A n‖ := by
      refine antitone_nat_of_succ_le fun n => ?_
      rw [hAsucc n]
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
      have hval : (A n - rk1 (g (A n))) x = A n (x - (inner 𝕜 (u n) x : 𝕜) • u n) := by
        rw [sub_apply, hrk1n n, map_sub, map_smul, hAu n, smul_smul,
          mul_comm (inner 𝕜 (u n) x : 𝕜) ((lam n : ℝ) : 𝕜)]
      -- `x - ⟪uₙ, x⟫ uₙ` is the orthogonal projection of `x` onto `(𝕜 ∙ uₙ)ᗮ`.
      have hnormle : ‖x - (inner 𝕜 (u n) x : 𝕜) • u n‖ ≤ ‖x‖ := by
        have hsub : x - (inner 𝕜 (u n) x : 𝕜) • u n = ((𝕜 ∙ u n)ᗮ).starProjection x := by
          rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton, hun n]
          simp
        rw [hsub]
        exact Submodule.norm_starProjection_apply_le _ x
      rw [hval]
      calc ‖A n (x - (inner 𝕜 (u n) x : 𝕜) • u n)‖
          ≤ ‖A n‖ * ‖x - (inner 𝕜 (u n) x : 𝕜) • u n‖ := (A n).le_opNorm _
        _ ≤ ‖A n‖ * ‖x‖ := mul_le_mul_of_nonneg_left hnormle (norm_nonneg _)
    -- Step 5: the null sequence.  `‖A n‖` decreases to `0`, by compactness.
    have hbdd : BddBelow (Set.range fun n => ‖A n‖) := ⟨0, by
      rintro r ⟨n, rfl⟩; exact norm_nonneg _⟩
    have hAtend : Filter.Tendsto (fun n => ‖A n‖) Filter.atTop (nhds (⨅ n, ‖A n‖)) :=
      tendsto_atTop_ciInf hAanti hbdd
    have hinf : (⨅ n, ‖A n‖) = 0 := by
      by_contra hne0
      have hge : ∀ n, (⨅ m, ‖A m‖) ≤ ‖A n‖ := fun n => ciInf_le hbdd n
      have hc0 : (0 : ℝ) ≤ ⨅ m, ‖A m‖ := le_ciInf fun n => norm_nonneg _
      set c := ⨅ m, ‖A m‖ with hcdef
      have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hne0)
      have hlamne : ∀ n, lam n ≠ 0 := by
        intro n h0
        have h1 := hge n
        rw [← hlamnorm n, h0, abs_zero] at h1
        linarith
      obtain ⟨φ, y, hφ, hy⟩ :=
        (isCompactOperator_iff_tendsto_subseq K).mp hc u 1 (fun n => le_of_eq (hun n))
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hy (c / 2) (by positivity)
      have h1 := hN N le_rfl
      have h2 := hN (N + 1) (Nat.le_succ N)
      rw [dist_eq_norm] at h1 h2
      have hlt : ‖K (u (φ N)) - K (u (φ (N + 1)))‖ < c := by
        have h3 := norm_sub_le_norm_sub_add_norm_sub (K (u (φ N))) y (K (u (φ (N + 1))))
        have h2' : ‖y - K (u (φ (N + 1)))‖ < c / 2 := by
          rw [← norm_neg]; simpa using h2
        linarith
      have hidx : φ N < φ (N + 1) := hφ (Nat.lt_succ_self N)
      have hsq : ‖K (u (φ N)) - K (u (φ (N + 1)))‖ ^ 2
          = lam (φ N) ^ 2 + lam (φ (N + 1)) ^ 2 := by
        rw [hKu _ (hlamne _), hKu _ (hlamne _), norm_sub_sq (𝕜 := 𝕜),
          inner_smul_left, inner_smul_right,
          horth (φ N) (φ (N + 1)) hidx (hlamne _), norm_smul, norm_smul,
          RCLike.norm_ofReal, RCLike.norm_ofReal, hun (φ N), hun (φ (N + 1))]
        simp [sq_abs]
      have e1 : c ≤ |lam (φ N)| := by rw [hlamnorm]; exact hge _
      have e2 : c ≤ |lam (φ (N + 1))| := by rw [hlamnorm]; exact hge _
      nlinarith [norm_nonneg (K (u (φ N)) - K (u (φ (N + 1)))), sq_abs (lam (φ N)),
        sq_abs (lam (φ (N + 1))), abs_nonneg (lam (φ N)), abs_nonneg (lam (φ (N + 1)))]
    have hAtend0 : Filter.Tendsto (fun n => ‖A n‖) Filter.atTop (nhds 0) := by
      rw [← hinf]; exact hAtend
    have hlamtend : Filter.Tendsto lam Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm (fun n => ?_) hAtend0
      simp [Real.norm_eq_abs, hlamnorm n]
    -- Step 6: the index set, an initial segment of `ℕ`.
    have hseg : ∀ m n : ℕ, lam n ≠ 0 → m ≤ n → lam m ≠ 0 := by
      intro m n hn hmn h0
      have h1 : ‖A n‖ ≤ ‖A m‖ := hAanti hmn
      rw [← hlamnorm m, ← hlamnorm n, h0, abs_zero] at h1
      exact hn (abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _)))
    have horthI : Orthonormal 𝕜 (fun i : ({n : ℕ | lam n ≠ 0} : Set ℕ) => u ↑i) := by
      refine ⟨fun i => hun _, fun {i j} hij => ?_⟩
      rcases lt_or_gt_of_ne (fun h : (i : ℕ) = (j : ℕ) => hij (Subtype.ext h)) with h | h
      · exact horth _ _ h j.2
      · rw [← inner_conj_symm (u ↑i) (u ↑j), horth _ _ h i.2, map_zero]
    have htendsum : ∀ x : H, Filter.Tendsto
        (fun n => ∑ k ∈ Finset.range n, ((lam k : 𝕜) * inner 𝕜 (u k) x) • u k)
        Filter.atTop (nhds (K x)) := by
      intro x
      have hgx : Filter.Tendsto (fun n => ‖A n‖ * ‖x‖) Filter.atTop (nhds 0) := by
        simpa using hAtend0.mul_const ‖x‖
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hgx
      have he : (∑ k ∈ Finset.range n, ((lam k : 𝕜) * inner 𝕜 (u k) x) • u k) - K x
          = -(A n x) := by rw [hAapply n x]; abel
      rw [he, norm_neg]
      exact (A n).le_opNorm x
    refine ⟨{n : ℕ | lam n ≠ 0}, fun i => lam ↑i, fun i => u ↑i, ?_, horthI, fun i => i.2,
      ?_, ?_, ?_, ?_⟩
    · intro m n hn hmn
      exact hseg m n hn hmn
    · intro i j hij
      simp only
      rw [hlamnorm, hlamnorm]
      exact hAanti hij
    · intro hinfI
      have huniv : ∀ n : ℕ, lam n ≠ 0 := by
        intro n
        by_contra h0
        have hsub : ({m : ℕ | lam m ≠ 0} : Set ℕ) ⊆ Set.Iio n := by
          intro m hm
          by_contra hmn
          exact (hseg n m hm (not_lt.mp hmn)) h0
        exact hinfI (Set.Finite.subset (Set.finite_Iio n) hsub)
      have : Nonempty ({n : ℕ | lam n ≠ 0} : Set ℕ) := ⟨⟨0, huniv 0⟩⟩
      have hval : Filter.Tendsto (fun i : ({n : ℕ | lam n ≠ 0} : Set ℕ) => (i : ℕ))
          Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_atTop.mpr fun b => ⟨⟨b, huniv b⟩, fun j hj => hj⟩
      exact hlamtend.comp hval
    · intro x
      obtain ⟨f, hfdef⟩ : ∃ f : ℕ → H, ∀ n, f n = ((lam n : 𝕜) * inner 𝕜 (u n) x) • u n :=
        ⟨_, fun _ => rfl⟩
      have hsupp : Function.support f ⊆ {n : ℕ | lam n ≠ 0} := by
        intro n hn
        change lam n ≠ 0
        intro h0
        exact hn (by rw [hfdef, h0]; simp)
      have hbess := horthI.inner_products_summable (x := x)
      have hsq : Summable fun i : ({n : ℕ | lam n ≠ 0} : Set ℕ) =>
          ‖((lam ↑i : 𝕜) * inner 𝕜 (u ↑i) x)‖ ^ 2 := by
        refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
          (hbess.mul_left (‖K‖ ^ 2))
        rw [norm_mul, mul_pow]
        have hle : ‖((lam ↑i : ℝ) : 𝕜)‖ ≤ ‖K‖ := by
          rw [RCLike.norm_ofReal, hlamnorm]
          have h3 : ‖A (i : ℕ)‖ ≤ ‖A 0‖ := hAanti (Nat.zero_le (i : ℕ))
          rwa [hA0] at h3
        have h2 : ‖((lam ↑i : ℝ) : 𝕜)‖ ^ 2 ≤ ‖K‖ ^ 2 := by
          nlinarith [norm_nonneg (((lam (i : ℕ) : ℝ)) : 𝕜), norm_nonneg K]
        exact mul_le_mul_of_nonneg_right h2 (by positivity)
      have hsummI : Summable fun i : ({n : ℕ | lam n ≠ 0} : Set ℕ) => f ↑i := by
        simp only [hfdef]
        exact (horthI.summable_iff_norm_sq_summable _).mpr hsq
      obtain ⟨S, hS⟩ := hsummI
      have hSN : HasSum f S := (hasSum_subtype_iff_of_support_subset hsupp).mp hS
      have hfinal : HasSum f (K x) := by
        refine (Summable.hasSum_iff_tendsto_nat ⟨S, hSN⟩).mpr ?_
        simpa only [hfdef] using htendsum x
      have hres := (hasSum_subtype_iff_of_support_subset hsupp).mpr hfinal
      simpa only [hfdef, Function.comp_def] using hres
    · apply le_antisymm
      · refine Submodule.topologicalClosure_mono ?_
        rw [Submodule.span_le]
        rintro y ⟨i, rfl⟩
        have hi : lam (i : ℕ) ≠ 0 := i.2
        have hi' : ((lam (i : ℕ) : ℝ) : 𝕜) ≠ 0 := by simpa using hi
        refine ⟨((lam ↑i : 𝕜))⁻¹ • u ↑i, ?_⟩
        change K (((lam ↑i : 𝕜))⁻¹ • u ↑i) = u ↑i
        rw [map_smul, hKu _ hi, smul_smul, inv_mul_cancel₀ hi', one_smul]
      · refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
        rintro y ⟨x, rfl⟩
        change (K x) ∈ _
        refine IsClosed.mem_of_tendsto (Submodule.isClosed_topologicalClosure _)
          (htendsum x) ?_
        filter_upwards with n
        refine Submodule.sum_mem _ fun k _ => ?_
        by_cases h0 : lam k = 0
        · simp [h0]
        · exact Submodule.smul_mem _ _
            (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨k, h0⟩, rfl⟩))
  obtain ⟨I, lam, u, hinit, hon, hne, hanti, htend, hsum, hspan⟩ := aux
  exact ⟨I, lam, u, hinit, hon, hne, hanti, htend, hsum, hspan,
    fun μ hμ => finite_and_finrank_eigenspace_eq_card hon htend hsum hμ⟩

end _thm_spectral_diagonal
