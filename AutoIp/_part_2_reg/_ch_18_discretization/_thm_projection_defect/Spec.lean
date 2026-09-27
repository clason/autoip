/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_08_svd._def_singular_system
import AutoIp._part_1_funcanal._ch_03_hilbert_spaces._lem_dim_count
import AutoIp._part_1_funcanal._ch_04_orthonormal_series._lem_riesz_fischer
import AutoIp._part_1_funcanal._ch_08_svd._lem_svd_companion

section _thm_projection_defect

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Projection defect of the dual subspaces: for `K` with an ordered singular system
`{(σₖ, vₖ, uₖ)}` with `rank K ≥ n + 1`, and a finite-dimensional `Yₙ ⊆ Y` with `dim Yₙ = n`,
`‖(Id - Pₙ) K*‖ ≥ σₙ₊₁`, where `Pₙ` is the orthogonal projection onto `Xₙ = K* Yₙ`, with
equality when `Yₙ = span{u₁, …, uₙ}`.

`K` is assumed to have an ordered singular system rather than to be compact. Indices start at
`0`, so `σₙ₊₁` is the singular value at index `n`, and the hypothesis that index `n` exists
stands for `rank K ≥ n + 1`. -/
public
theorem le_norm_id_sub_starProjection_comp_adjoint_and_eq_of_singularSpan (K : E →L[𝕜] F) {I : Set
  ℕ} {σ : I → ℝ} {v : I → E}
    {u : I → F} (hs : IsOrderedSingularSystem K σ v u) (Y : ℕ → Submodule 𝕜 F)
    (X : ℕ → Submodule 𝕜 E) [∀ n, (X n).HasOrthogonalProjection]
    {n : ℕ} (hX : X n = (Y n).map K.adjoint.toLinearMap)
    [FiniteDimensional 𝕜 (Y n)] (hfin : Module.finrank 𝕜 (Y n) = n)
    (hmem : n ∈ I) :
    σ ⟨n, hmem⟩ ≤ ‖(ContinuousLinearMap.id 𝕜 E - (X n).starProjection) ∘L
        K.adjoint‖ ∧
      (Y n = Submodule.span 𝕜 (u '' {i : I | (i : ℕ) < n}) →
        ‖(ContinuousLinearMap.id 𝕜 E - (X n).starProjection) ∘L
          K.adjoint‖ = σ ⟨n, hmem⟩) := by
  classical
  set A : E →L[𝕜] E := ContinuousLinearMap.id 𝕜 E - (X n).starProjection with hAdef
  have hAeq : A = ((X n)ᗮ).starProjection := by
    rw [hAdef]; exact (Submodule.starProjection_orthogonal (X n)).symm
  have hAle : ∀ x : E, ‖A x‖ ≤ ‖x‖ := by
    intro x; rw [hAeq]; exact Submodule.norm_starProjection_apply_le _ x
  have hAmem : ∀ x : E, A x ∈ (X n)ᗮ := by
    intro x; rw [hAeq]; exact ((X n)ᗮ).starProjection_apply_mem x
  have hAid : ∀ x : E, x ∈ (X n)ᗮ → A x = x := by
    intro x hx; rw [hAeq]; exact Submodule.starProjection_eq_self_iff.2 hx
  have hPsa : ContinuousLinearMap.adjoint ((X n).starProjection) = (X n).starProjection :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection (X n))
  have hAsa : ContinuousLinearMap.adjoint A = A := by
    rw [hAdef, map_sub, ContinuousLinearMap.adjoint_id, hPsa]
  have hnormeq : ‖A ∘L ContinuousLinearMap.adjoint K‖ = ‖K ∘L A‖ := by
    have hcomp : ContinuousLinearMap.adjoint (K ∘L A) = A ∘L ContinuousLinearMap.adjoint K := by
      rw [ContinuousLinearMap.adjoint_comp, hAsa]
    rw [← hcomp]
    exact LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint (K ∘L A)
  have hIle : ∀ m : ℕ, m ≤ n → m ∈ I := fun m hm => hs.isLowerSet hmem hm
  set idx : Fin (n + 1) → I := fun j => ⟨(j : ℕ), hIle j (Nat.lt_succ_iff.mp j.2)⟩ with hidx
  have hidxval : ∀ j : Fin (n + 1), ((idx j : I) : ℕ) = (j : ℕ) := fun _ => rfl
  have hidxinj : Function.Injective idx := by
    intro a b hab
    have h1 : (a : ℕ) = (b : ℕ) := congrArg Subtype.val hab
    exact Fin.val_inj.mp h1
  have hwon : Orthonormal 𝕜 (fun j => v (idx j)) := hs.orthonormal_left.comp idx hidxinj
  have huon : Orthonormal 𝕜 (fun j => u (idx j)) := hs.orthonormal_right.comp idx hidxinj
  set V : Submodule 𝕜 E := Submodule.span 𝕜 (Set.range fun j => v (idx j)) with hVdef
  have hVrank : Module.finrank 𝕜 V = n + 1 := by
    rw [hVdef, finrank_span_eq_card hwon.linearIndependent, Fintype.card_fin]
  have hVfd : FiniteDimensional 𝕜 V := by
    rw [hVdef]; exact FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)
  -- The `FiniteDimensional` instance on `Yₙ` is used here: without it, `finrank Yₙ = n` would
  -- also hold for an infinite-dimensional `Yₙ` with `n = 0`.
  have hXfd : FiniteDimensional 𝕜 (X n) := by rw [hX]; infer_instance
  have hXrank : Module.finrank 𝕜 (X n) ≤ n := by
    have h := Submodule.finrank_map_le (ContinuousLinearMap.adjoint K).toLinearMap (Y n)
    rw [hfin] at h
    rw [hX]
    exact h
  -- A dimension count: `dim V = n + 1 > n ≥ dim Xₙ`, so `P_{Xₙ}` is not injective on `V`.
  obtain ⟨xb, hxb0, hxbV, hxbperp⟩ :=
    Submodule.exists_ne_zero_mem_inf_orthogonal_of_rank_lt (U := X n) (V := V)
      (by rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank, hVrank]; exact_mod_cast (by omega))
  have hexp : ∀ x ∈ V, x = ∑ j, (inner 𝕜 (v (idx j)) x : 𝕜) • v (idx j) := by
    intro x hx
    rw [hVdef] at hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨k, rfl⟩ := hz
        simp [orthonormal_iff_ite.mp hwon]
    | zero => simp
    | add a b _ _ ha hb =>
        simp only [inner_add_right, add_smul, Finset.sum_add_distrib]
        rw [← ha, ← hb]
    | smul c a _ ha =>
        simp only [inner_smul_right, mul_smul, ← Finset.smul_sum]
        rw [← ha]
  have hpythE : ∀ c : Fin (n + 1) → 𝕜,
      ‖∑ j, c j • v (idx j)‖ ^ 2 = ∑ j, ‖c j‖ ^ 2 := by
    intro c
    rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), hwon.inner_sum c c Finset.univ, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [RCLike.conj_mul]; simp
  have hpythF : ∀ c : Fin (n + 1) → 𝕜,
      ‖∑ j, c j • u (idx j)‖ ^ 2 = ∑ j, ‖c j‖ ^ 2 := by
    intro c
    rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), huon.inner_sum c c Finset.univ, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [RCLike.conj_mul]; simp
  have hKV : ∀ x ∈ V, K x
      = ∑ j, ((RCLike.ofReal (σ (idx j)) : 𝕜) * inner 𝕜 (v (idx j)) x) • u (idx j) := by
    intro x hx
    conv_lhs => rw [hexp x hx]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.map_smul, hs.map_left (idx j), smul_smul, mul_comm]
  have hlow : ∀ x ∈ V, σ ⟨n, hmem⟩ * ‖x‖ ≤ ‖K x‖ := by
    intro x hx
    have h1 : ‖K x‖ ^ 2
        = ∑ j, ‖(RCLike.ofReal (σ (idx j)) : 𝕜) * inner 𝕜 (v (idx j)) x‖ ^ 2 := by
      rw [hKV x hx,
        hpythF (fun j => (RCLike.ofReal (σ (idx j)) : 𝕜) * inner 𝕜 (v (idx j)) x)]
    have h2 : ‖x‖ ^ 2 = ∑ j, ‖(inner 𝕜 (v (idx j)) x : 𝕜)‖ ^ 2 := by
      conv_lhs => rw [hexp x hx]
      rw [hpythE (fun j => (inner 𝕜 (v (idx j)) x : 𝕜))]
    have h3 : ∀ j : Fin (n + 1),
        σ ⟨n, hmem⟩ ^ 2 * ‖(inner 𝕜 (v (idx j)) x : 𝕜)‖ ^ 2
          ≤ ‖(RCLike.ofReal (σ (idx j)) : 𝕜) * inner 𝕜 (v (idx j)) x‖ ^ 2 := by
      intro j
      have hjle : ((idx j : I) : ℕ) ≤ ((⟨n, hmem⟩ : I) : ℕ) := by
        rw [hidxval]; exact Nat.lt_succ_iff.mp j.2
      have hge : σ ⟨n, hmem⟩ ≤ σ (idx j) := hs.antitone (Subtype.coe_le_coe.mp hjle)
      rw [norm_mul, mul_pow, RCLike.norm_ofReal, abs_of_pos (hs.pos (idx j))]
      have hsq : σ ⟨n, hmem⟩ ^ 2 ≤ σ (idx j) ^ 2 := by nlinarith [hs.pos ⟨n, hmem⟩]
      exact mul_le_mul_of_nonneg_right hsq (by positivity)
    have h4 : σ ⟨n, hmem⟩ ^ 2 * ‖x‖ ^ 2 ≤ ‖K x‖ ^ 2 := by
      rw [h1, h2, Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => h3 j
    refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
    rw [mul_pow]
    exact h4
  have hlower : σ ⟨n, hmem⟩ ≤ ‖K ∘L A‖ := by
    have hx0 : (0 : ℝ) < ‖xb‖ := norm_pos_iff.2 hxb0
    have h1 : ‖(K ∘L A) xb‖ ≤ ‖K ∘L A‖ * ‖xb‖ := (K ∘L A).le_opNorm xb
    have h2 : (K ∘L A) xb = K xb := by
      rw [ContinuousLinearMap.comp_apply, hAid xb hxbperp]
    rw [h2] at h1
    exact le_of_mul_le_mul_right (le_trans (hlow xb hxbV) h1) hx0
  refine ⟨by rw [hnormeq]; exact hlower, ?_⟩
  -- The equality case: `Yₙ = span{u₀,…,u_{n-1}}` makes `Xₙ = span{v₀,…,v_{n-1}}`.
  intro hYspan
  have hXspan : X n = Submodule.span 𝕜 (v '' {i : I | (i : ℕ) < n}) := by
    rw [hX, hYspan, Submodule.map_span]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro z ⟨t, ⟨i, hi, rfl⟩, rfl⟩
      simp only [ContinuousLinearMap.coe_coe, hs.map_right i, SetLike.mem_coe]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · rw [Submodule.span_le]
      rintro z ⟨i, hi, rfl⟩
      have hne : (RCLike.ofReal (σ i) : 𝕜) ≠ 0 := by
        simpa using (hs.pos i).ne'
      have hv : v i = (RCLike.ofReal (σ i) : 𝕜)⁻¹ • ContinuousLinearMap.adjoint K (u i) := by
        rw [hs.map_right i, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [SetLike.mem_coe, hv]
      exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨u i, ⟨i, hi, rfl⟩, by simp⟩)
  have hperpv : ∀ x : E, x ∈ (X n)ᗮ → ∀ i : I, (i : ℕ) < n → (inner 𝕜 (v i) x : 𝕜) = 0 := by
    intro x hx i hi
    rw [hXspan] at hx
    exact (Submodule.mem_orthogonal _ _).1 hx _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  -- On `Xₙᗮ` the singular expansion is supported in `{i ≥ n}`, so `‖Kx‖ ≤ σₙ‖x‖`.
  have hub : ∀ x : E, x ∈ (X n)ᗮ → ‖K x‖ ≤ σ ⟨n, hmem⟩ * ‖x‖ := by
    intro x hx
    have hbess : Summable (fun i : I => ‖(inner 𝕜 (v i) x : 𝕜)‖ ^ 2) :=
      Orthonormal.inner_products_summable x hs.orthonormal_left
    have hbessle : (∑' i : I, ‖(inner 𝕜 (v i) x : 𝕜)‖ ^ 2) ≤ ‖x‖ ^ 2 :=
      Orthonormal.tsum_inner_products_le x hs.orthonormal_left
    have hnorm : ‖K x‖ ^ 2 = ∑' i : I, ‖(RCLike.ofReal (σ i) : 𝕜) * inner 𝕜 (v i) x‖ ^ 2 :=
      hs.orthonormal_right.norm_sq_eq_tsum_norm_sq (hs.hasSum x)
    have hterm : ∀ i : I, ‖(RCLike.ofReal (σ i) : 𝕜) * inner 𝕜 (v i) x‖ ^ 2
        = σ i ^ 2 * ‖(inner 𝕜 (v i) x : 𝕜)‖ ^ 2 := by
      intro i
      rw [norm_mul, mul_pow, RCLike.norm_ofReal, abs_of_pos (hs.pos i)]
    have hle : ∀ i : I, σ i ^ 2 * ‖(inner 𝕜 (v i) x : 𝕜)‖ ^ 2
        ≤ σ ⟨n, hmem⟩ ^ 2 * ‖(inner 𝕜 (v i) x : 𝕜)‖ ^ 2 := by
      intro i
      by_cases hi : (i : ℕ) < n
      · rw [hperpv x hx i hi]; simp
      · have hge : σ i ≤ σ ⟨n, hmem⟩ :=
          hs.antitone (Subtype.coe_le_coe.mp (Nat.not_lt.mp hi))
        have h1 : σ i ^ 2 ≤ σ ⟨n, hmem⟩ ^ 2 := by nlinarith [hs.pos i]
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have hsummable : Summable (fun i : I => σ i ^ 2 * ‖(inner 𝕜 (v i) x : 𝕜)‖ ^ 2) :=
      Summable.of_nonneg_of_le (fun i => by positivity) hle (hbess.mul_left _)
    have hchain : ‖K x‖ ^ 2 ≤ σ ⟨n, hmem⟩ ^ 2 * ‖x‖ ^ 2 := by
      rw [hnorm]
      calc ∑' i : I, ‖(RCLike.ofReal (σ i) : 𝕜) * inner 𝕜 (v i) x‖ ^ 2
          = ∑' i : I, σ i ^ 2 * ‖(inner 𝕜 (v i) x : 𝕜)‖ ^ 2 := tsum_congr hterm
        _ ≤ ∑' i : I, σ ⟨n, hmem⟩ ^ 2 * ‖(inner 𝕜 (v i) x : 𝕜)‖ ^ 2 :=
            hsummable.tsum_le_tsum hle (hbess.mul_left _)
        _ = σ ⟨n, hmem⟩ ^ 2 * ∑' i : I, ‖(inner 𝕜 (v i) x : 𝕜)‖ ^ 2 := tsum_mul_left
        _ ≤ σ ⟨n, hmem⟩ ^ 2 * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_left hbessle (by positivity)
    refine le_of_pow_le_pow_left₀ two_ne_zero
      (mul_nonneg (hs.pos ⟨n, hmem⟩).le (norm_nonneg x)) ?_
    rw [mul_pow]
    exact hchain
  rw [hnormeq]
  refine le_antisymm ?_ hlower
  refine ContinuousLinearMap.opNorm_le_bound _ (hs.pos ⟨n, hmem⟩).le fun x => ?_
  calc ‖(K ∘L A) x‖ = ‖K (A x)‖ := rfl
    _ ≤ σ ⟨n, hmem⟩ * ‖A x‖ := hub (A x) (hAmem x)
    _ ≤ σ ⟨n, hmem⟩ * ‖x‖ := mul_le_mul_of_nonneg_left (hAle x) (hs.pos _).le

/-- The inequality `‖(Id - Pₙ) K*‖ ≥ σₙ₊₁` alone, with the hypotheses and the indexing of the
full statement. -/
public theorem le_norm_id_sub_starProjection_comp_adjoint (K : E →L[𝕜] F) {I : Set ℕ} {σ : I → ℝ}
    {v : I → E} {u : I → F} (hs : IsOrderedSingularSystem K σ v u) (Y : ℕ → Submodule 𝕜 F)
    (X : ℕ → Submodule 𝕜 E) [∀ n, (X n).HasOrthogonalProjection]
    {n : ℕ} (hX : X n = (Y n).map K.adjoint.toLinearMap)
    [FiniteDimensional 𝕜 (Y n)] (hfin : Module.finrank 𝕜 (Y n) = n) (hmem : n ∈ I) :
    σ ⟨n, hmem⟩ ≤ ‖(ContinuousLinearMap.id 𝕜 E - (X n).starProjection) ∘L
      K.adjoint‖ :=
  (le_norm_id_sub_starProjection_comp_adjoint_and_eq_of_singularSpan K hs Y X hX hfin hmem).1

/-- The equality case `‖(Id - Pₙ) K*‖ = σₙ₊₁` for `Yₙ = span{u₁, …, uₙ}` alone, with the
hypotheses and the indexing of the full statement. -/
public
theorem norm_id_sub_starProjection_comp_adjoint_eq_of_singularSpan (K : E →L[𝕜] F) {I : Set ℕ}
    {σ : I → ℝ} {v : I → E} {u : I → F} (hs : IsOrderedSingularSystem K σ v u)
    (Y : ℕ → Submodule 𝕜 F) (X : ℕ → Submodule 𝕜 E) [∀ n, (X n).HasOrthogonalProjection]
    {n : ℕ} (hX : X n = (Y n).map K.adjoint.toLinearMap)
    [FiniteDimensional 𝕜 (Y n)] (hfin : Module.finrank 𝕜 (Y n) = n) (hmem : n ∈ I)
    (hYspan : Y n = Submodule.span 𝕜 (u '' {i : I | (i : ℕ) < n})) :
    ‖(ContinuousLinearMap.id 𝕜 E - (X n).starProjection) ∘L
      K.adjoint‖ = σ ⟨n, hmem⟩ :=
  (le_norm_id_sub_starProjection_comp_adjoint_and_eq_of_singularSpan K hs Y X hX hfin hmem).2
    hYspan

end AutoIp

end _thm_projection_defect
