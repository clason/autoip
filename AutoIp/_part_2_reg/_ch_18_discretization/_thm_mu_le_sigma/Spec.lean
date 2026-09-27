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
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_adjoint
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_equations
import AutoIp._part_2_reg._ch_12_picard._lem_mp_singular_vector
import AutoIp._part_2_reg._ch_18_discretization._lem_discrete_opnorm

section _thm_mu_le_sigma

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Discrete singular values undercut the true ones: for `K` with an ordered singular system
`{(σₖ, vₖ, uₖ)}`, `n ≥ 1` and `Yₙ ⊆ Ker(K*)ᗮ` with `dim Yₙ = n`, the smallest singular value
`μₙ` of `Qₙ K` satisfies `μₙ ≤ σₙ`, with equality when `Yₙ = span{u₁, …, uₙ}`.

`K` is assumed to have an ordered singular system rather than to be compact, and `μₙ` is the
infimum of the singular values of a given ordered singular system of `Qₙ K`. Indices start at
`0`, so `σₙ` is the singular value at index `n - 1`; the hypothesis that it exists is there
because that term needs it. -/
public
theorem iInf_le_singularValue_and_eq_of_singularSpan (K : E →L[𝕜] F) {I : Set ℕ} {σ : I → ℝ} {v : I
  → E} {u : I → F}
    (hs : IsOrderedSingularSystem K σ v u) (Y : ℕ → Submodule 𝕜 F)
    [∀ n, (Y n).HasOrthogonalProjection]
    {n : ℕ} (hsub : Y n ≤ (K.adjoint.toLinearMap.ker)ᗮ)
    (hn : 0 < n) (hfin : Module.finrank 𝕜 (Y n) = n) (hmem : n - 1 ∈ I)
    {J : Set ℕ} {μ : J → ℝ} {a : J → E} {b : J → F}
    (hμ : IsOrderedSingularSystem ((Y n).starProjection ∘L K) μ a b) :
    (⨅ j, μ j) ≤ σ ⟨n - 1, hmem⟩ ∧
      (Y n = Submodule.span 𝕜 (u '' {i : I | (i : ℕ) < n}) →
        (⨅ j, μ j) = σ ⟨n - 1, hmem⟩) := by
  classical
  have hYfd : FiniteDimensional 𝕜 (Y n) :=
    FiniteDimensional.of_finrank_pos (by rw [hfin]; omega)
  have hranle : LinearMap.range ((Y n).starProjection ∘L K).toLinearMap ≤ Y n := by
    rintro z ⟨x, rfl⟩
    exact (Y n).starProjection_apply_mem _
  have hRfd : FiniteDimensional 𝕜
      (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap) :=
    Submodule.finiteDimensional_of_le hranle
  have hRclosed : IsClosed
      (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap : Set F) :=
    Submodule.closed_of_finiteDimensional _
  -- In fact `Ran(Kₙ) = Yₙ`: `K*` is injective on `Yₙ ⊆ Ker(K*)ᗮ`.
  have hraneq : LinearMap.range ((Y n).starProjection ∘L K).toLinearMap = Y n := by
    refine le_antisymm hranle ?_
    intro z hz
    have hproj := (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap)
      |>.starProjection_apply_mem z
    have hdiff : z - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection z
        ∈ (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap)ᗮ :=
      (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).sub_starProjection_mem_orthogonal z
    have hdiffY : z - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection z
        ∈ Y n := Submodule.sub_mem _ hz (hranle hproj)
    have hK0 : ContinuousLinearMap.adjoint K
        (z - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection z) = 0 := by
      have hall : ∀ x : E, (inner 𝕜 (ContinuousLinearMap.adjoint K
          (z - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection z))
            x : 𝕜) = 0 := by
        intro x
        rw [ContinuousLinearMap.adjoint_inner_left]
        have h1 : (Y n).starProjection
            (z - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection z)
            = z - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection z :=
          Submodule.starProjection_eq_self_iff.2 hdiffY
        have h2 : (inner 𝕜
            (z - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection z)
            (K x) : 𝕜)
            = inner 𝕜
              (z - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection z)
              (((Y n).starProjection ∘L K) x) := by
          conv_lhs => rw [← h1]
          rw [Submodule.inner_starProjection_left_eq_right]
          rfl
        rw [h2]
        exact (Submodule.mem_orthogonal' _ _).1 hdiff _ ⟨x, rfl⟩
      have := hall (ContinuousLinearMap.adjoint K
        (z - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection z))
      exact inner_self_eq_zero.1 this
    have hz0 : z - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection z
        = 0 := by
      have hmem1 : z - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection z
          ∈ LinearMap.ker (ContinuousLinearMap.adjoint K).toLinearMap := hK0
      have hmem2 : z - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection z
          ∈ (LinearMap.ker (ContinuousLinearMap.adjoint K).toLinearMap)ᗮ := hsub hdiffY
      have hmem3 : z - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection z
          ∈ LinearMap.ker (ContinuousLinearMap.adjoint K).toLinearMap
            ⊓ (LinearMap.ker (ContinuousLinearMap.adjoint K).toLinearMap)ᗮ := ⟨hmem1, hmem2⟩
      rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hmem3
    rw [sub_eq_zero] at hz0
    rw [hz0]
    exact hproj
  -- The discrete system is nonempty: otherwise `Kₙ = 0` and `Yₙ = ⊥`.
  have hJne : Nonempty J := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    have hK0 : ∀ x : E, ((Y n).starProjection ∘L K) x = 0 := by
      intro x
      have h := hμ.hasSum x
      have he : (fun j : J => ((RCLike.ofReal (μ j) : 𝕜) * inner 𝕜 (a j) x) • b j)
          = fun _ => 0 := funext fun j => isEmptyElim j
      rw [he] at h
      exact h.unique hasSum_zero
    have hbot : Y n = ⊥ := by
      rw [← hraneq, Submodule.eq_bot_iff]
      rintro z ⟨x, rfl⟩
      exact hK0 x
    rw [hbot] at hfin
    simp only [finrank_bot] at hfin
    omega
  have hopn : ‖moorePenroseL hRclosed‖ = (⨅ j, μ j)⁻¹ :=
    opNorm_moorePenroseL_eq_inv_iInf hRclosed hμ
  -- The discrete system is finite, so the infimum is attained and positive.
  have hJfin : J.Finite := by
    by_contra hinf
    have hinf' : J.Infinite := hinf
    obtain ⟨j₀, hj₀⟩ := hinf'.nonempty
    have htend := hμ.tendsto_zero hinf'
    have hlow : ∀ j : J, (μ j)⁻¹ ≤ ‖moorePenroseL hRclosed‖ := by
      intro j
      have h1 : ‖moorePenroseL hRclosed (b j)‖ = (μ j)⁻¹ := by
        rw [moorePenroseL_apply]
        exact norm_moorePenrose_apply_u hμ.toIsSingularSystem j
      have h2 := (moorePenroseL hRclosed).le_opNorm (b j)
      rwa [h1, hμ.orthonormal_right.1 j, mul_one] at h2
    have hNpos : 0 < ‖moorePenroseL hRclosed‖ :=
      lt_of_lt_of_le (inv_pos.2 (hμ.pos ⟨j₀, hj₀⟩)) (hlow ⟨j₀, hj₀⟩)
    have hge : ∀ j : J, ‖moorePenroseL hRclosed‖⁻¹ ≤ μ j := by
      intro j
      have h1 := hlow j
      have h2 := hμ.pos j
      have hkey : 1 ≤ μ j * ‖moorePenroseL hRclosed‖ := by
        have h3 := mul_le_mul_of_nonneg_left h1 h2.le
        rwa [mul_inv_cancel₀ (ne_of_gt h2)] at h3
      nlinarith [inv_pos.2 hNpos, mul_inv_cancel₀ (ne_of_gt hNpos)]
    have hev := htend.eventually_lt_const (inv_pos.2 hNpos)
    obtain ⟨j, hj⟩ := hev.exists
    exact absurd hj (not_lt.2 (hge j))
  have : Finite J := hJfin.to_subtype
  obtain ⟨j₀, hj₀⟩ := exists_eq_ciInf_of_finite (f := μ)
  have hmpos : 0 < ⨅ j, μ j := by rw [← hj₀]; exact hμ.pos j₀
  have hrangeadj : IsClosed (LinearMap.range
      (ContinuousLinearMap.adjoint ((Y n).starProjection ∘L K)).toLinearMap : Set E) := by
    have : FiniteDimensional 𝕜 (LinearMap.range
        (ContinuousLinearMap.adjoint ((Y n).starProjection ∘L K)).toLinearMap) := by
      refine Submodule.finiteDimensional_of_le
        (S₂ := Submodule.map (ContinuousLinearMap.adjoint K).toLinearMap (Y n)) ?_
      rintro z ⟨w, rfl⟩
      refine ⟨(Y n).starProjection w, (Y n).starProjection_apply_mem _, ?_⟩
      rw [ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection (Y n))]
      rfl
    exact Submodule.closed_of_finiteDimensional _
  have hYlow : ∀ z ∈ Y n, (⨅ j, μ j) * ‖z‖ ≤ ‖ContinuousLinearMap.adjoint K z‖ := by
    intro z hz
    have hQz : (Y n).starProjection z = z := Submodule.starProjection_eq_self_iff.2 hz
    have hKnz : ContinuousLinearMap.adjoint ((Y n).starProjection ∘L K) z
        = ContinuousLinearMap.adjoint K z := by
      rw [ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection (Y n))]
      simp only [ContinuousLinearMap.comp_apply, hQz]
    have hkerz : z ∈ (LinearMap.ker
        (ContinuousLinearMap.adjoint ((Y n).starProjection ∘L K)).toLinearMap)ᗮ := by
      have h1 : LinearMap.ker
          (ContinuousLinearMap.adjoint ((Y n).starProjection ∘L K)).toLinearMap = (Y n)ᗮ := by
        rw [← ((Y n).starProjection ∘L K).orthogonal_range, hraneq]
      rw [h1]
      exact Submodule.le_orthogonal_orthogonal _ hz
    have hzeq : moorePenrose (ContinuousLinearMap.adjoint ((Y n).starProjection ∘L
        K)) ⟨(ContinuousLinearMap.adjoint ((Y n).starProjection ∘L
            K) z), (Submodule.mem_sup_left ⟨z, rfl⟩)⟩ = z := by
      have h := moorePenrose_apply_apply
        (T := ContinuousLinearMap.adjoint ((Y n).starProjection ∘L K)) z
      rw [h]
      have h0 : (LinearMap.ker
          (ContinuousLinearMap.adjoint ((Y n).starProjection ∘L K)).toLinearMap).starProjection z
          = 0 := by
        exact (Submodule.starProjection_apply_eq_zero_iff _).mpr hkerz
      rw [h0, sub_zero]
    have hbound : ‖z‖ ≤ (⨅ j, μ j)⁻¹ * ‖ContinuousLinearMap.adjoint K z‖ := by
      have h1 : ContinuousLinearMap.adjoint (moorePenroseL hRclosed)
          (ContinuousLinearMap.adjoint ((Y n).starProjection ∘L K) z) = z := by
        rw [adjoint_moorePenroseL_apply hRclosed]
        exact hzeq
      have h2 : ‖ContinuousLinearMap.adjoint (moorePenroseL hRclosed)
          (ContinuousLinearMap.adjoint ((Y n).starProjection ∘L K) z)‖
          ≤ ‖ContinuousLinearMap.adjoint (moorePenroseL hRclosed)‖ *
            ‖ContinuousLinearMap.adjoint ((Y n).starProjection ∘L K) z‖ :=
        (ContinuousLinearMap.adjoint (moorePenroseL hRclosed)).le_opNorm _
      have h3 : ‖ContinuousLinearMap.adjoint (moorePenroseL hRclosed)‖
          = ‖moorePenroseL hRclosed‖ :=
        LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint (moorePenroseL hRclosed)
      rw [h3, hopn, h1, hKnz] at h2
      exact h2
    have hkey := mul_le_mul_of_nonneg_left hbound hmpos.le
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hmpos), one_mul] at hkey
    exact hkey
  have hIle : ∀ m : ℕ, m ≤ n - 1 → m ∈ I := fun m hm => hs.isLowerSet hmem hm
  set idxN : Fin n → I := fun j => ⟨(j : ℕ), hIle j (by have := j.2; omega)⟩ with hidxN
  have hidxNval : ∀ j : Fin n, ((idxN j : I) : ℕ) = (j : ℕ) := fun _ => rfl
  set idxM : Fin (n - 1) → I := fun j => ⟨(j : ℕ), hIle j (by have := j.2; omega)⟩ with hidxM
  have hidxNinj : Function.Injective idxN := by
    intro p q hpq
    have h1 : (p : ℕ) = (q : ℕ) := congrArg Subtype.val hpq
    exact Fin.val_inj.mp h1
  have hidxMinj : Function.Injective idxM := by
    intro p q hpq
    have h1 : (p : ℕ) = (q : ℕ) := congrArg Subtype.val hpq
    exact Fin.val_inj.mp h1
  have hexp : ∀ (m : ℕ) (idx : Fin m → I), Function.Injective idx →
      ∀ z ∈ Submodule.span 𝕜 (Set.range fun j => u (idx j)),
        z = ∑ j, (inner 𝕜 (u (idx j)) z : 𝕜) • u (idx j) := by
    intro m idx hinj z hz
    have hon : Orthonormal 𝕜 (fun j => u (idx j)) := hs.orthonormal_right.comp idx hinj
    induction hz using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨k, rfl⟩ := hw
        simp [orthonormal_iff_ite.mp hon]
    | zero => simp
    | add p q _ _ hp hq =>
        simp only [inner_add_right, add_smul, Finset.sum_add_distrib]
        rw [← hp, ← hq]
    | smul c p _ hp =>
        simp only [inner_smul_right, mul_smul, ← Finset.smul_sum]
        rw [← hp]
  have hpythF : ∀ (m : ℕ) (idx : Fin m → I), Function.Injective idx →
      ∀ c : Fin m → 𝕜, ‖∑ j, c j • u (idx j)‖ ^ 2 = ∑ j, ‖c j‖ ^ 2 := by
    intro m idx hinj c
    have hon : Orthonormal 𝕜 (fun j => u (idx j)) := hs.orthonormal_right.comp idx hinj
    rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), hon.inner_sum c c Finset.univ, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [RCLike.conj_mul]; simp
  have hpythE : ∀ (m : ℕ) (idx : Fin m → I), Function.Injective idx →
      ∀ c : Fin m → 𝕜, ‖∑ j, c j • v (idx j)‖ ^ 2 = ∑ j, ‖c j‖ ^ 2 := by
    intro m idx hinj c
    have hon : Orthonormal 𝕜 (fun j => v (idx j)) := hs.orthonormal_left.comp idx hinj
    rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), hon.inner_sum c c Finset.univ, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [RCLike.conj_mul]; simp
  have hspanlow : ∀ z ∈ Submodule.span 𝕜 (Set.range fun j : Fin n => u (idxN j)),
      σ ⟨n - 1, hmem⟩ * ‖z‖ ≤ ‖ContinuousLinearMap.adjoint K z‖ := by
    intro z hz
    have hKz : ContinuousLinearMap.adjoint K z
        = ∑ j : Fin n, ((RCLike.ofReal (σ (idxN j)) : 𝕜)
          * inner 𝕜 (u (idxN j)) z) • v (idxN j) := by
      conv_lhs => rw [hexp n idxN hidxNinj z hz]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ContinuousLinearMap.map_smul, hs.map_right (idxN j), smul_smul, mul_comm]
    have h1 : ‖ContinuousLinearMap.adjoint K z‖ ^ 2
        = ∑ j : Fin n, ‖(RCLike.ofReal (σ (idxN j)) : 𝕜)
            * inner 𝕜 (u (idxN j)) z‖ ^ 2 := by
      rw [hKz, hpythE n idxN hidxNinj
        (fun j => (RCLike.ofReal (σ (idxN j)) : 𝕜) * inner 𝕜 (u (idxN j)) z)]
    have h2 : ‖z‖ ^ 2 = ∑ j : Fin n, ‖(inner 𝕜 (u (idxN j)) z : 𝕜)‖ ^ 2 := by
      conv_lhs => rw [hexp n idxN hidxNinj z hz]
      rw [hpythF n idxN hidxNinj (fun j => (inner 𝕜 (u (idxN j)) z : 𝕜))]
    have h3 : ∀ j : Fin n,
        σ ⟨n - 1, hmem⟩ ^ 2 * ‖(inner 𝕜 (u (idxN j)) z : 𝕜)‖ ^ 2
          ≤ ‖(RCLike.ofReal (σ (idxN j)) : 𝕜) * inner 𝕜 (u (idxN j)) z‖ ^ 2 := by
      intro j
      have hnm : ((⟨n - 1, hmem⟩ : I) : ℕ) = n - 1 := rfl
      have hjle : ((idxN j : I) : ℕ) ≤ ((⟨n - 1, hmem⟩ : I) : ℕ) := by
        have hj := j.2
        rw [hidxNval, hnm]
        omega
      have hge : σ ⟨n - 1, hmem⟩ ≤ σ (idxN j) := hs.antitone (Subtype.coe_le_coe.mp hjle)
      rw [norm_mul, mul_pow, RCLike.norm_ofReal, abs_of_pos (hs.pos (idxN j))]
      have hsq : σ ⟨n - 1, hmem⟩ ^ 2 ≤ σ (idxN j) ^ 2 := by nlinarith [hs.pos ⟨n - 1, hmem⟩]
      exact mul_le_mul_of_nonneg_right hsq (by positivity)
    have h4 : σ ⟨n - 1, hmem⟩ ^ 2 * ‖z‖ ^ 2 ≤ ‖ContinuousLinearMap.adjoint K z‖ ^ 2 := by
      rw [h1, h2, Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => h3 j
    refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
    rw [mul_pow]
    exact h4
  have hub : ∀ z : F, (∀ i : I, (i : ℕ) < n - 1 → (inner 𝕜 (u i) z : 𝕜) = 0) →
      ‖ContinuousLinearMap.adjoint K z‖ ≤ σ ⟨n - 1, hmem⟩ * ‖z‖ := by
    intro z hz
    have hbess : Summable (fun i : I => ‖(inner 𝕜 (u i) z : 𝕜)‖ ^ 2) :=
      Orthonormal.inner_products_summable z hs.orthonormal_right
    have hbessle : (∑' i : I, ‖(inner 𝕜 (u i) z : 𝕜)‖ ^ 2) ≤ ‖z‖ ^ 2 :=
      Orthonormal.tsum_inner_products_le z hs.orthonormal_right
    have hnorm : ‖ContinuousLinearMap.adjoint K z‖ ^ 2
        = ∑' i : I, ‖(RCLike.ofReal (σ i) : 𝕜) * inner 𝕜 (u i) z‖ ^ 2 :=
      hs.orthonormal_left.norm_sq_eq_tsum_norm_sq (hs.hasSum_adjoint z)
    have hterm : ∀ i : I, ‖(RCLike.ofReal (σ i) : 𝕜) * inner 𝕜 (u i) z‖ ^ 2
        = σ i ^ 2 * ‖(inner 𝕜 (u i) z : 𝕜)‖ ^ 2 := by
      intro i
      rw [norm_mul, mul_pow, RCLike.norm_ofReal, abs_of_pos (hs.pos i)]
    have hle : ∀ i : I, σ i ^ 2 * ‖(inner 𝕜 (u i) z : 𝕜)‖ ^ 2
        ≤ σ ⟨n - 1, hmem⟩ ^ 2 * ‖(inner 𝕜 (u i) z : 𝕜)‖ ^ 2 := by
      intro i
      by_cases hi : (i : ℕ) < n - 1
      · rw [hz i hi]; simp
      · have hge : σ i ≤ σ ⟨n - 1, hmem⟩ :=
          hs.antitone (Subtype.coe_le_coe.mp (Nat.not_lt.mp hi))
        have h1 : σ i ^ 2 ≤ σ ⟨n - 1, hmem⟩ ^ 2 := by nlinarith [hs.pos i]
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have hsummable : Summable (fun i : I => σ i ^ 2 * ‖(inner 𝕜 (u i) z : 𝕜)‖ ^ 2) :=
      Summable.of_nonneg_of_le (fun i => by positivity) hle (hbess.mul_left _)
    have hchain : ‖ContinuousLinearMap.adjoint K z‖ ^ 2 ≤ σ ⟨n - 1, hmem⟩ ^ 2 * ‖z‖ ^ 2 := by
      rw [hnorm]
      calc ∑' i : I, ‖(RCLike.ofReal (σ i) : 𝕜) * inner 𝕜 (u i) z‖ ^ 2
          = ∑' i : I, σ i ^ 2 * ‖(inner 𝕜 (u i) z : 𝕜)‖ ^ 2 := tsum_congr hterm
        _ ≤ ∑' i : I, σ ⟨n - 1, hmem⟩ ^ 2 * ‖(inner 𝕜 (u i) z : 𝕜)‖ ^ 2 :=
            hsummable.tsum_le_tsum hle (hbess.mul_left _)
        _ = σ ⟨n - 1, hmem⟩ ^ 2 * ∑' i : I, ‖(inner 𝕜 (u i) z : 𝕜)‖ ^ 2 := tsum_mul_left
        _ ≤ σ ⟨n - 1, hmem⟩ ^ 2 * ‖z‖ ^ 2 := mul_le_mul_of_nonneg_left hbessle (by positivity)
    refine le_of_pow_le_pow_left₀ two_ne_zero
      (mul_nonneg (hs.pos ⟨n - 1, hmem⟩).le (norm_nonneg z)) ?_
    rw [mul_pow]
    exact hchain
  -- A dimension count, `dim Yₙ = n > n - 1 = dim U`, gives a nonzero vector of `Yₙ` orthogonal
  -- to `u₀, …, u_{n-2}`.
  set U : Submodule 𝕜 F := Submodule.span 𝕜 (Set.range fun j : Fin (n - 1) => u (idxM j))
    with hUdef
  have hUon : Orthonormal 𝕜 (fun j : Fin (n - 1) => u (idxM j)) :=
    hs.orthonormal_right.comp idxM hidxMinj
  have hUrank : Module.finrank 𝕜 U = n - 1 := by
    rw [hUdef, finrank_span_eq_card hUon.linearIndependent, Fintype.card_fin]
  have hUfd : FiniteDimensional 𝕜 U := by
    rw [hUdef]; exact FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)
  obtain ⟨zb, hzb0, hzbY, hzbperp⟩ :=
    Submodule.exists_ne_zero_mem_inf_orthogonal_of_rank_lt (U := U) (V := Y n)
      (by rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank]; exact_mod_cast (by omega))
  have hzbcoef : ∀ i : I, (i : ℕ) < n - 1 → (inner 𝕜 (u i) zb : 𝕜) = 0 := by
    intro i hi
    have hidxeq : idxM ⟨(i : ℕ), hi⟩ = i := Subtype.ext rfl
    rw [← hidxeq]
    exact (Submodule.mem_orthogonal _ _).1 hzbperp _
      (Submodule.subset_span ⟨⟨(i : ℕ), hi⟩, rfl⟩)
  have hzbnorm : 0 < ‖zb‖ := norm_pos_iff.2 hzb0
  have hfirst : (⨅ j, μ j) ≤ σ ⟨n - 1, hmem⟩ := by
    have h1 := hYlow zb hzbY
    have h2 := hub zb hzbcoef
    have h3 : (⨅ j, μ j) * ‖zb‖ ≤ σ ⟨n - 1, hmem⟩ * ‖zb‖ := le_trans h1 h2
    exact le_of_mul_le_mul_right (by linarith) hzbnorm
  refine ⟨hfirst, fun hYspan => ?_⟩
  have himg : (u '' {i : I | (i : ℕ) < n}) = Set.range (fun j : Fin n => u (idxN j)) := by
    ext w
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨⟨(i : ℕ), hi⟩, ?_⟩
      congr 1
    · rintro ⟨j, rfl⟩
      refine ⟨idxN j, ?_, rfl⟩
      simp only [Set.mem_ofPred_eq, hidxNval]
      exact j.2
  have hbmem : b j₀ ∈ Y n := by
    have h1 : b j₀ ∈ (Submodule.span 𝕜 (Set.range b)).topologicalClosure :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨j₀, rfl⟩)
    rw [hμ.span_right] at h1
    have h2 : (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).topologicalClosure
        ≤ Y n :=
      Submodule.topologicalClosure_minimal _ hranle (Submodule.closed_of_finiteDimensional (Y n))
    exact h2 h1
  have hbKadj : ‖ContinuousLinearMap.adjoint K (b j₀)‖ = ⨅ j, μ j := by
    have hQb : (Y n).starProjection (b j₀) = b j₀ :=
      Submodule.starProjection_eq_self_iff.2 hbmem
    have h1 : ContinuousLinearMap.adjoint ((Y n).starProjection ∘L K) (b j₀)
        = ContinuousLinearMap.adjoint K (b j₀) := by
      rw [ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection (Y n))]
      simp only [ContinuousLinearMap.comp_apply, hQb]
    rw [← h1, hμ.map_right j₀, norm_smul, RCLike.norm_ofReal,
      hμ.orthonormal_left.1 j₀, mul_one, abs_of_pos (hμ.pos j₀), hj₀]
  have hsecond : σ ⟨n - 1, hmem⟩ ≤ ⨅ j, μ j := by
    have hbspan : b j₀ ∈ Submodule.span 𝕜 (Set.range fun j : Fin n => u (idxN j)) := by
      rw [← himg, ← hYspan]
      exact hbmem
    have h1 := hspanlow (b j₀) hbspan
    rw [hbKadj, hμ.orthonormal_right.1 j₀, mul_one] at h1
    exact h1
  exact le_antisymm hfirst hsecond

/-- The inequality `μₙ ≤ σₙ` alone, with the hypotheses and the indexing of the full
statement. -/
public theorem iInf_le_singularValue (K : E →L[𝕜] F) {I : Set ℕ} {σ : I → ℝ} {v : I → E} {u : I → F}
    (hs : IsOrderedSingularSystem K σ v u) (Y : ℕ → Submodule 𝕜 F)
    [∀ n, (Y n).HasOrthogonalProjection]
    {n : ℕ} (hsub : Y n ≤ (K.adjoint.toLinearMap.ker)ᗮ)
    (hn : 0 < n) (hfin : Module.finrank 𝕜 (Y n) = n) (hmem : n - 1 ∈ I)
    {J : Set ℕ} {μ : J → ℝ} {a : J → E} {b : J → F}
    (hμ : IsOrderedSingularSystem ((Y n).starProjection ∘L K) μ a b) :
    (⨅ j, μ j) ≤ σ ⟨n - 1, hmem⟩ :=
  (iInf_le_singularValue_and_eq_of_singularSpan K hs Y hsub hn hfin hmem hμ).1

/-- The equality case `μₙ = σₙ` for `Yₙ = span{u₁, …, uₙ}` alone, with the hypotheses and
the indexing of the full statement. -/
public
theorem iInf_eq_singularValue_of_singularSpan (K : E →L[𝕜] F) {I : Set ℕ} {σ : I → ℝ} {v : I → E}
    {u : I → F} (hs : IsOrderedSingularSystem K σ v u) (Y : ℕ → Submodule 𝕜 F)
    [∀ n, (Y n).HasOrthogonalProjection]
    {n : ℕ} (hsub : Y n ≤ (K.adjoint.toLinearMap.ker)ᗮ)
    (hn : 0 < n) (hfin : Module.finrank 𝕜 (Y n) = n) (hmem : n - 1 ∈ I)
    {J : Set ℕ} {μ : J → ℝ} {a : J → E} {b : J → F}
    (hμ : IsOrderedSingularSystem ((Y n).starProjection ∘L K) μ a b)
    (hYspan : Y n = Submodule.span 𝕜 (u '' {i : I | (i : ℕ) < n})) :
    (⨅ j, μ j) = σ ⟨n - 1, hmem⟩ :=
  (iInf_le_singularValue_and_eq_of_singularSpan K hs Y hsub hn hfin hmem hμ).2 hYspan

end AutoIp

end _thm_mu_le_sigma
