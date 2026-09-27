/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_08_svd._def_singular_system
public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose_bounded
public import AutoIp._part_2_reg._ch_18_discretization._def_dual_lsq_projection
public import AutoIp._part_2_reg._ch_18_discretization._lem_dual_lsq_range_closed
import AutoIp._part_1_funcanal._ch_06_compact_operators._lem_finrank_compact
import AutoIp._part_1_funcanal._ch_08_svd._thm_svd
import AutoIp._part_2_reg._ch_18_discretization._lem_discrete_opnorm
import AutoIp._part_2_reg._ch_18_discretization._thm_dual_lsq_rate
import AutoIp._part_2_reg._ch_18_discretization._thm_mu_le_sigma
import AutoIp._part_2_reg._ch_18_discretization._thm_projection_defect

section _cor_dual_lsq_best_rate

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Best rate for the dual least-squares projection, the rate: for `K` with an ordered singular
system `{(σₖ, vₖ, uₖ)}`, `y ∈ Dom(K†)`, `y^δ` with `‖y - y^δ‖ ≤ δ` and `x† = K* w`,
`‖x^δₙ - x†‖ ≤ ‖w‖ ‖(Id - Pₙ) K*‖ + δ / μₙ`, and for `Yₙ = span{u₁, …, uₙ}`,
`‖x^δₙ - x†‖ ≤ ‖w‖ σₙ₊₁ + δ / σₙ`. Here `n ≥ 1`, the subspaces `Y n` are nested with
`dim Yₙ = n`, `Yₙ ⊆ Ker(K*)ᗮ`, and `Pₙ` is the orthogonal projection onto `Xₙ = K* Yₙ`.

`K` is assumed to have an ordered singular system rather than to be compact. The smallest
singular value `μₙ` of `Kₙ` enters through the hypothesis `‖Kₙ†‖ = μₙ⁻¹` for `n > 0`. Indices
start at `0`, so `σₙ₊₁` and `σₙ` are the singular values at the indices `n` and `n - 1`. -/
public theorem dualLsq_norm_sub_le_of_singularSpan (K : E →L[𝕜] F) {I : Set ℕ} {σ : I → ℝ}
    {v : I → E} {u : I → F}
    (hs : IsOrderedSingularSystem K σ v u) (Y : ℕ → Submodule 𝕜 F)
    [∀ n, (Y n).HasOrthogonalProjection] (X : ℕ → Submodule 𝕜 E)
    [∀ n, (X n).HasOrthogonalProjection]
    (hmono : Monotone Y) (hfin : ∀ n, Module.finrank 𝕜 (Y n) = n)
    {μ : ℕ → ℝ}
    (hμ : ∀ n, 0 < n → ‖moorePenroseL (isClosed_range_dualLsq K Y hmono hfin n)‖ = (μ n)⁻¹)
    {y : F} (hy : y ∈ mpDomain K) {w : F}
    (hw : moorePenrose K ⟨y, hy⟩ = K.adjoint w)
    {δ : ℝ} {z : F} (hz : ‖y - z‖ ≤ δ) {n : ℕ}
    (hX : X n = (Y n).map K.adjoint.toLinearMap)
    (hsub : Y n ≤ (K.adjoint.toLinearMap.ker)ᗮ)
    (hn : 0 < n) :
    ‖dualLsqProjection K Y z (mem_mpDomain_dualLsq K Y hmono hfin z) n - moorePenrose K ⟨y, hy⟩‖ ≤
        ‖w‖ * ‖(ContinuousLinearMap.id 𝕜 E - (X n).starProjection) ∘L
          K.adjoint‖ + δ / μ n ∧
      (∀ (hmem : n ∈ I) (hmem' : n - 1 ∈ I),
        Y n = Submodule.span 𝕜 (u '' {i : I | (i : ℕ) < n}) →
          ‖dualLsqProjection K Y z (mem_mpDomain_dualLsq K Y hmono hfin z) n - moorePenrose K ⟨y,
              hy⟩‖ ≤
            ‖w‖ * σ ⟨n, hmem⟩ + δ / σ ⟨n - 1, hmem'⟩) := by
  classical
  have hclosed : ∀ n,
      IsClosed (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap : Set F) :=
    isClosed_range_dualLsq K Y hmono hfin
  -- The propagated data error, `‖Rₙ(y - z)‖ ≤ δ/μₙ`.
  have hdata : ‖dualLsqProjection K Y z (mem_mpDomain_dualLsq K Y hmono hfin
      z) n - dualLsqProjection K Y y (mem_mpDomain_dualLsq K Y hmono hfin y) n‖ ≤ δ / μ n := by
    have e1 : dualLsqProjection K Y z (mem_mpDomain_dualLsq K Y hmono hfin z) n
        = moorePenroseL (hclosed n) ((Y n).starProjection z) :=
      by rw [dualLsqProjection_def, moorePenroseL_apply]
    have e2 : dualLsqProjection K Y y (mem_mpDomain_dualLsq K Y hmono hfin y) n
        = moorePenroseL (hclosed n) ((Y n).starProjection y) :=
      by rw [dualLsqProjection_def, moorePenroseL_apply]
    have h1 : dualLsqProjection K Y z (mem_mpDomain_dualLsq K Y hmono hfin
        z) n - dualLsqProjection K Y y (mem_mpDomain_dualLsq K Y hmono hfin y) n
        = moorePenroseL (hclosed n) ((Y n).starProjection (z - y)) := by
      rw [e1, e2, ← map_sub, ← map_sub]
    have hQ : ‖(Y n).starProjection (z - y)‖ ≤ ‖z - y‖ :=
      Submodule.norm_starProjection_apply_le _ _
    have hzy : ‖z - y‖ ≤ δ := by rwa [norm_sub_rev]
    rw [h1]
    calc ‖moorePenroseL (hclosed n) ((Y n).starProjection (z - y))‖
        ≤ ‖moorePenroseL (hclosed n)‖ * ‖(Y n).starProjection (z - y)‖ :=
          (moorePenroseL (hclosed n)).le_opNorm _
      _ ≤ ‖moorePenroseL (hclosed n)‖ * δ :=
          mul_le_mul_of_nonneg_left (le_trans hQ hzy) (norm_nonneg _)
      _ = (μ n)⁻¹ * δ := by rw [hμ n hn]
      _ = δ / μ n := by rw [inv_mul_eq_div]
  -- The approximation error.
  have happrox : ‖dualLsqProjection K Y y (mem_mpDomain_dualLsq K Y hmono hfin
      y) n - moorePenrose K ⟨y, hy⟩‖
      ≤ ‖w‖ * ‖(ContinuousLinearMap.id 𝕜 E - (X n).starProjection) ∘L
        ContinuousLinearMap.adjoint K‖ :=
    norm_dualLsqProjection_sub_le K Y X n hX hsub hy (mem_mpDomain_dualLsq K Y hmono hfin y) hw
  have htri := norm_sub_le_norm_sub_add_norm_sub (dualLsqProjection K Y z (mem_mpDomain_dualLsq K
      Y hmono hfin z) n)
    (dualLsqProjection K Y y (mem_mpDomain_dualLsq K Y hmono hfin y) n) (moorePenrose K ⟨y, hy⟩)
  have hYfd : FiniteDimensional 𝕜 (Y n) :=
    FiniteDimensional.of_finrank_pos (by rw [hfin]; omega)
  -- `Kₙ` has finite-dimensional range, so it is compact and has an ordered singular system.
  have hranle : LinearMap.range ((Y n).starProjection ∘L K).toLinearMap ≤ Y n := by
    rintro t ⟨x, rfl⟩
    exact (Y n).starProjection_apply_mem _
  have hRfd : FiniteDimensional 𝕜
      (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap) :=
    Submodule.finiteDimensional_of_le hranle
  have hcompact : IsCompactOperator ((Y n).starProjection ∘L K) :=
    IsCompactOperator.of_finiteDimensional_range _ hRfd
  obtain ⟨J, μ', a', b', hsys, -⟩ := hcompact.exists_isOrderedSingularSystem
  have hopn : ‖moorePenroseL (hclosed n)‖ = (⨅ j, μ' j)⁻¹ :=
    opNorm_moorePenroseL_eq_inv_iInf (hclosed n) hsys
  refine ⟨by linarith, fun hmem hmem' hYspan => ?_⟩
  have hprojeq : ‖(ContinuousLinearMap.id 𝕜 E - (X n).starProjection) ∘L
      ContinuousLinearMap.adjoint K‖ = σ ⟨n, hmem⟩ :=
    norm_id_sub_starProjection_comp_adjoint_eq_of_singularSpan K hs Y X hX (hfin n) hmem hYspan
  have hraneq : LinearMap.range ((Y n).starProjection ∘L K).toLinearMap = Y n := by
    refine le_antisymm hranle ?_
    intro t ht
    have hproj := (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap)
      |>.starProjection_apply_mem t
    have hdiff : t - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection t
        ∈ (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap)ᗮ :=
      (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).sub_starProjection_mem_orthogonal t
    have hdiffY : t - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection t
        ∈ Y n := Submodule.sub_mem _ ht (hranle hproj)
    have hK0 : ContinuousLinearMap.adjoint K
        (t - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection t) = 0 := by
      have hall : ∀ x : E, (inner 𝕜 (ContinuousLinearMap.adjoint K
          (t - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection t))
            x : 𝕜) = 0 := by
        intro x
        rw [ContinuousLinearMap.adjoint_inner_left]
        have h1 : (Y n).starProjection
            (t - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection t)
            = t - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection t :=
          Submodule.starProjection_eq_self_iff.2 hdiffY
        have h2 : (inner 𝕜
            (t - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection t)
            (K x) : 𝕜)
            = inner 𝕜
              (t - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection t)
              (((Y n).starProjection ∘L K) x) := by
          conv_lhs => rw [← h1]
          rw [Submodule.inner_starProjection_left_eq_right]
          rfl
        rw [h2]
        exact (Submodule.mem_orthogonal' _ _).1 hdiff _ ⟨x, rfl⟩
      have := hall (ContinuousLinearMap.adjoint K
        (t - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection t))
      exact inner_self_eq_zero.1 this
    have ht0 : t - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection t
        = 0 := by
      have hmem1 : t - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection t
          ∈ LinearMap.ker (ContinuousLinearMap.adjoint K).toLinearMap := hK0
      have hmem2 : t - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection t
          ∈ (LinearMap.ker (ContinuousLinearMap.adjoint K).toLinearMap)ᗮ := hsub hdiffY
      have hmem3 : t - (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap).starProjection t
          ∈ LinearMap.ker (ContinuousLinearMap.adjoint K).toLinearMap
            ⊓ (LinearMap.ker (ContinuousLinearMap.adjoint K).toLinearMap)ᗮ := ⟨hmem1, hmem2⟩
      rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hmem3
    rw [sub_eq_zero] at ht0
    rw [ht0]
    exact hproj
  have heqmu : (⨅ j, μ' j) = σ ⟨n - 1, hmem'⟩ :=
    iInf_eq_singularValue_of_singularSpan K hs Y hsub hn (hfin n) hmem' hsys hYspan
  have hμn : μ n = σ ⟨n - 1, hmem'⟩ := by
    refine inv_inj.mp ?_
    rw [← hμ n hn, hopn, heqmu]
  rw [hprojeq] at happrox
  rw [hμn] at hdata
  linarith

/-- Best rate for the dual least-squares projection, the optimality: for `K` with an ordered
singular system `{(σₖ, vₖ, uₖ)}`, no admissible family improves either term of the rate:
`μₙ ≤ σₙ` and `‖(Id - Pₙ) K*‖ ≥ σₙ₊₁` always. Here `n ≥ 1`, the subspaces `Y n` are nested with
`dim Yₙ = n`, `Yₙ ⊆ Ker(K*)ᗮ`, and `Pₙ` is the orthogonal projection onto `Xₙ = K* Yₙ`.

`K` is assumed to have an ordered singular system rather than to be compact. The smallest
singular value `μₙ` of `Kₙ` enters through the hypothesis `‖Kₙ†‖ = μₙ⁻¹` for `n > 0`. Indices
start at `0`, so `σₙ₊₁` and `σₙ` are the singular values at the indices `n` and `n - 1`. -/
public theorem dualLsq_mu_le_and_le_norm_id_sub_starProjection (K : E →L[𝕜] F) {I : Set ℕ}
    {σ : I → ℝ} {v : I → E} {u : I → F}
    (hs : IsOrderedSingularSystem K σ v u) (Y : ℕ → Submodule 𝕜 F)
    [∀ n, (Y n).HasOrthogonalProjection] (X : ℕ → Submodule 𝕜 E)
    [∀ n, (X n).HasOrthogonalProjection]
    (hmono : Monotone Y) (hfin : ∀ n, Module.finrank 𝕜 (Y n) = n)
    {μ : ℕ → ℝ}
    (hμ : ∀ n, 0 < n → ‖moorePenroseL (isClosed_range_dualLsq K Y hmono hfin n)‖ = (μ n)⁻¹)
    {n : ℕ} (hX : X n = (Y n).map K.adjoint.toLinearMap)
    (hsub : Y n ≤ (K.adjoint.toLinearMap.ker)ᗮ)
    (hn : 0 < n) :
    (∀ hmem' : n - 1 ∈ I, μ n ≤ σ ⟨n - 1, hmem'⟩) ∧
      ∀ hmem : n ∈ I, σ ⟨n, hmem⟩ ≤
        ‖(ContinuousLinearMap.id 𝕜 E - (X n).starProjection) ∘L K.adjoint‖ := by
  have hclosed : ∀ n,
      IsClosed (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap : Set F) :=
    isClosed_range_dualLsq K Y hmono hfin
  have hYfd : FiniteDimensional 𝕜 (Y n) :=
    FiniteDimensional.of_finrank_pos (by rw [hfin]; omega)
  -- `Kₙ` has finite-dimensional range, so it is compact and has an ordered singular system.
  have hranle : LinearMap.range ((Y n).starProjection ∘L K).toLinearMap ≤ Y n := by
    rintro t ⟨x, rfl⟩
    exact (Y n).starProjection_apply_mem _
  have hRfd : FiniteDimensional 𝕜
      (LinearMap.range ((Y n).starProjection ∘L K).toLinearMap) :=
    Submodule.finiteDimensional_of_le hranle
  have hcompact : IsCompactOperator ((Y n).starProjection ∘L K) :=
    IsCompactOperator.of_finiteDimensional_range _ hRfd
  obtain ⟨J, μ', a', b', hsys, -⟩ := hcompact.exists_isOrderedSingularSystem
  have hopn : ‖moorePenroseL (hclosed n)‖ = (⨅ j, μ' j)⁻¹ :=
    opNorm_moorePenroseL_eq_inv_iInf (hclosed n) hsys
  have hμinf : μ n = ⨅ j, μ' j := inv_inj.mp (by rw [← hμ n hn, hopn])
  refine ⟨fun hmem' => ?_, fun hmem => ?_⟩
  · -- No admissible family improves the data term: `μₙ ≤ σₙ`.
    rw [hμinf]
    exact iInf_le_singularValue K hs Y hsub hn (hfin n) hmem' hsys
  · -- Nor the approximation term: `‖(Id - Pₙ) K*‖ ≥ σₙ₊₁`.
    exact le_norm_id_sub_starProjection_comp_adjoint K hs Y X hX (hfin n) hmem

end AutoIp

end _cor_dual_lsq_best_rate
