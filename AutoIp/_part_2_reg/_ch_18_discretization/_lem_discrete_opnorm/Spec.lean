/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_08_svd._def_singular_system
public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose_bounded
import AutoIp._part_1_funcanal._ch_04_orthonormal_series._lem_riesz_fischer
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_domain_dense
import AutoIp._part_2_reg._ch_12_picard._cor_picard_domain
import AutoIp._part_2_reg._ch_12_picard._lem_mp_singular_vector

section _lem_discrete_opnorm

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Norm of the discrete pseudo-inverse: if `μ` are the singular values of an ordered
singular system of `S`, then `‖S†‖ = (inf_j μ_j)⁻¹`, which for singular values
`μ₁ ≥ ⋯ ≥ μₙ > 0` is `μₙ⁻¹`.

The blueprint states this for the rank-`n` operator `Tₙ = Qₙ T`; the Lean states it for any
`S` with closed range and an ordered singular system. The closed range is a binder because
the bounded `S†` needs it. -/
public theorem opNorm_moorePenroseL_eq_inv_iInf {S : E →L[𝕜] F}
    (hclosed : IsClosed (S.toLinearMap.range : Set F))
    {J : Set ℕ} {μ : J → ℝ} {a : J → E} {b : J → F}
    (hμ : IsOrderedSingularSystem S μ a b) :
    ‖moorePenroseL hclosed‖ = (⨅ j, μ j)⁻¹ := by
  classical
  have hdom : ∀ z : F, z ∈ mpDomain S := fun z => by
    rw [mpDomain_eq_top_iff.2 hclosed]; trivial
  have hlow : ∀ j : J, (μ j)⁻¹ ≤ ‖moorePenroseL hclosed‖ := by
    intro j
    have h1 : ‖moorePenroseL hclosed (b j)‖ = (μ j)⁻¹ := by
      rw [moorePenroseL_apply]
      exact norm_moorePenrose_apply_u hμ.toIsSingularSystem j
    have h2 := (moorePenroseL hclosed).le_opNorm (b j)
    rwa [h1, hμ.orthonormal_right.1 j, mul_one] at h2
  -- The singular system is finite: an infinite one would make `S†` unbounded.
  have hJfin : J.Finite := by
    by_contra hinf
    have hinf' : J.Infinite := hinf
    obtain ⟨j₀, hj₀⟩ := hinf'.nonempty
    have : Nonempty J := ⟨⟨j₀, hj₀⟩⟩
    have htend := hμ.tendsto_zero hinf'
    have hNpos : 0 < ‖moorePenroseL hclosed‖ :=
      lt_of_lt_of_le (inv_pos.2 (hμ.pos ⟨j₀, hj₀⟩)) (hlow ⟨j₀, hj₀⟩)
    have hge : ∀ j : J, ‖moorePenroseL hclosed‖⁻¹ ≤ μ j := by
      intro j
      have h1 := hlow j
      have h2 := hμ.pos j
      have hkey : 1 ≤ μ j * ‖moorePenroseL hclosed‖ := by
        have h3 := mul_le_mul_of_nonneg_left h1 h2.le
        rwa [mul_inv_cancel₀ (ne_of_gt h2)] at h3
      nlinarith [inv_pos.2 hNpos, mul_inv_cancel₀ (ne_of_gt hNpos)]
    have hev := htend.eventually_lt_const (inv_pos.2 hNpos)
    obtain ⟨j, hj⟩ := hev.exists
    exact absurd hj (not_lt.2 (hge j))
  have : Finite J := hJfin.to_subtype
  rcases isEmpty_or_nonempty J with hJe | hJn
  · -- No singular values: `S† = 0` and both sides are `0`.
    have hzero : moorePenroseL hclosed = 0 := by
      ext z
      have hz := hasSum_moorePenrose hμ.toIsSingularSystem (hdom z)
      have he : (fun j : J => ((RCLike.ofReal (μ j)⁻¹ : 𝕜) * inner 𝕜 (b j) z) • a j)
          = fun _ => 0 := funext fun j => isEmptyElim j
      rw [he] at hz
      have hz0 := hz.unique hasSum_zero
      simp [moorePenroseL_apply, hz0]
    rw [hzero, norm_zero, Real.iInf_of_isEmpty, inv_zero]
  · obtain ⟨j₀, hj₀⟩ := exists_eq_ciInf_of_finite (f := μ)
    have hmpos : 0 < ⨅ j, μ j := by rw [← hj₀]; exact hμ.pos j₀
    have hmle : ∀ j : J, (⨅ j, μ j) ≤ μ j := fun j =>
      ciInf_le (Set.Finite.bddBelow (Set.finite_range _)) j
    refine le_antisymm ?_ (by rw [← hj₀]; exact hlow j₀)
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
    have hz := hasSum_moorePenrose hμ.toIsSingularSystem (hdom z)
    have hnorm : ‖moorePenrose S ⟨z, (hdom z)⟩‖ ^ 2
        = ∑' j : J, ‖(RCLike.ofReal (μ j)⁻¹ : 𝕜) * inner 𝕜 (b j) z‖ ^ 2 :=
      hμ.orthonormal_left.norm_sq_eq_tsum_norm_sq hz
    have hterm : ∀ j : J, ‖(RCLike.ofReal (μ j)⁻¹ : 𝕜) * inner 𝕜 (b j) z‖ ^ 2
        = (μ j)⁻¹ ^ 2 * ‖(inner 𝕜 (b j) z : 𝕜)‖ ^ 2 := by
      intro j
      rw [norm_mul, mul_pow, RCLike.norm_ofReal,
        abs_of_pos (inv_pos.2 (hμ.pos j))]
    have hle : ∀ j : J, (μ j)⁻¹ ^ 2 * ‖(inner 𝕜 (b j) z : 𝕜)‖ ^ 2
        ≤ ((⨅ j, μ j)⁻¹) ^ 2 * ‖(inner 𝕜 (b j) z : 𝕜)‖ ^ 2 := by
      intro j
      have h1 : (μ j)⁻¹ ≤ (⨅ j, μ j)⁻¹ := by
        have := one_div_le_one_div_of_le hmpos (hmle j)
        simpa [one_div] using this
      have h2 : (μ j)⁻¹ ^ 2 ≤ ((⨅ j, μ j)⁻¹) ^ 2 := by
        have h3 : (0:ℝ) ≤ (μ j)⁻¹ := le_of_lt (inv_pos.2 (hμ.pos j))
        nlinarith
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    have hbess : ∑' j : J, ‖(inner 𝕜 (b j) z : 𝕜)‖ ^ 2 ≤ ‖z‖ ^ 2 :=
      Orthonormal.tsum_inner_products_le z hμ.orthonormal_right
    have hchain : ‖moorePenrose S ⟨z, (hdom z)⟩‖ ^ 2
        ≤ ((⨅ j, μ j)⁻¹) ^ 2 * ‖z‖ ^ 2 := by
      rw [hnorm]
      calc ∑' j : J, ‖(RCLike.ofReal (μ j)⁻¹ : 𝕜) * inner 𝕜 (b j) z‖ ^ 2
          = ∑' j : J, (μ j)⁻¹ ^ 2 * ‖(inner 𝕜 (b j) z : 𝕜)‖ ^ 2 := tsum_congr hterm
        _ ≤ ∑' j : J, ((⨅ j, μ j)⁻¹) ^ 2 * ‖(inner 𝕜 (b j) z : 𝕜)‖ ^ 2 :=
            Summable.tsum_le_tsum hle Summable.of_finite Summable.of_finite
        _ = ((⨅ j, μ j)⁻¹) ^ 2 * ∑' j : J, ‖(inner 𝕜 (b j) z : 𝕜)‖ ^ 2 := tsum_mul_left
        _ ≤ ((⨅ j, μ j)⁻¹) ^ 2 * ‖z‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hbess (by positivity)
    rw [moorePenroseL_apply]
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    rw [mul_pow]
    exact hchain

end AutoIp

end _lem_discrete_opnorm
