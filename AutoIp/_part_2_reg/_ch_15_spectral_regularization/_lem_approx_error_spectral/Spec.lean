/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_frac_power
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_filter
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_basic
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_bounded
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_hom
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound
public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
import Mathlib.Topology.GDelta.MetrizableSpace

section _lem_approx_error_spectral

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable {K : E →L[𝕜] F}

/-- Spectral form of the approximation error, the error formula: for a regularizing filter,
`y ∈ Dom(K†)`, `x† = K†y` and `r_α(λ) = 1 − λ φ_α(λ)`,
`K†y − R_α y = r_α(K*K) x† = ∑_{n ∈ I} r_α(σ_n²) ⟨v_n, x†⟩ v_n`.

It holds for every `K`, `K = 0` included. -/
public
theorem moorePenrose_sub_spectralReg_eq_funCalc [CompleteSpace E] [CompleteSpace F]
    {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F} (hs : IsSingularSystem K σ v u)
    {φ : Set.Ioi (0 : ℝ) → ℝ → ℝ} {C : ℝ} (hφ : IsRegularizingFilter K φ C) {α : Set.Ioi (0 : ℝ)}
    {y : F} (hy : y ∈ mpDomain K) :
    moorePenrose K ⟨y, hy⟩ - spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y =
        hs.funCalc (fun lam => 1 - lam * φ α lam) (hφ.exists_bound_residual hs α)
          (moorePenrose K ⟨y, hy⟩) ∧
      HasSum
        (fun i => (((1 - σ i ^ 2 * φ α (σ i ^ 2) : ℝ) : 𝕜) *
            inner 𝕜 (v i) (moorePenrose K ⟨y, hy⟩)) • v i)
        (moorePenrose K ⟨y, hy⟩
          - spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y) := by
  set x := moorePenrose K ⟨y, hy⟩ with hxdef
  obtain ⟨h1, h2⟩ := isMinimumNorm_iff.mp (moorePenrose_isMinimumNorm ⟨_, hy⟩)
  have hKadj : ContinuousLinearMap.adjoint K (y - K x) = 0 := by
    rw [Submodule.mem_orthogonal] at h1
    set w := ContinuousLinearMap.adjoint K (y - K x) with hw
    have h0 : (inner 𝕜 (K w) (y - K x) : 𝕜) = 0 := h1 (K w) ⟨w, rfl⟩
    have h0' : (inner 𝕜 (y - K x) (K w) : 𝕜) = 0 := by
      rw [← inner_conj_symm, h0, map_zero]
    rw [← ContinuousLinearMap.adjoint_inner_left] at h0'
    exact inner_self_eq_zero.mp h0'
  have hnormal : ContinuousLinearMap.adjoint K (K x) = ContinuousLinearMap.adjoint K y := by
    rw [map_sub, sub_eq_zero] at hKadj
    exact hKadj.symm
  have hPker : K.toLinearMap.ker.starProjection x = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr h2
  obtain ⟨B, hB⟩ := hφ.bddOn α
  have hbφ : ∃ c, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |φ α t| ≤ c := ⟨B, hB⟩
  have hbd := hφ.exists_bound_on_spectrum hs
  have hbid : ∃ c, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |(id : ℝ → ℝ) t| ≤ c :=
    ⟨‖K‖ ^ 2, fun t ht => by simpa [abs_of_nonneg ht.1] using ht.2⟩
  have hbmul : ∃ c, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |(φ α * (id : ℝ → ℝ)) t| ≤ c := by
    obtain ⟨c1, hc1⟩ := hbφ
    obtain ⟨c2, hc2⟩ := hbid
    exact ⟨c1 * c2, fun t ht => by
      rw [Pi.mul_apply, abs_mul]
      exact mul_le_mul (hc1 t ht) (hc2 t ht) (abs_nonneg _)
        (le_trans (abs_nonneg _) (hc1 t ht))⟩
  have hbone : ∃ c, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |(fun _ => (1 : ℝ)) t| ≤ c :=
    ⟨1, fun t _ => by simp⟩
  have hbneg : ∃ c, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2),
      |((-1 : ℝ) • (φ α * (id : ℝ → ℝ)) : ℝ → ℝ) t| ≤ c := by
    obtain ⟨c, hc⟩ := hbmul
    exact ⟨c, fun t ht => by simpa using hc t ht⟩
  have hr : (fun lam => 1 - lam * φ α lam)
      = (fun _ => (1 : ℝ)) + (-1 : ℝ) • (φ α * (id : ℝ → ℝ)) := by
    funext lam
    simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, id_eq, smul_eq_mul]
    ring
  have hbonesq := hs.exists_bound_sq hbone
  have hbmulsq := hs.exists_bound_sq hbmul
  have hb2 := hφ.exists_bound_residual hs α
  have hop : hs.funCalc (fun lam => 1 - lam * φ α lam) hb2
      = ContinuousLinearMap.id 𝕜 E - hs.funCalc (φ α * (id : ℝ → ℝ)) hbmulsq := by
    rw [hs.funCalc_congr hb2
        (ψ := (fun _ => (1 : ℝ)) + (-1 : ℝ) • (φ α * (id : ℝ → ℝ)))
        (exists_forall_abs_add_sq_le hbonesq (exists_forall_abs_smul_sq_le (-1) hbmulsq))
        (fun t _ => by
          simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, id_eq, smul_eq_mul]
          ring),
      hs.funCalc_add' hbonesq (exists_forall_abs_smul_sq_le (-1) hbmulsq),
      hs.funCalc_smul' (-1) hbmulsq, hs.funCalc_one hbonesq,
      show ((RCLike.ofReal (-1 : ℝ)) : 𝕜) = -1 by simp, neg_smul, one_smul, ← sub_eq_add_neg]
  have hspec : spectralReg hs φ hbd α y
      = hs.funCalc (φ α * (id : ℝ → ℝ)) hbmulsq x := by
    have h := hs.funCalc_mul' (hs.exists_bound_sq hbφ) (hs.exists_bound_sq hbid)
    rw [hs.funCalc_id (hs.exists_bound_sq hbid)] at h
    have h' := congrArg (fun S : E →L[𝕜] E => S x) h
    simp only [ContinuousLinearMap.comp_apply] at h'
    rw [h', hnormal, spectralReg_eq hs φ hbd α, ContinuousLinearMap.comp_apply]
  have hpart1 : x - spectralReg hs φ hbd α y
      = hs.funCalc (fun lam => 1 - lam * φ α lam) hb2 x := by
    rw [hop, hspec]
    simp
  have hsum := hs.hasSum_funCalc_sub_starProjection (φ := fun lam => 1 - lam * φ α lam) hb2 x
  rw [hPker, smul_zero, sub_zero] at hsum
  refine ⟨hpart1, ?_⟩
  rw [hpart1]
  exact hsum

/-- Spectral form of the approximation error, the residual function: for a regularizing filter
and `r_α(λ) = 1 − λ φ_α(λ)`, `r_α(λ) → 0` as `α → 0` for each `λ ∈ (0, κ]`, and
`|r_α(λ)| ≤ 1 + C_φ` for all `α > 0` and `λ ∈ (0, κ]`.

It holds for every `K`, `K = 0` included. -/
public theorem IsRegularizingFilter.tendsto_one_sub_mul_and_abs_le {φ : Set.Ioi (0 : ℝ) → ℝ → ℝ}
    {C : ℝ} (hφ : IsRegularizingFilter K φ C) :
    (∀ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
        Tendsto (fun a => 1 - lam * φ a lam) atBot (𝓝 0)) ∧
      ∀ (a : Set.Ioi (0 : ℝ)), ∀ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
        |1 - lam * φ a lam| ≤ 1 + C := by
  refine ⟨fun lam hlam => ?_, fun a lam hlam => ?_⟩
  · have h := (hφ.tendsto_inv lam hlam).const_mul lam
    have h2 := (tendsto_const_nhds (x := (1 : ℝ))
      (f := (atBot : Filter (Set.Ioi (0 : ℝ))))).sub h
    rwa [mul_inv_cancel₀ hlam.1.ne', sub_self] at h2
  · have habs : |lam * φ a lam| ≤ C := by
      rw [abs_mul, abs_of_pos hlam.1]; exact hφ.mul_abs_le a lam hlam
    rw [abs_le] at habs ⊢
    constructor <;> linarith [habs.1, habs.2]

end AutoIp

end _lem_approx_error_spectral
