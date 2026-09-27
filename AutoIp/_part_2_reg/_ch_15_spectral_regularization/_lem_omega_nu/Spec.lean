/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_12_picard._def_source_set
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_filter
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_bounded
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_hom
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_approx_error_spectral
public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose

section _lem_omega_nu

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Approximation error under a source condition: with
`ω_ν(α) := sup_{λ ∈ (0,κ]} λ^{ν/2} |r_α(λ)|`, for `y ∈ Dom(K†)` and `x† = K†y ∈ X_{ν,ρ}`
with `ν, ρ > 0`, for all `α > 0`, `‖x_α − x†‖ ≤ ω_ν(α) ρ` and
`‖K x_α − K x†‖ ≤ ω_{ν+1}(α) ρ`.

It holds for every `K`, `K = 0` included. -/
public
theorem norm_spectralReg_sub_moorePenrose_le (hs : IsSingularSystem K σ v u) {φ : Set.Ioi (0 : ℝ)
    → ℝ → ℝ} {C : ℝ}
    (hφ : IsRegularizingFilter K φ C) {ν ρ : ℝ} {α : Set.Ioi (0 : ℝ)} (hν : 0 < ν) (hρ : 0 < ρ)
    {y : F} (hy : y ∈ mpDomain K) (hx : moorePenrose K ⟨y, hy⟩ ∈ sourceSet hs ν hν ρ hρ) :
    ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y - moorePenrose K ⟨y, hy⟩‖ ≤
        (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), lam ^ (ν / 2) * |1 - lam * φ α lam|) * ρ ∧
      ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y) - K (moorePenrose K ⟨y, hy⟩)‖ ≤
        (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
          lam ^ ((ν + 1) / 2) * |1 - lam * φ α lam|) * ρ := by
  have hC0 : (0 : ℝ) < C := hφ.const_pos
  have h1C : (0 : ℝ) ≤ 1 + C := by linarith
  have hκ0 : (0 : ℝ) ≤ ‖K‖ ^ 2 := by positivity
  have hr : ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |1 - t * φ α t| ≤ 1 + C := by
    intro t ht
    rcases ht.1.lt_or_eq with h0 | h0
    · have h := hφ.mul_abs_le α t ⟨h0, ht.2⟩
      have habs : |t * φ α t| ≤ C := by rw [abs_mul, abs_of_pos h0]; exact h
      rw [abs_le] at habs ⊢
      constructor <;> linarith [habs.1, habs.2]
    · rw [← h0]; simp; linarith
  have homega_nonneg : ∀ s : ℝ,
      (0 : ℝ) ≤ ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), lam ^ (s / 2) * |1 - lam * φ α lam| :=
    fun s => Real.iSup_nonneg fun lam => Real.iSup_nonneg fun h =>
      mul_nonneg (Real.rpow_nonneg h.1.le _) (abs_nonneg _)
  have homega_le : ∀ s : ℝ, 0 < s → ∀ i,
      (σ i ^ 2) ^ (s / 2) * |1 - σ i ^ 2 * φ α (σ i ^ 2)|
        ≤ ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), lam ^ (s / 2) * |1 - lam * φ α lam| := by
    intro s hs0 i
    have hbdd : BddAbove (Set.range (fun lam : ℝ =>
        ⨆ _ : lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), lam ^ (s / 2) * |1 - lam * φ α lam|)) := by
      refine ⟨(‖K‖ ^ 2) ^ (s / 2) * (1 + C), ?_⟩
      rintro _ ⟨lam, rfl⟩
      refine Real.iSup_le (fun h => ?_) (by positivity)
      exact mul_le_mul (Real.rpow_le_rpow h.1.le h.2 (by positivity))
        (hr lam ⟨h.1.le, h.2⟩) (abs_nonneg _) (Real.rpow_nonneg hκ0 _)
    have h1 := le_ciSup hbdd (σ i ^ 2)
    rwa [ciSup_pos (show σ i ^ 2 ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2) from
      ⟨pow_pos (hs.pos i) 2, (hs.sq_mem_Icc i).2⟩)] at h1
  rw [mem_sourceSet_iff] at hx
  obtain ⟨w, hw, hxw⟩ := hx
  have hwρ : ‖w‖ ≤ ρ := hw
  obtain ⟨h1, -⟩ := moorePenrose_sub_spectralReg_eq_funCalc (α := α) hs hφ hy
  have hbr : ∃ c, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2),
      |(fun lam => 1 - lam * φ α lam) t| ≤ c := ⟨1 + C, hr⟩
  have hbψ : ∃ c, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2),
      |(fun t : ℝ => t ^ (ν / 2)) t| ≤ c :=
    ⟨(‖K‖ ^ 2) ^ (ν / 2), fun t ht => by
      simp only
      rw [abs_of_nonneg (Real.rpow_nonneg ht.1 _)]
      exact Real.rpow_le_rpow ht.1 ht.2 (by positivity)⟩
  have hbrsq := hs.exists_bound_sq hbr
  have hbψsq := hs.exists_bound_sq hbψ
  set g : ℝ → ℝ := (fun lam => 1 - lam * φ α lam) * (fun t : ℝ => t ^ (ν / 2)) with hgdef
  have hbg : ∃ c, ∀ i, |g (σ i ^ 2)| ≤ c := exists_forall_abs_mul_sq_le hbrsq hbψsq
  have hkey : moorePenrose K ⟨y, hy⟩ - spectralReg hs φ (hφ.exists_bound_on_spectrum
      hs) α y = hs.funCalc g hbg w := by
    have h2 : hs.funCalc g hbg w
        = hs.funCalc (fun lam => 1 - lam * φ α lam) hbrsq
            (hs.funCalc (fun t : ℝ => t ^ (ν / 2)) hbψsq w) :=
      congrArg (fun T : E →L[𝕜] E => T w) (hs.funCalc_mul' hbrsq hbψsq)
    rw [hs.absRpow_def ν hν.le hbψsq] at hxw
    rw [h2, hxw]
    exact h1
  have hg0 : g 0 = 0 := by
    rw [hgdef]
    simp [Real.zero_rpow (by positivity : (0:ℝ) < ν / 2).ne']
  have hgval : ∀ i, |g (σ i ^ 2)| = (σ i ^ 2) ^ (ν / 2) * |1 - σ i ^ 2 * φ α (σ i ^ 2)| := by
    intro i
    rw [hgdef]
    simp only [Pi.mul_apply]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (sq_nonneg (σ i)) _)]
    ring
  have hsum := hs.hasSum_funCalc_sub_starProjection hbg w
  rw [hg0, RCLike.ofReal_zero, zero_smul, sub_zero] at hsum
  have hbessel : ∑' i, ‖(inner 𝕜 (v i) w : 𝕜)‖ ^ 2 ≤ ‖w‖ ^ 2 :=
    hs.orthonormal_left.tsum_inner_products_le w
  have hsummable : Summable (fun i => ‖(inner 𝕜 (v i) w : 𝕜)‖ ^ 2) :=
    hs.orthonormal_left.inner_products_summable (x := w)
  have hpart1 : ‖spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y - moorePenrose K ⟨y, hy⟩‖ ≤
      (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), lam ^ (ν / 2) * |1 - lam * φ α lam|) * ρ := by
    set ω := ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), lam ^ (ν / 2) * |1 - lam * φ α lam| with hωdef
    have hω0 : (0 : ℝ) ≤ ω := homega_nonneg ν
    have hn := hs.norm_funCalc_le g ω (fun i => by rw [hgval i]; exact homega_le ν hν i)
    rw [hg0, abs_zero, max_eq_left hω0] at hn
    rw [norm_sub_rev, hkey]
    calc ‖hs.funCalc g hbg w‖ ≤ ‖hs.funCalc g hbg‖ * ‖w‖ := (hs.funCalc g hbg).le_opNorm w
      _ ≤ ω * ρ := mul_le_mul hn hwρ (norm_nonneg w) hω0
  refine ⟨hpart1, ?_⟩
  set ω1 := ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2), lam ^ ((ν + 1) / 2) * |1 - lam * φ α lam|
    with hω1def
  have hω10 : (0 : ℝ) ≤ ω1 := homega_nonneg (ν + 1)
  have hKsum := hsum.mapL K
  simp only [ContinuousLinearMap.map_smul, hs.map_left, smul_smul] at hKsum
  have hsqrt : ∀ i, (σ i ^ 2) ^ (ν / 2) * σ i = (σ i ^ 2) ^ ((ν + 1) / 2) := by
    intro i
    have hp : (0 : ℝ) < σ i ^ 2 := pow_pos (hs.pos i) 2
    have h1 : (σ i ^ 2) ^ ((1 : ℝ) / 2) = σ i := hs.rpow_sq_half i
    calc (σ i ^ 2) ^ (ν / 2) * σ i
        = (σ i ^ 2) ^ (ν / 2) * (σ i ^ 2) ^ ((1 : ℝ) / 2) := by rw [h1]
      _ = (σ i ^ 2) ^ (ν / 2 + (1 : ℝ) / 2) := (Real.rpow_add hp _ _).symm
      _ = (σ i ^ 2) ^ ((ν + 1) / 2) := by congr 1; ring
  have hterm2 : ∀ i, ‖(RCLike.ofReal (g (σ i ^ 2)) : 𝕜) * inner 𝕜 (v i) w *
      (RCLike.ofReal (σ i) : 𝕜)‖ ^ 2 ≤ ω1 ^ 2 * ‖(inner 𝕜 (v i) w : 𝕜)‖ ^ 2 := by
    intro i
    rw [norm_mul, norm_mul, RCLike.norm_ofReal, RCLike.norm_ofReal, mul_pow, mul_pow]
    have hle : |g (σ i ^ 2)| * |σ i| ≤ ω1 := by
      rw [hgval i, abs_of_pos (hs.pos i), mul_right_comm, hsqrt i]
      exact homega_le (ν + 1) (by linarith) i
    have hnn : (0 : ℝ) ≤ |g (σ i ^ 2)| * |σ i| := by positivity
    have hsq : (|g (σ i ^ 2)| * |σ i|) ^ 2 ≤ ω1 ^ 2 := by nlinarith
    calc |g (σ i ^ 2)| ^ 2 * ‖(inner 𝕜 (v i) w : 𝕜)‖ ^ 2 * |σ i| ^ 2
        = (|g (σ i ^ 2)| * |σ i|) ^ 2 * ‖(inner 𝕜 (v i) w : 𝕜)‖ ^ 2 := by ring
      _ ≤ ω1 ^ 2 * ‖(inner 𝕜 (v i) w : 𝕜)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hs2' : Summable (fun i => ‖(RCLike.ofReal (g (σ i ^ 2)) : 𝕜) * inner 𝕜 (v i) w *
      (RCLike.ofReal (σ i) : 𝕜)‖ ^ 2) :=
    (hs.orthonormal_right.summable_iff_norm_sq_summable _).mp hKsum.summable
  have hnorm2 : ‖K (hs.funCalc g hbg w)‖ ^ 2 ≤ ω1 ^ 2 * ‖w‖ ^ 2 := by
    rw [hs.orthonormal_right.norm_sq_eq_tsum_norm_sq hKsum]
    calc ∑' i, ‖(RCLike.ofReal (g (σ i ^ 2)) : 𝕜) * inner 𝕜 (v i) w *
            (RCLike.ofReal (σ i) : 𝕜)‖ ^ 2
        ≤ ∑' i, ω1 ^ 2 * ‖(inner 𝕜 (v i) w : 𝕜)‖ ^ 2 :=
          Summable.tsum_le_tsum hterm2 hs2' (hsummable.mul_left _)
      _ = ω1 ^ 2 * ∑' i, ‖(inner 𝕜 (v i) w : 𝕜)‖ ^ 2 := hsummable.tsum_mul_left _
      _ ≤ ω1 ^ 2 * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_left hbessel (sq_nonneg _)
  have hfinal2 : ‖K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y) - K (moorePenrose K
      ⟨y, hy⟩)‖ ^ 2 ≤ (ω1 * ρ) ^ 2 := by
    have he : K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) α y) - K (moorePenrose K ⟨y, hy⟩)
        = -(K (hs.funCalc g hbg w)) := by
      rw [← hkey, map_sub]
      abel
    rw [he, norm_neg]
    have hwρ2 : ‖w‖ ^ 2 ≤ ρ ^ 2 := by nlinarith [norm_nonneg w]
    calc ‖K (hs.funCalc g hbg w)‖ ^ 2 ≤ ω1 ^ 2 * ‖w‖ ^ 2 := hnorm2
      _ ≤ ω1 ^ 2 * ρ ^ 2 := mul_le_mul_of_nonneg_left hwρ2 (sq_nonneg _)
      _ = (ω1 * ρ) ^ 2 := by ring
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hfinal2

end AutoIp

end _lem_omega_nu
