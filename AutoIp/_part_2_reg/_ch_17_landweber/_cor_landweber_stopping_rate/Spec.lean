/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_12_picard._def_source_set
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_standard_filters
public import AutoIp._part_2_reg._ch_17_landweber._def_landweber
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_bounded
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound
import AutoIp._part_2_reg._ch_11_moore_penrose._thm_mp_inverse
import AutoIp._part_2_reg._ch_12_picard._lem_source_in_kerperp
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_omega_nu
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_residual_constant
import AutoIp._part_2_reg._ch_17_landweber._thm_landweber_order_optimal
import AutoIp._part_2_reg._ch_17_landweber._thm_landweber_regularization
import Mathlib.Algebra.Order.Ring.Star

section _cor_landweber_stopping_rate

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- Faster stopping under a source condition: if `Ran(K)` is dense in `Y`, `ν > 0`, `ρ > 0`
and `τ > 1`, there is `C > 0` with `m(δ,y^δ) ≤ C δ^(-2/(ν+1))` for every `x† ∈ X_{ν,ρ}`,
`δ > 0` and `y^δ ∈ B_δ(K x†)`, where `m(δ,y^δ)` is the first index with
`‖K x^δ_m - y^δ‖ ≤ τ δ`.

`C` is also independent of `x†`, and the hypothesis `dim Ran(K) = ∞` of the prose is not
needed.

The step size `ω ∈ (0, κ⁻¹)` is stated as `0 < ω` and `ωκ < 1`, which is the same for `K ≠ 0` and,
unlike the interval, makes no use of `0⁻¹`. It holds for every `K`, `K = 0` included. -/
public theorem landweber_stopping_le_of_mem_sourceSet (hs : IsSingularSystem K σ v u) {ω : ℝ}
    (hω : 0 < ω ∧ ω * ‖K‖ ^ 2 < 1)
    (hdense : Dense (K.toLinearMap.range : Set F))
    {ν ρ τ : ℝ} (hν : 0 < ν) (hρ : 0 < ρ) (hτ : 1 < τ) :
    ∃ C > (0 : ℝ), ∀ x ∈ sourceSet hs ν hν ρ hρ, ∀ δ > (0 : ℝ), ∀ z : F, ‖z - K x‖ ≤ δ →
      ∀ m : ℕ, ‖K (landweber K ω z m) - z‖ ≤ τ * δ →
        (∀ k < m, τ * δ < ‖K (landweber K ω z k) - z‖) →
          (m : ℝ) ≤ C * δ ^ (-2 / (ν + 1)) := by
  obtain ⟨hω0, hωκ⟩ := hω
  have hbdL := landweberFilter_exists_bound_on_spectrum hs ⟨hω0, hωκ.le⟩
  by_cases hK : K = 0
  · -- `K = 0`: `Ran(K) = {0}` is dense, so `Y = {0}` and the iteration stops at `m = 0`
    refine ⟨1, one_pos, fun x _ δ hδ z _ m _ hm2 => ?_⟩
    have hz : z = 0 := by
      have h := hdense.closure_eq ▸ Set.mem_univ z
      simpa [hK] using h
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [hm0]; push_cast; positivity
    · have h := hm2 0 hmpos
      rw [hz, hK] at h
      simp at h
      nlinarith
  have hκ : (0 : ℝ) < ‖K‖ ^ 2 := by positivity
  have hτ1 : (0:ℝ) < τ - 1 := by linarith
  have hν1 : (0:ℝ) < ν + 1 := by linarith
  set p : ℝ := 2 / (ν + 1) with hpdef
  have hp0 : 0 < p := by positivity
  have hfilt : IsRegularizingFilter K (landweberFilter ω) 1 :=
    landweberFilter_isRegularizingFilter K ⟨hω0, hωκ.le⟩
  have hCr := iSup_abs_one_sub_mul_landweberFilter_eq_one hK ⟨hω0, hωκ⟩
  set Cq : ℝ := ((ν + 1) / (2 * ω)) ^ ((ν + 1) / 2) * Real.exp (-(ν + 1) / 2) with hCqdef
  have hCq0 : 0 < Cq := by rw [hCqdef]; positivity
  have hQ : ∀ α : Set.Ioi (0 : ℝ), (⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
      lam ^ ((ν + 1) / 2) * |1 - lam * landweberFilter ω α lam|) ≤
        Cq * (α : ℝ) ^ ((ν + 1) / 2) :=
    fun α => landweberFilter_iSup_rpow_mul_residual_le hω0 hωκ.le hν1
  have hresid : ∀ (y : F), ∀ α : Set.Ioi (0 : ℝ),
      ‖y - K (spectralReg hs (landweberFilter ω) hbdL α y)‖ ≤ ‖y‖ := by
    have h := (one_le_iSup_abs_one_sub_mul_and_norm_residual_le hs hK hfilt).2.2
    rw [hCr] at h
    intro y α
    simpa using h y α
  -- the constant, fixed before `δ` and `yᵟ`
  set Dk : ℝ := ‖K‖ * (‖K‖ ^ 2) ^ (ν / 2) with hDkdef
  have hDk0 : 0 < Dk := by
    rw [hDkdef]
    have hKn : (0:ℝ) < ‖K‖ := by nlinarith [norm_nonneg K]
    positivity
  set A : ℝ := (Cq * ρ / (τ - 1)) ^ p with hAdef
  set B : ℝ := (Dk * ρ / (τ - 1)) ^ p with hBdef
  have hA0 : 0 < A := Real.rpow_pos_of_pos (by positivity) _
  have hB0 : 0 < B := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨A + B, by linarith, ?_⟩
  intro x hx δ hδ z hzx m hm1 hm2
  have hnegp : δ ^ (-2 / (ν + 1)) = (δ ^ p)⁻¹ := by
    rw [hpdef, show (-2 : ℝ) / (ν + 1) = -(2 / (ν + 1)) by ring, Real.rpow_neg hδ.le]
  have hδp : 0 < δ ^ p := Real.rpow_pos_of_pos hδ _
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · rw [hm0]
    push_cast
    positivity
  have hzn : τ * δ < ‖z‖ := by
    have h := hm2 0 hmpos
    rwa [landweber_zero, map_zero, zero_sub, norm_neg] at h
  -- the noise level is bounded above by a constant free of `δ`
  have hKx : ‖K x‖ ≤ Dk * ρ := by
    obtain ⟨w, hw, hxw⟩ := (mem_sourceSet_iff _ _ _ _ _).1 hx
    have hwρ : ‖w‖ ≤ ρ := hw
    have hb : ∀ i, |(fun t : ℝ => t ^ (ν / 2)) (σ i ^ 2)| ≤ (‖K‖ ^ 2) ^ (ν / 2) := by
      intro i
      have h := hs.sq_mem_Icc i
      simp only
      rw [abs_of_nonneg (Real.rpow_nonneg h.1 _)]
      exact Real.rpow_le_rpow h.1 h.2 (by positivity)
    have hop : ‖hs.absRpow ν hν.le‖ ≤ (‖K‖ ^ 2) ^ (ν / 2) := by
      have h := hs.norm_funCalc_le (fun t : ℝ => t ^ (ν / 2)) ((‖K‖ ^ 2) ^ (ν / 2)) hb
      rw [hs.absRpow_def ν hν.le (hs.exists_bound_rpow_sq (by linarith))]
      rwa [show |(0:ℝ) ^ (ν / 2)| = 0 by rw [Real.zero_rpow (by positivity), abs_zero],
        max_eq_left (Real.rpow_nonneg (by positivity) _)] at h
    have hxn : ‖x‖ ≤ (‖K‖ ^ 2) ^ (ν / 2) * ρ := by
      rw [← hxw]
      calc ‖hs.absRpow ν hν.le w‖ ≤ ‖hs.absRpow ν hν.le‖ * ‖w‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (‖K‖ ^ 2) ^ (ν / 2) * ρ :=
            mul_le_mul hop hwρ (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)
    calc ‖K x‖ ≤ ‖K‖ * ‖x‖ := K.le_opNorm x
      _ ≤ ‖K‖ * ((‖K‖ ^ 2) ^ (ν / 2) * ρ) := mul_le_mul_of_nonneg_left hxn (norm_nonneg K)
      _ = Dk * ρ := by rw [hDkdef]; ring
  have hδD : δ ≤ Dk * ρ / (τ - 1) := by
    have h1 : τ * δ < ‖K x‖ + δ := by
      calc τ * δ < ‖z‖ := hzn
        _ ≤ ‖K x‖ + ‖z - K x‖ := by
            have h := norm_add_le (K x) (z - K x)
            rwa [show K x + (z - K x) = z by abel] at h
        _ ≤ ‖K x‖ + δ := by linarith
    rw [le_div_iff₀ hτ1]
    nlinarith [hKx]
  -- an explicit admissible index `M`, and `m ≤ M` by minimality
  set A0 : ℝ := Cq * ρ / ((τ - 1) * δ) with hA0def
  have hA00 : 0 < A0 := by rw [hA0def]; positivity
  set M : ℕ := max 1 ⌈A0 ^ p⌉₊ with hMdef
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMR : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM1
  have hMge : A0 ^ p ≤ (M : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast Nat.cast_le.mpr (le_max_right 1 ⌈A0 ^ p⌉₊)
  have hMle : (M : ℝ) ≤ A0 ^ p + 1 := by
    rcases le_or_gt (⌈A0 ^ p⌉₊ : ℝ) 1 with h | h
    · have hM : (M:ℝ) = 1 := by
        rw [hMdef]
        push_cast [Nat.cast_max]
        exact max_eq_left (by exact_mod_cast h)
      rw [hM]
      have : (0:ℝ) ≤ A0 ^ p := (Real.rpow_pos_of_pos hA00 p).le
      linarith
    · have hM : (M:ℝ) = (⌈A0 ^ p⌉₊ : ℝ) := by
        rw [hMdef]
        push_cast [Nat.cast_max]
        exact max_eq_right (by linarith)
      rw [hM]
      exact (Nat.ceil_lt_add_one (Real.rpow_pos_of_pos hA00 p).le).le
  obtain ⟨α, hαdef⟩ : ∃ α : Set.Ioi (0 : ℝ), (α : ℝ) = 1 / (M : ℝ) :=
    ⟨⟨_, Set.mem_Ioi.2 (by positivity)⟩, rfl⟩
  have hα : (0 : ℝ) < (α : ℝ) := α.2
  have hxperp : x ∈ (K.toLinearMap.ker)ᗮ := sourceSet_subset_orthogonal_ker hs hν hρ hx
  have hmp : moorePenrose K ⟨(K x), (Submodule.mem_sup_left ⟨x,
      rfl⟩)⟩ = x := moorePenrose_apply_apply_of_mem_orthogonal hxperp
  have hymem : (K x : F) ∈ mpDomain K := Submodule.mem_sup_left ⟨x, rfl⟩
  have hxsrc : moorePenrose K ⟨(K x), (Submodule.mem_sup_left ⟨x,
      rfl⟩)⟩ ∈ sourceSet hs ν hν ρ hρ := by rw [hmp]; exact hx
  obtain ⟨-, hom⟩ := norm_spectralReg_sub_moorePenrose_le (α := α) hs hfilt hν hρ hymem hxsrc
  rw [hmp] at hom
  have hom2 : ‖K (spectralReg hs (landweberFilter ω) hbdL α (K x)) - K x‖
      ≤ Cq * (α : ℝ) ^ ((ν + 1) / 2) * ρ :=
    hom.trans (mul_le_mul_of_nonneg_right (hQ α) hρ.le)
  have hstep : (α : ℝ) ^ ((ν + 1) / 2) ≤ A0⁻¹ := by
    have h1 : A0 ≤ (M:ℝ) ^ ((ν + 1) / 2) := by
      have h2 := Real.rpow_le_rpow (Real.rpow_pos_of_pos hA00 p).le hMge
        (show (0:ℝ) ≤ (ν + 1) / 2 by positivity)
      rwa [← Real.rpow_mul hA00.le,
        show p * ((ν + 1) / 2) = 1 by rw [hpdef]; field_simp, Real.rpow_one] at h2
    rw [hαdef, one_div, ← Real.rpow_neg_one (M:ℝ), ← Real.rpow_mul hMR.le,
      show (-1 : ℝ) * ((ν + 1) / 2) = -((ν + 1) / 2) by ring, Real.rpow_neg hMR.le]
    exact inv_anti₀ hA00 h1
  have hbig : Cq * (α : ℝ) ^ ((ν + 1) / 2) * ρ ≤ (τ - 1) * δ := by
    have h1 : Cq * (α : ℝ) ^ ((ν + 1) / 2) * ρ ≤ Cq * A0⁻¹ * ρ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hCq0.le) hρ.le
    refine h1.trans (le_of_eq ?_)
    rw [hA0def]
    field_simp
  have hres1 : ‖(z - K x) - K (spectralReg hs (landweberFilter ω) hbdL α (z - K x))‖ ≤ δ :=
    (hresid (z - K x) α).trans hzx
  have hsplit : ‖K (spectralReg hs (landweberFilter ω) hbdL α z) - z‖ ≤ τ * δ := by
    have he : K (spectralReg hs (landweberFilter ω) hbdL α z) - z
        = (K (spectralReg hs (landweberFilter ω) hbdL α (K x)) - K x)
          - ((z - K x) - K (spectralReg hs (landweberFilter ω) hbdL α (z - K x))) := by
      have hlin : spectralReg hs (landweberFilter ω) hbdL α z
          = spectralReg hs (landweberFilter ω) hbdL α (K x)
            + spectralReg hs (landweberFilter ω) hbdL α (z - K x) := by
        rw [← map_add]; congr 1; abel
      rw [hlin, map_add]; abel
    rw [he]
    refine (norm_sub_le _ _).trans ?_
    have h := hom2.trans hbig
    linarith
  have hiter : landweber K ω z M = spectralReg hs (landweberFilter ω) hbdL α z :=
    landweber_eq_spectralReg hs ⟨hω0, hωκ.le⟩ z hM1 hαdef
  have hmM : m ≤ M := by
    by_contra hc
    push Not at hc
    have h := hm2 M hc
    rw [hiter] at h
    linarith
  have hcast : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM
  have hA0p : A0 ^ p = A * (δ ^ p)⁻¹ := by
    rw [hA0def, hAdef,
      show Cq * ρ / ((τ - 1) * δ) = (Cq * ρ / (τ - 1)) * δ⁻¹ by field_simp,
      Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hδ.le]
  have hone : (1:ℝ) ≤ B * (δ ^ p)⁻¹ := by
    have h1 : δ ^ p ≤ B := by
      rw [hBdef]
      exact Real.rpow_le_rpow hδ.le hδD hp0.le
    rw [le_mul_inv_iff₀ hδp]
    linarith
  rw [hnegp]
  calc (m:ℝ) ≤ (M:ℝ) := hcast
    _ ≤ A0 ^ p + 1 := hMle
    _ = A * (δ ^ p)⁻¹ + 1 := by rw [hA0p]
    _ ≤ A * (δ ^ p)⁻¹ + B * (δ ^ p)⁻¹ := by linarith
    _ = (A + B) * (δ ^ p)⁻¹ := by ring

end AutoIp

end _cor_landweber_stopping_rate
