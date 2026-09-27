/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_frac_power.Spec
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_basic
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_bounded
public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_hom
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound
import AutoIp.Auxiliary.Rpow

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- The square root of a squared singular value is the singular value itself. -/
public theorem IsSingularSystem.rpow_sq_half (hs : IsSingularSystem K σ v u) (i : ι) :
    (σ i ^ 2) ^ ((1 : ℝ) / 2) = σ i := by
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (hs.pos i).le]

/-- `|K|^a = |K|^b` whenever `a = b`. -/
public theorem IsSingularSystem.absRpow_congr (hs : IsSingularSystem K σ v u) {a b : ℝ}
    (hab : a = b) (ha : 0 ≤ a) (hb : 0 ≤ b) : hs.absRpow a ha = hs.absRpow b hb := by
  subst hab
  rfl

/-- `|K| ∘ |K| = K*K`. -/
public theorem IsSingularSystem.absRpow_one_comp_absRpow_one (hs : IsSingularSystem K σ v u) :
    hs.absRpow 1 zero_le_one ∘L hs.absRpow 1 zero_le_one
      = K.adjoint ∘L K := by
  have hb : ∃ C, ∀ i, |(fun t : ℝ => t ^ ((1 : ℝ) / 2)) (σ i ^ 2)| ≤ C :=
    hs.exists_bound_rpow_sq (c := 1 / 2) (by norm_num)
  have hbs : ∃ C, ∀ i, |Real.sqrt (σ i ^ 2)| ≤ C :=
    hb.imp fun _ hC i => by simpa only [Real.sqrt_eq_rpow] using hC i
  rw [hs.absRpow_def 1 zero_le_one hb,
    hs.funCalc_congr' hb hbs (by simp [Real.sqrt_eq_rpow]) fun i => by simp [Real.sqrt_eq_rpow],
    hs.funCalc_sqrt_comp_funCalc_sqrt hbs]

/-- `‖|K|^ν‖ ≤ (‖K‖²)^(ν/2)` for `ν > 0`. -/
public theorem IsSingularSystem.norm_absRpow_le (hs : IsSingularSystem K σ v u) {ν : ℝ}
    (hν : 0 < ν) : ‖hs.absRpow ν hν.le‖ ≤ (‖K‖ ^ 2) ^ (ν / 2) := by
  have hb : ∃ C, ∀ i, |(fun t : ℝ => t ^ (ν / 2)) (σ i ^ 2)| ≤ C :=
    hs.exists_bound_rpow_sq (by positivity)
  rw [hs.absRpow_def ν hν.le hb]
  have h := hs.norm_funCalc_le (fun s : ℝ => s ^ (ν / 2)) ((‖K‖ ^ 2) ^ (ν / 2))
    (fun i => by
      rw [abs_of_nonneg (Real.rpow_nonneg (sq_nonneg _) _)]
      exact Real.rpow_le_rpow (sq_nonneg _) (hs.sq_mem_Icc i).2 (by positivity))
  have h0 : |(fun s : ℝ => s ^ (ν / 2)) (0 : ℝ)| = 0 := by
    simp only
    rw [Real.zero_rpow (by positivity : (0 : ℝ) < ν / 2).ne', abs_zero]
  rw [h0, max_eq_left (Real.rpow_nonneg (sq_nonneg _) _)] at h
  exact h

/-- The zeroth power is the identity. -/
public theorem IsSingularSystem.absRpow_zero (hs : IsSingularSystem K σ v u) :
    hs.absRpow 0 le_rfl = ContinuousLinearMap.id 𝕜 E := by
  have hbone : ∃ C, ∀ i, |(fun _ : ℝ => (1 : ℝ)) (σ i ^ 2)| ≤ C := ⟨1, fun _ => by norm_num⟩
  rw [hs.absRpow_def 0 le_rfl (hs.exists_bound_rpow_sq (by norm_num)),
    hs.funCalc_congr _ (ψ := fun _ : ℝ => (1 : ℝ)) hbone (fun t _ => by simp),
    hs.funCalc_one hbone]

/-- Fractional powers compose. -/
public theorem IsSingularSystem.absRpow_add (hs : IsSingularSystem K σ v u) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    hs.absRpow (a + b) (add_pos ha hb).le
      = hs.absRpow a ha.le ∘L hs.absRpow b hb.le := by
  have hbd : ∀ c : ℝ, 0 ≤ c → ∃ C, ∀ i, |(fun t : ℝ => t ^ (c / 2)) (σ i ^ 2)| ≤ C :=
    fun c hc => hs.exists_bound_rpow_sq (by linarith)
  rw [hs.absRpow_def (a + b) (add_pos ha hb).le (hbd _ (add_pos ha hb).le),
    hs.absRpow_def a ha.le (hbd a ha.le), hs.absRpow_def b hb.le (hbd b hb.le),
    ← hs.funCalc_mul' (hbd a ha.le) (hbd b hb.le)]
  refine hs.funCalc_congr' _ _ ?_ fun i => ?_
  · simp only [Pi.mul_apply]
    rw [Real.zero_rpow (by linarith : (0 : ℝ) < (a + b) / 2).ne',
      Real.zero_rpow (by linarith : (0 : ℝ) < a / 2).ne', zero_mul]
  · simp only [Pi.mul_apply]
    rw [show (a + b) / 2 = a / 2 + b / 2 by ring, Real.rpow_add (pow_pos (hs.pos i) 2)]

/-- `|K|^ν x = ∑ᵢ σᵢ^ν ⟨vᵢ, x⟩ vᵢ` for `ν > 0`. -/
public theorem IsSingularSystem.hasSum_absRpow (hs : IsSingularSystem K σ v u) {ν : ℝ} (hν : 0 < ν)
    (x : E) :
    HasSum (fun i => (((σ i ^ ν : ℝ) : 𝕜) * inner 𝕜 (v i) x) • v i)
      (hs.absRpow ν hν.le x) := by
  have hb := hs.exists_bound_rpow_sq (c := ν / 2) (by positivity)
  rw [hs.absRpow_def ν hν.le hb]
  have h := hs.hasSum_funCalc_sub_starProjection (φ := fun t : ℝ => t ^ (ν / 2)) hb x
  simp only [Real.zero_rpow (by positivity : (0 : ℝ) < ν / 2).ne', RCLike.ofReal_zero,
    zero_smul, sub_zero] at h
  refine h.congr_fun fun i => ?_
  rw [AutoIp.rpow_sq_div_two (hs.pos i).le ν]

/-- The singular vectors are eigenvectors of every fractional power. -/
public theorem IsSingularSystem.absRpow_apply_v (hs : IsSingularSystem K σ v u) {ν : ℝ} (hν : 0 ≤ ν)
    (i : ι) :
    hs.absRpow ν hν (v i) = ((σ i ^ ν : ℝ) : 𝕜) • v i := by
  have hb := hs.exists_bound_rpow_sq (c := ν / 2) (by linarith)
  rw [hs.absRpow_def ν hν hb, hs.funCalc_rpow_apply_v ν hb i]
