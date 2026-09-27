/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_hom.Spec
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_basic
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound
import AutoIp.Auxiliary.BoundedOnIcc

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- `0(K*K) = 0`. -/
public theorem IsSingularSystem.funCalc_zero (hs : IsSingularSystem K σ v u)
    (hb : ∃ C, ∀ i, |(0 : ℝ → ℝ) (σ i ^ 2)| ≤ C) :
    hs.funCalc (0 : ℝ → ℝ) hb = 0 := by
  ext x
  have h := hs.hasSum_funCalc_sub_starProjection hb x
  simp only [Pi.zero_apply, RCLike.ofReal_zero, zero_mul, zero_smul, sub_zero] at h
  simpa using h.unique hasSum_zero

/-- `(φ - ψ)(K*K) = φ(K*K) - ψ(K*K)` for `φ`, `ψ` bounded on `[0, ‖K‖²]`. -/
public theorem IsSingularSystem.funCalc_sub (hs : IsSingularSystem K σ v u) {φ ψ : ℝ → ℝ}
    (hφ : ∃ C, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |φ t| ≤ C)
    (hψ : ∃ C, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |ψ t| ≤ C) :
    hs.funCalc (φ - ψ) (exists_forall_abs_sub_sq_le (hs.exists_bound_sq hφ) (hs.exists_bound_sq hψ))
      = hs.funCalc φ (hs.exists_bound_sq hφ) - hs.funCalc ψ (hs.exists_bound_sq hψ) := by
  rw [hs.funCalc_congr _ (ψ := φ + (-1 : ℝ) • ψ)
        (exists_forall_abs_add_sq_le (hs.exists_bound_sq hφ)
          (exists_forall_abs_smul_sq_le (-1) (hs.exists_bound_sq hψ)))
        (fun t _ => by simp [sub_eq_add_neg]),
    hs.funCalc_add' (hs.exists_bound_sq hφ)
      (exists_forall_abs_smul_sq_le (-1) (hs.exists_bound_sq hψ)),
    hs.funCalc_smul' (-1) (hs.exists_bound_sq hψ)]
  simp [sub_eq_add_neg]

/-- The functional calculus sends `λ ↦ 1 - ωλ` to `Id - ω K*K`. -/
public theorem IsSingularSystem.funCalc_one_sub (hs : IsSingularSystem K σ v u) (ω : ℝ)
    (hb : ∃ C, ∀ i, |(fun t : ℝ => 1 - ω * t) (σ i ^ 2)| ≤ C) :
    hs.funCalc (fun t => 1 - ω * t) hb =
      ContinuousLinearMap.id 𝕜 E -
        (ω : 𝕜) • (K.adjoint ∘L K) := by
  have hbone : ∃ C, ∀ i, |(fun _ : ℝ => (1 : ℝ)) (σ i ^ 2)| ≤ C := ⟨1, fun _ => by norm_num⟩
  have hbid : ∃ C, ∀ i, |id (σ i ^ 2)| ≤ C :=
    hs.exists_bound_sq (AutoIp.exists_bound_on_Icc_of_continuous (‖K‖ ^ 2) continuous_id)
  rw [hs.funCalc_congr hb (ψ := (fun _ : ℝ => (1 : ℝ)) + (-ω) • (id : ℝ → ℝ))
      (exists_forall_abs_add_sq_le hbone (exists_forall_abs_smul_sq_le (-ω) hbid))
      (fun t _ => by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, id_eq]; ring),
    hs.funCalc_add' hbone (exists_forall_abs_smul_sq_le (-ω) hbid),
    hs.funCalc_smul' (-ω) hbid, hs.funCalc_one hbone, hs.funCalc_id hbid]
  simp [sub_eq_add_neg]

/-- The functional calculus sends `λ ↦ (1 - ωλ)ⁿ` to `(Id - ω K*K)ⁿ`. -/
public
theorem IsSingularSystem.funCalc_one_sub_pow (hs : IsSingularSystem K σ v u) (ω : ℝ) (n : ℕ)
    (hb : ∃ C, ∀ i, |(fun t : ℝ => (1 - ω * t) ^ n) (σ i ^ 2)| ≤ C) :
    hs.funCalc (fun t => (1 - ω * t) ^ n) hb =
      (ContinuousLinearMap.id 𝕜 E -
        (ω : 𝕜) • (K.adjoint ∘L K)) ^ n := by
  induction n with
  | zero =>
    have hbone : ∃ C, ∀ i, |(fun _ : ℝ => (1 : ℝ)) (σ i ^ 2)| ≤ C := ⟨1, fun _ => by norm_num⟩
    rw [hs.funCalc_congr hb (ψ := fun _ : ℝ => (1 : ℝ)) hbone (fun t _ => by simp),
      hs.funCalc_one hbone, pow_zero,
      ContinuousLinearMap.one_def]
  | succ n ih =>
    have hbn : ∃ C, ∀ i, |(fun t : ℝ => (1 - ω * t) ^ n) (σ i ^ 2)| ≤ C :=
      hs.exists_bound_sq (AutoIp.exists_bound_on_Icc_of_continuous (‖K‖ ^ 2)
        (φ := fun t : ℝ => (1 - ω * t) ^ n) (by fun_prop))
    have hb1 : ∃ C, ∀ i, |(fun t : ℝ => 1 - ω * t) (σ i ^ 2)| ≤ C :=
      hs.exists_bound_sq (AutoIp.exists_bound_on_Icc_of_continuous (‖K‖ ^ 2)
        (φ := fun t : ℝ => 1 - ω * t) (by fun_prop))
    rw [hs.funCalc_congr hb (ψ := (fun t : ℝ => (1 - ω * t) ^ n) * (fun t : ℝ => 1 - ω * t))
        (exists_forall_abs_mul_sq_le hbn hb1)
        (fun t _ => by simp only [Pi.mul_apply]; ring),
      hs.funCalc_mul' hbn hb1, ih hbn, hs.funCalc_one_sub ω hb1, pow_succ]
    rfl

/-- The functional calculus of a finite geometric sum is the corresponding operator sum. -/
public theorem IsSingularSystem.funCalc_geom_sum (hs : IsSingularSystem K σ v u) (ω : ℝ) (m : ℕ)
    (hb : ∃ C, ∀ i, |(fun t : ℝ => ∑ n ∈ Finset.range m, (1 - ω * t) ^ n) (σ i ^ 2)| ≤ C) :
    hs.funCalc (fun t => ∑ n ∈ Finset.range m, (1 - ω * t) ^ n) hb =
      ∑ n ∈ Finset.range m,
        (ContinuousLinearMap.id 𝕜 E -
          (ω : 𝕜) • (K.adjoint ∘L K)) ^ n := by
  induction m with
  | zero =>
    have hbzero : ∃ C, ∀ i, |(0 : ℝ → ℝ) (σ i ^ 2)| ≤ C := ⟨0, fun _ => by simp⟩
    rw [hs.funCalc_congr hb (ψ := (0 : ℝ → ℝ)) hbzero (fun t _ => by simp),
      hs.funCalc_zero hbzero]
    simp
  | succ m ih =>
    have hbm : ∃ C, ∀ i, |(fun t : ℝ => ∑ n ∈ Finset.range m, (1 - ω * t) ^ n) (σ i ^ 2)| ≤ C :=
      hs.exists_bound_sq (AutoIp.exists_bound_on_Icc_of_continuous (‖K‖ ^ 2)
        (φ := fun t : ℝ => ∑ n ∈ Finset.range m, (1 - ω * t) ^ n) (by fun_prop))
    have hbpow : ∃ C, ∀ i, |(fun t : ℝ => (1 - ω * t) ^ m) (σ i ^ 2)| ≤ C :=
      hs.exists_bound_sq (AutoIp.exists_bound_on_Icc_of_continuous (‖K‖ ^ 2)
        (φ := fun t : ℝ => (1 - ω * t) ^ m) (by fun_prop))
    rw [hs.funCalc_congr hb
        (ψ := (fun t : ℝ => ∑ n ∈ Finset.range m, (1 - ω * t) ^ n)
          + (fun t : ℝ => (1 - ω * t) ^ m))
        (exists_forall_abs_add_sq_le hbm hbpow)
        (fun t _ => by simp [Finset.sum_range_succ]),
      hs.funCalc_add' hbm hbpow, ih hbm, hs.funCalc_one_sub_pow ω m hbpow,
      Finset.sum_range_succ]
