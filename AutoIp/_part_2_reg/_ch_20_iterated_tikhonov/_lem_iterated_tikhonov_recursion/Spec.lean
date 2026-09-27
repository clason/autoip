/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
public import AutoIp._part_2_reg._ch_20_iterated_tikhonov._def_iterated_tikhonov
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_basic
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_hom
import AutoIp._part_2_reg._ch_16_tikhonov._lem_tikhonov_normal

section _lem_iterated_tikhonov_recursion

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- For `α > 0` and `y ∈ Y`, if `z₀ = 0` and `z_k = z_{k-1} + (K*K + α)⁻¹ K* (y - K z_{k-1})` for
`k = 1, …, m`, then `z_m = φ^(m)_α(K*K) K* y`. Each step is stated as the equation
`(K*K + α)(z_k - z_{k-1}) = K* (y - K z_{k-1})`, which is equivalent since `K*K + α` is
invertible. The index `m` may be `0`, and the singular system need not be ordered.

It holds for every `K`, `K = 0` included. -/
public theorem iteratedTikhonov_eq_spectralReg (hs : IsSingularSystem K σ v u)
    {α : Set.Ioi (0 : ℝ)} (y : F) (z : ℕ → E) (hz0 : z 0 = 0) (m : ℕ)
    (hrec : ∀ k < m,
      (K.adjoint ∘L K + ((α : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E) (z (k + 1) - z k) =
        K.adjoint (y - K (z k))) :
    z m = spectralReg hs (iteratedTikhonovFilter m)
      (iteratedTikhonovFilter_exists_bound_on_spectrum hs m) α y := by
  have hα : (0 : ℝ) < (α : ℝ) := α.2
  have hα' : (α : ℝ) ≠ 0 := hα.ne'
  have hbT : ∃ c, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |tikhonovFilter α t| ≤ c :=
    (tikhonovFilter_isRegularizingFilter K).bddOn α
  have hbone : ∃ c, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |(fun _ => (1 : ℝ)) t| ≤ c :=
    ⟨1, fun t _ => by simp⟩
  have hbid : ∃ c, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |(id : ℝ → ℝ) t| ≤ c :=
    ⟨‖K‖ ^ 2, fun t ht => by simpa [abs_of_nonneg ht.1] using ht.2⟩
  have hbφ : ∀ n : ℕ, ∃ c, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2),
      |iteratedTikhonovFilter n α t| ≤ c :=
    fun n => ⟨(n : ℝ) / (α : ℝ), fun t ht => abs_iteratedTikhonovFilter_le ht.1⟩
  have hbTsq := tikhonovFilter_exists_bound_on_spectrum hs α
  have hbonesq := hs.exists_bound_sq hbone
  have hbidsq := hs.exists_bound_sq hbid
  have hbφsq : ∀ n : ℕ, ∃ c, ∀ i, |iteratedTikhonovFilter n α (σ i ^ 2)| ≤ c :=
    fun n => iteratedTikhonovFilter_exists_bound_on_spectrum hs n α
  have hcongr1 : hs.funCalc ((tikhonovFilter α) * (id : ℝ → ℝ))
        (exists_forall_abs_mul_sq_le hbTsq hbidsq)
      = hs.funCalc ((fun _ => (1 : ℝ)) + (-(α : ℝ)) • tikhonovFilter α)
        (exists_forall_abs_add_sq_le hbonesq (exists_forall_abs_smul_sq_le (-(α : ℝ)) hbTsq)) := by
    refine hs.funCalc_congr _ _ ?_
    intro t ht
    have hsum : (0 : ℝ) < t + (α : ℝ) := by linarith [ht.1]
    have hne : t + (α : ℝ) ≠ 0 := hsum.ne'
    simp only [Pi.mul_apply, id_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, tikhonovFilter]
    field_simp
    ring
  have hTid : hs.funCalc (tikhonovFilter α) hbTsq ∘L (ContinuousLinearMap.adjoint K ∘L K)
      = ContinuousLinearMap.id 𝕜 E
        - (RCLike.ofReal (α : ℝ) : 𝕜) • hs.funCalc (tikhonovFilter α) hbTsq := by
    rw [← hs.funCalc_id hbidsq, ← hs.funCalc_mul' hbTsq hbidsq, hcongr1,
      hs.funCalc_add' hbonesq (exists_forall_abs_smul_sq_le (-(α : ℝ)) hbTsq),
      hs.funCalc_one hbonesq,
      hs.funCalc_smul' (-(α : ℝ)) hbTsq, RCLike.ofReal_neg, neg_smul, ← sub_eq_add_neg]
  have hstep : ∀ k < m, z (k + 1)
      = (RCLike.ofReal (α : ℝ) : 𝕜) • hs.funCalc (tikhonovFilter α) hbTsq (z k)
        + hs.funCalc (tikhonovFilter α) hbTsq (ContinuousLinearMap.adjoint K y) := by
    intro k hk
    have h := (tikhonov_iff_normal hs (y - K (z k)) (z (k + 1) - z k)).mpr (hrec k hk)
    rw [spectralReg_eq hs tikhonovFilter (tikhonovFilter_exists_bound_on_spectrum hs) α,
      ContinuousLinearMap.comp_apply] at h
    simp only [map_sub] at h
    have h2 := congrArg (fun S : E →L[𝕜] E => S (z k)) hTid
    simp only [sub_apply, ContinuousLinearMap.id_apply,
      smul_apply, ContinuousLinearMap.comp_apply] at h2
    rw [h2] at h
    rw [sub_eq_iff_eq_add.mp h]
    abel
  induction m with
  | zero =>
    have h0 : hs.funCalc (iteratedTikhonovFilter 0 α) (hbφsq 0) = 0 := by
      have hc : hs.funCalc (iteratedTikhonovFilter 0 α) (hbφsq 0)
          = hs.funCalc ((0 : ℝ) • (fun _ => (1 : ℝ)))
            (exists_forall_abs_smul_sq_le 0 hbonesq) := by
        refine hs.funCalc_congr _ _ ?_
        intro t ht
        simp only [Pi.smul_apply, smul_eq_mul, zero_mul]
        rcases eq_or_ne t 0 with rfl | h
        · simp [iteratedTikhonovFilter_zero]
        · simp [iteratedTikhonovFilter_of_ne_zero h]
      rw [hc, hs.funCalc_smul' 0 hbonesq, hs.funCalc_one hbonesq]
      simp
    rw [hz0, spectralReg_eq hs (iteratedTikhonovFilter 0)
      (iteratedTikhonovFilter_exists_bound_on_spectrum hs 0) α,
      ContinuousLinearMap.comp_apply, h0]
    simp
  | succ n ih =>
    have hkey : hs.funCalc (iteratedTikhonovFilter (n + 1) α) (hbφsq (n + 1))
        = (RCLike.ofReal (α : ℝ) : 𝕜)
            • hs.funCalc (tikhonovFilter α * iteratedTikhonovFilter n α)
              (exists_forall_abs_mul_sq_le hbTsq (hbφsq n))
          + hs.funCalc (tikhonovFilter α) hbTsq := by
      have hc : hs.funCalc (iteratedTikhonovFilter (n + 1) α) (hbφsq (n + 1))
          = hs.funCalc ((α : ℝ) • (tikhonovFilter α * iteratedTikhonovFilter n α)
              + tikhonovFilter α)
            (exists_forall_abs_add_sq_le
              (exists_forall_abs_smul_sq_le (α : ℝ) (exists_forall_abs_mul_sq_le hbTsq (hbφsq n)))
              hbTsq) := by
        refine hs.funCalc_congr _ _ ?_
        intro t ht
        have hsum : (0 : ℝ) < t + (α : ℝ) := by linarith [ht.1]
        have hsum' : (0 : ℝ) < (α : ℝ) + t := by linarith [ht.1]
        have hne1 : t + (α : ℝ) ≠ 0 := hsum.ne'
        have hne2 : (α : ℝ) + t ≠ 0 := hsum'.ne'
        rcases eq_or_ne t 0 with rfl | ht0
        · simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul,
            tikhonovFilter_apply, iteratedTikhonovFilter_zero]
          push_cast
          field_simp
          ring
        · simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul,
            tikhonovFilter_apply, iteratedTikhonovFilter_of_ne_zero ht0, pow_succ]
          set w := ((α : ℝ) / ((α : ℝ) + t)) ^ n with hw
          field_simp
          ring
      rw [hc, hs.funCalc_add' (exists_forall_abs_smul_sq_le (α : ℝ)
          (exists_forall_abs_mul_sq_le hbTsq (hbφsq n))) hbTsq,
        hs.funCalc_smul' (α : ℝ) (exists_forall_abs_mul_sq_le hbTsq (hbφsq n))]
    rw [hstep n (Nat.lt_succ_self n),
      ih (fun k hk => hrec k (Nat.lt_succ_of_lt hk))
        (fun k hk => hstep k (Nat.lt_succ_of_lt hk)),
      spectralReg_eq hs (iteratedTikhonovFilter n)
        (iteratedTikhonovFilter_exists_bound_on_spectrum hs n) α,
      spectralReg_eq hs (iteratedTikhonovFilter (n + 1))
        (iteratedTikhonovFilter_exists_bound_on_spectrum hs (n + 1)) α,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hkey]
    simp only [add_apply, smul_apply]
    rw [hs.funCalc_mul' hbTsq (hbφsq n)]
    rfl

end AutoIp

end _lem_iterated_tikhonov_recursion
