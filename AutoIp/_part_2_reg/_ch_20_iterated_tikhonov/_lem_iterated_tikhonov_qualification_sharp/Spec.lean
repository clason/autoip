/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_qualification
public import AutoIp._part_2_reg._ch_20_iterated_tikhonov._def_iterated_tikhonov
import AutoIp._part_2_reg._ch_20_iterated_tikhonov._thm_iterated_tikhonov_qualification
import AutoIp._part_2_reg._ch_20_iterated_tikhonov._lem_iterated_tikhonov_filter

section _lem_iterated_tikhonov_qualification_sharp

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- For `m ≥ 1` and `ν > 2m` there is no constant `C` with (Q_ν), and the qualification of
`{φ^(m)_α}` is exactly `2m`. The hypothesis is `K ≠ 0`, weaker than the prose's
infinite-dimensional range. -/
public theorem iteratedTikhonov_qualification (K : E →L[𝕜] F) (hK : K ≠ 0) {m : ℕ} (hm : 0 < m) :
    (∀ ν > 2 * (m : ℝ), ¬ ∃ C : ℝ, HasResidualBound K (iteratedTikhonovFilter m) ν C) ∧
      qualification K (iteratedTikhonovFilter m) = 2 * (m : ℝ≥0∞) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hκ : (0 : ℝ) < ‖K‖ ^ 2 := by positivity
  have hres : ∀ (α : Set.Ioi (0 : ℝ)) (lam : ℝ), 0 < lam →
      1 - lam * iteratedTikhonovFilter m α lam = ((α : ℝ) / ((α : ℝ) + lam)) ^ m :=
    fun _ _ hlam => one_sub_mul_iteratedTikhonovFilter hlam
  -- `ω_ν(α) ≥ κ^{ν/2} (α/(α+κ))^m`, the supremum at the single point `λ = κ`
  have hlow : ∀ ν : ℝ, 0 < ν → ∀ α : Set.Ioi (0 : ℝ),
      (‖K‖ ^ 2) ^ (ν / 2) * ((α : ℝ) / ((α : ℝ) + ‖K‖ ^ 2)) ^ m ≤
        ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
          lam ^ (ν / 2) * |1 - lam * iteratedTikhonovFilter m α lam| := by
    intro ν hν α
    have hα : (0 : ℝ) < (α : ℝ) := α.2
    have hbd : ∀ lam : ℝ,
        (⨆ _ : lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
          lam ^ (ν / 2) * |1 - lam * iteratedTikhonovFilter m α lam|)
          ≤ (‖K‖ ^ 2) ^ (ν / 2) := by
      intro lam
      refine Real.iSup_le (fun h => ?_) (Real.rpow_nonneg hκ.le _)
      have hlam : (0 : ℝ) < lam := h.1
      have hsum : (0 : ℝ) < (α : ℝ) + lam := by linarith
      have hu0 : (0 : ℝ) ≤ (α : ℝ) / ((α : ℝ) + lam) := by positivity
      have hu1 : (α : ℝ) / ((α : ℝ) + lam) ≤ 1 := by rw [div_le_one hsum]; linarith
      rw [hres α lam hlam, abs_of_nonneg (pow_nonneg hu0 m)]
      have h1 : lam ^ (ν / 2) ≤ (‖K‖ ^ 2) ^ (ν / 2) :=
        Real.rpow_le_rpow hlam.le h.2 (by linarith)
      have h2 : ((α : ℝ) / ((α : ℝ) + lam)) ^ m ≤ 1 := pow_le_one₀ hu0 hu1
      nlinarith [Real.rpow_nonneg hlam.le (ν / 2), pow_nonneg hu0 m]
    have hbdd : BddAbove (Set.range (fun lam : ℝ =>
        ⨆ _ : lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
          lam ^ (ν / 2) * |1 - lam * iteratedTikhonovFilter m α lam|)) :=
      ⟨(‖K‖ ^ 2) ^ (ν / 2), by rintro _ ⟨lam, rfl⟩; exact hbd lam⟩
    have h1 := le_ciSup hbdd (‖K‖ ^ 2)
    rw [ciSup_pos (show (‖K‖ ^ 2) ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2) from ⟨hκ, le_rfl⟩),
      hres α _ hκ, abs_of_nonneg (pow_nonneg (by positivity) m)] at h1
    exact h1
  have hpart1 : ∀ ν > 2 * (m : ℝ), ¬ ∃ C : ℝ, HasResidualBound K (iteratedTikhonovFilter
      m) ν C := by
    rintro ν hν ⟨C, hC⟩
    have hν0 : (0 : ℝ) < ν := by linarith
    have hs0 : (0 : ℝ) < ν / 2 - m := by linarith
    set s := ν / 2 - (m : ℝ) with hsdef
    set D := (‖K‖ ^ 2) ^ (ν / 2) / (2 * ‖K‖ ^ 2) ^ m with hDdef
    have hD0 : 0 < D := by
      rw [hDdef]
      have : (0 : ℝ) < (‖K‖ ^ 2) ^ (ν / 2) := Real.rpow_pos_of_pos hκ _
      positivity
    have hmain : ∀ a : ℝ, 0 < a → a ≤ ‖K‖ ^ 2 → D * a ^ m ≤ C * a ^ (ν / 2) := by
      intro a ha haκ
      obtain ⟨α, rfl⟩ : ∃ α : Set.Ioi (0 : ℝ), (α : ℝ) = a := ⟨⟨a, Set.mem_Ioi.2 ha⟩, rfl⟩
      have h1 := (hlow ν hν0 α).trans (hC.omega_le α haκ)
      have h2 : ((α : ℝ) / (2 * ‖K‖ ^ 2)) ^ m ≤ ((α : ℝ) / ((α : ℝ) + ‖K‖ ^ 2)) ^ m := by
        refine pow_le_pow_left₀ (by positivity) ?_ m
        exact div_le_div_of_nonneg_left ha.le (by linarith) (by linarith)
      have h3 : D * (α : ℝ) ^ m = (‖K‖ ^ 2) ^ (ν / 2) * ((α : ℝ) / (2 * ‖K‖ ^ 2)) ^ m := by
        rw [hDdef, div_pow]
        ring
      rw [h3]
      refine le_trans ?_ h1
      exact mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hκ.le _)
    have hDle : ∀ a : ℝ, 0 < a → a ≤ ‖K‖ ^ 2 → D ≤ C * a ^ s := by
      intro a ha haκ
      have hexp : a ^ (ν / 2) = a ^ m * a ^ s := by
        rw [← Real.rpow_natCast a m, ← Real.rpow_add ha]
        congr 1
        rw [hsdef]; ring
      have h := hmain a ha haκ
      rw [hexp, show C * (a ^ m * a ^ s) = C * a ^ s * a ^ m by ring] at h
      exact le_of_mul_le_mul_right h (pow_pos ha m)
    have hC0 : 0 < C := by
      by_contra hcon
      push Not at hcon
      have h := hDle _ (lt_min hκ one_pos) (min_le_left _ _)
      have hpos : (0 : ℝ) < (min (‖K‖ ^ 2) 1) ^ s :=
        Real.rpow_pos_of_pos (lt_min hκ one_pos) _
      nlinarith
    set c : ℝ := (D / (2 * C)) ^ (1 / s) with hcdef
    have hc0 : (0 : ℝ) < c := Real.rpow_pos_of_pos (by positivity) _
    have hα0 : (0 : ℝ) < min (‖K‖ ^ 2) c := lt_min hκ hc0
    have hcs : c ^ s = D / (2 * C) := by
      rw [hcdef, ← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hs0.ne',
        Real.rpow_one]
    have hαs : (min (‖K‖ ^ 2) c) ^ s ≤ D / (2 * C) := by
      rw [← hcs]
      exact Real.rpow_le_rpow hα0.le (min_le_right _ _) hs0.le
    have hfin := hDle _ hα0 (min_le_left _ _)
    have hhalf : C * (min (‖K‖ ^ 2) c) ^ s ≤ D / 2 := by
      calc C * (min (‖K‖ ^ 2) c) ^ s ≤ C * (D / (2 * C)) :=
            mul_le_mul_of_nonneg_left hαs hC0.le
        _ = D / 2 := by field_simp
    linarith
  refine ⟨hpart1, ?_⟩
  have hconv : ENNReal.ofReal (2 * (m : ℝ)) = 2 * (m : ℝ≥0∞) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simp
  refine le_antisymm ((qualification_le_iff _ _ _).2 fun ν hν => ?_) ?_
  · obtain ⟨hν0, Cν, hCle⟩ := hν
    have hle : ν ≤ 2 * (m : ℝ) := by
      by_contra hcon
      push Not at hcon
      exact hpart1 ν hcon ⟨Cν, hCle⟩
    exact hconv ▸ ENNReal.ofReal_le_ofReal hle
  · rw [← hconv]
    exact le_qualification K _ (by positivity)
      ⟨1, ⟨1, iteratedTikhonovFilter_isRegularizingFilter K hm⟩, one_pos, fun α _ =>
        iSup_rpow_mul_abs_one_sub_mul_iteratedTikhonovFilter_le K (by positivity) le_rfl α⟩

/-- The qualification of `{φ^(m)_α}` is exactly `2m`, for `m ≥ 1`. The hypothesis is `K ≠ 0`,
weaker than the prose's infinite-dimensional range. -/
public
theorem qualification_iteratedTikhonovFilter (K : E →L[𝕜] F) (hK : K ≠ 0) {m : ℕ} (hm : 0 < m) :
    qualification K (iteratedTikhonovFilter m) = 2 * (m : ℝ≥0∞) :=
  (iteratedTikhonov_qualification K hK hm).2

/-- For `m ≥ 1` and `ν > 2m` there is no constant `C` with (Q_ν). The hypothesis is `K ≠ 0`,
weaker than the prose's infinite-dimensional range. -/
public
theorem not_exists_qualification_const_of_gt (K : E →L[𝕜] F) (hK : K ≠ 0) {m : ℕ} (hm : 0 < m)
    {ν : ℝ} (hν : 2 * (m : ℝ) < ν) :
    ¬ ∃ C : ℝ, HasResidualBound K (iteratedTikhonovFilter m) ν C :=
  (iteratedTikhonov_qualification K hK hm).1 ν hν

end AutoIp

end _lem_iterated_tikhonov_qualification_sharp
