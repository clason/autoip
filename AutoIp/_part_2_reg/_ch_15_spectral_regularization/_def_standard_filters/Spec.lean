/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_filter
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_spectral_residual_form
import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.AtTopBotIxx
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init

section _def_standard_filters

namespace AutoIp

open Filter Topology

/-- (i) Truncated singular value decomposition: `φ_α(λ) := λ⁻¹` if `λ ≥ α` and `0`
otherwise. -/
@[expose]
public noncomputable def tsvdFilter (α : Set.Ioi (0 : ℝ)) (lam : ℝ) : ℝ :=
  if (α : ℝ) ≤ lam then lam⁻¹ else 0

/-- (ii) Tikhonov: `φ_α(λ) := (λ + α)⁻¹`. -/
@[expose]
public noncomputable def tikhonovFilter (α : Set.Ioi (0 : ℝ)) (lam : ℝ) : ℝ :=
  (lam + (α : ℝ))⁻¹

/-- (iii) Landweber: `φ_α(λ) := λ⁻¹ (1 − (1 − ωλ)^{1/α})` for `λ ≠ 0`, and
`φ_α(0) := ω/α`. The definition takes any real `ω`; the range `ω ∈ (0, κ⁻¹]` is a hypothesis
of the statement that it is a regularizing filter. -/
@[expose]
public noncomputable def landweberFilter (ω : ℝ) (α : Set.Ioi (0 : ℝ)) (lam : ℝ) : ℝ :=
  if lam = 0 then ω / (α : ℝ)
  else lam⁻¹ * (1 - (1 - ω * lam) ^ ((1 : ℝ) / (α : ℝ)))

/-- (iii), the clause `φ_α(0) = ω/α` of the Landweber filter. -/
public theorem landweberFilter_zero (ω : ℝ) (α : Set.Ioi (0 : ℝ)) :
    landweberFilter ω α 0 = ω / (α : ℝ) := by
  simp [landweberFilter]

/-- (iii), the clause `φ_α(λ) = λ⁻¹ (1 − (1 − ωλ)^{1/α})` for `λ ≠ 0` of the Landweber
filter. -/
public theorem landweberFilter_of_ne_zero {lam : ℝ} (h : lam ≠ 0) (ω : ℝ)
    (α : Set.Ioi (0 : ℝ)) :
    landweberFilter ω α lam = lam⁻¹ * (1 - (1 - ω * lam) ^ ((1 : ℝ) / (α : ℝ))) := by
  simp [landweberFilter, h]

/-- The truncated singular value decomposition filter is a regularizing filter with `C_φ = 1`.

It holds for every `K`, `K = 0` included. -/
public theorem tsvdFilter_isRegularizingFilter {𝕜 : Type*} [RCLike 𝕜] {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (K : E →L[𝕜] F) : IsRegularizingFilter K tsvdFilter 1 where
  const_pos := one_pos
  bddOn := by
    rintro ⟨α, hα⟩
    replace hα : (0 : ℝ) < α := hα
    refine ⟨α⁻¹, fun t ht => ?_⟩
    unfold tsvdFilter
    split
    · rename_i h
      rw [abs_of_nonneg (inv_nonneg.mpr (le_trans hα.le h))]
      gcongr
    · simpa using inv_nonneg.mpr hα.le
  tendsto_inv := by
    intro lam hlam
    have h3 : Tendsto (fun a : ℝ => if a ≤ lam then lam⁻¹ else 0)
        (𝓝[>] (0 : ℝ)) (𝓝 lam⁻¹) := by
      refine Tendsto.congr' ?_ (tendsto_const_nhds (x := lam⁻¹))
      filter_upwards [Ioo_mem_nhdsGT hlam.1] with α hα
      simp [hα.2.le]
    exact (h3.comp (map_coe_Ioi_atBot (0 : ℝ)).le).congr fun _ => rfl
  mul_abs_le := by
    rintro ⟨α, hα⟩ lam hlam
    replace hα : (0 : ℝ) < α := hα
    unfold tsvdFilter
    split
    · rw [abs_of_nonneg (inv_nonneg.mpr hlam.1.le), mul_inv_cancel₀ hlam.1.ne']
    · simp

/-- The Tikhonov filter is a regularizing filter with `C_φ = 1`.

It holds for every `K`, `K = 0` included. -/
public theorem tikhonovFilter_isRegularizingFilter {𝕜 : Type*} [RCLike 𝕜] {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (K : E →L[𝕜] F) : IsRegularizingFilter K tikhonovFilter 1 where
  const_pos := one_pos
  bddOn := by
    rintro ⟨α, hα⟩
    replace hα : (0 : ℝ) < α := hα
    refine ⟨α⁻¹, fun t ht => ?_⟩
    have h : 0 < t + α := by linarith [ht.1]
    rw [tikhonovFilter, abs_of_nonneg (inv_nonneg.mpr h.le)]
    gcongr
    · linarith [ht.1]
  tendsto_inv := by
    intro lam hlam
    have hc : ContinuousAt (fun α : ℝ => (lam + α)⁻¹) 0 :=
      ContinuousAt.inv₀ (by fun_prop) (by simpa using hlam.1.ne')
    have h := hc.tendsto
    simp only [add_zero] at h
    exact ((h.mono_left nhdsWithin_le_nhds).comp
      (map_coe_Ioi_atBot (0 : ℝ)).le).congr fun _ => rfl
  mul_abs_le := by
    rintro ⟨α, hα⟩ lam hlam
    replace hα : (0 : ℝ) < α := hα
    have h : 0 < lam + α := by linarith [hlam.1]
    rw [tikhonovFilter, abs_of_nonneg (inv_nonneg.mpr h.le), ← div_eq_mul_inv, div_le_one h]
    linarith

/-- The Landweber filter, for `ω ∈ (0, κ⁻¹]`, is a regularizing filter with `C_φ = 1`.

The step size `ω ∈ (0, κ⁻¹]` is stated as `0 < ω` and `ωκ ≤ 1`, which is the same for `K ≠ 0` and,
unlike the interval, makes no use of `0⁻¹`. It holds for every `K`, `K = 0` included. -/
public theorem landweberFilter_isRegularizingFilter {𝕜 : Type*} [RCLike 𝕜] {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (K : E →L[𝕜] F) {ω : ℝ} (hω : 0 < ω ∧ ω * ‖K‖ ^ 2 ≤ 1) :
    IsRegularizingFilter K (landweberFilter ω) 1 := by
  obtain ⟨hω0, hωκ1⟩ := hω
  have hb : ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), 0 ≤ 1 - ω * t ∧ 1 - ω * t ≤ 1 := by
    rintro t ⟨ht0, htκ⟩
    constructor
    · nlinarith
    · nlinarith
  constructor
  · exact one_pos
  · rintro ⟨α, hα⟩
    replace hα : (0 : ℝ) < α := hα
    refine ⟨max (ω / α) (max (1 / α) 1 * ω), ?_⟩
    rintro t ht
    obtain ⟨hb0, hb1⟩ := hb t ht
    have hq : 0 < 1 / α := by positivity
    rcases ht.1.lt_or_eq with ht0 | ht0
    · rw [landweberFilter_of_ne_zero ht0.ne']
      have hbq0 : (0 : ℝ) ≤ (1 - ω * t) ^ ((1 : ℝ) / α) := Real.rpow_nonneg hb0 _
      have hbq1 : (1 - ω * t) ^ ((1 : ℝ) / α) ≤ 1 := Real.rpow_le_one hb0 hb1 hq.le
      have hmax1 : (1 : ℝ) ≤ max (1 / α) 1 := le_max_right _ _
      have key : 1 - (1 - ω * t) ^ ((1 : ℝ) / α) ≤ max (1 / α) 1 * (ω * t) := by
        rcases le_or_gt 1 (1 / α) with h | h
        · have hber := one_add_mul_self_le_rpow_one_add (s := -(ω * t)) (by linarith) h
          rw [show (1 : ℝ) + -(ω * t) = 1 - ω * t by ring] at hber
          rw [max_eq_left h]
          linarith
        · rcases hb0.lt_or_eq with hbpos | hbz
          · have h1 := Real.rpow_le_rpow_of_exponent_ge hbpos hb1 h.le
            rw [Real.rpow_one] at h1
            nlinarith
          · rw [← hbz, Real.zero_rpow hq.ne']
            have hone : ω * t = 1 := by linarith
            rw [hone]
            linarith
      rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr ht0.le) (by linarith))]
      refine le_trans ?_ (le_max_right (ω / α) _)
      calc t⁻¹ * (1 - (1 - ω * t) ^ ((1 : ℝ) / α))
          ≤ t⁻¹ * (max (1 / α) 1 * (ω * t)) :=
            mul_le_mul_of_nonneg_left key (inv_nonneg.mpr ht0.le)
        _ = max (1 / α) 1 * ω := by field_simp
    · rw [← ht0, landweberFilter_zero, abs_of_nonneg (by positivity)]
      exact le_max_left _ _
  · rintro lam ⟨hl0, hlκ⟩
    obtain ⟨hb0, hb1⟩ := hb lam ⟨hl0.le, hlκ⟩
    have hblt : 1 - ω * lam < 1 := by nlinarith
    have h0 : Tendsto (fun α : ℝ => (1 - ω * lam) ^ ((1 : ℝ) / α)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := tendsto_rpow_atTop_of_base_lt_one (1 - ω * lam) (by linarith) hblt
      have h2 : Tendsto (fun α : ℝ => (1 : ℝ) / α) (𝓝[>] (0 : ℝ)) atTop := by
        simpa [one_div] using tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
      exact h.comp h2
    have h3 := ((tendsto_const_nhds (x := (1 : ℝ)) (f := 𝓝[>] (0 : ℝ))).sub h0).const_mul lam⁻¹
    simp only [sub_zero, mul_one] at h3
    exact (h3.comp (map_coe_Ioi_atBot (0 : ℝ)).le).congr fun α =>
      (landweberFilter_of_ne_zero hl0.ne' ω α).symm
  · rintro ⟨α, hα⟩ lam ⟨hl0, hlκ⟩
    replace hα : (0 : ℝ) < α := hα
    obtain ⟨hb0, hb1⟩ := hb lam ⟨hl0.le, hlκ⟩
    have hq : 0 < 1 / α := by positivity
    have hbq0 : (0 : ℝ) ≤ (1 - ω * lam) ^ ((1 : ℝ) / α) := Real.rpow_nonneg hb0 _
    have hbq1 : (1 - ω * lam) ^ ((1 : ℝ) / α) ≤ 1 := Real.rpow_le_one hb0 hb1 hq.le
    rw [landweberFilter_of_ne_zero hl0.ne',
      abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hl0.le) (by linarith))]
    have he : lam * (lam⁻¹ * (1 - (1 - ω * lam) ^ ((1 : ℝ) / α)))
        = 1 - (1 - ω * lam) ^ ((1 : ℝ) / α) := by
      field_simp
    rw [he]
    linarith

end AutoIp

end _def_standard_filters

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/- (i) So that `R_α y` is the truncated sum `∑_{σₙ ≥ √α} σₙ⁻¹ ⟨uₙ, y⟩ vₙ`. -/
example (hs : IsSingularSystem K σ v u) (α : Set.Ioi (0 : ℝ)) (y : F) :
    HasSum (fun i => (if Real.sqrt α ≤ σ i then
        (((σ i)⁻¹ : ℝ) : 𝕜) * inner 𝕜 (u i) y else 0) • v i)
      (AutoIp.spectralReg hs AutoIp.tsvdFilter
        ((AutoIp.tsvdFilter_isRegularizingFilter K).exists_bound_on_spectrum hs) α y) := by
  refine (AutoIp.hasSum_spectralReg_and_norm_sq hs _ y).1.congr_fun fun i => ?_
  have hσ := hs.pos i
  unfold AutoIp.tsvdFilter
  by_cases h : Real.sqrt α ≤ σ i
  · have h' : (α : ℝ) ≤ σ i ^ 2 := (Real.sqrt_le_left hσ.le).1 h
    rw [if_pos h, if_pos h']
    congr 2
    push_cast
    field_simp
  · have h' : ¬ (α : ℝ) ≤ σ i ^ 2 := fun h' => h ((Real.sqrt_le_left hσ.le).2 h')
    rw [if_neg h, if_neg h']
    simp

/- (ii) So that `R_α y = ∑ₙ σₙ (σₙ² + α)⁻¹ ⟨uₙ, y⟩ vₙ`. -/
example (hs : IsSingularSystem K σ v u) (α : Set.Ioi (0 : ℝ)) (y : F) :
    HasSum (fun i => (((σ i * (σ i ^ 2 + α)⁻¹ : ℝ) : 𝕜) * inner 𝕜 (u i) y) • v i)
      (AutoIp.spectralReg hs AutoIp.tikhonovFilter
        ((AutoIp.tikhonovFilter_isRegularizingFilter K).exists_bound_on_spectrum hs) α y) := by
  refine (AutoIp.hasSum_spectralReg_and_norm_sq hs _ y).1.congr_fun fun i => ?_
  unfold AutoIp.tikhonovFilter
  rw [mul_comm (σ i ^ 2 + (α : ℝ))⁻¹]
