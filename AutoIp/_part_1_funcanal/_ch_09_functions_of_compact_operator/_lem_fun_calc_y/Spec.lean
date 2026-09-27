/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_fun_calc_y
import AutoIp._part_1_funcanal._ch_03_hilbert_spaces._prop_adjoint_props
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_basic
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_bounded
public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_hom

section _lem_fun_calc_y

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- The norm bound for `ψ(KK*)`: for any `a` with `|ψ(σₙ²)| ≤ a` for all `n`,
`‖ψ(KK*)‖ ≤ max a |ψ(0)|`. -/
public theorem IsSingularSystem.norm_funCalcRight_le (hs : IsSingularSystem K σ v u) (ψ : ℝ → ℝ)
    (a : ℝ) (ha : ∀ i, |ψ (σ i ^ 2)| ≤ a) :
    ‖hs.funCalcRight ψ ⟨a, ha⟩‖ ≤ max a |ψ 0| := by
  rw [hs.funCalcRight_eq]
  exact hs.adjoint.norm_funCalc_le ψ a ha

/-- `id(KK*) = KK*`. -/
public theorem IsSingularSystem.funCalcRight_id (hs : IsSingularSystem K σ v u)
    (hid : ∃ C, ∀ i, |id (σ i ^ 2)| ≤ C) :
    hs.funCalcRight id hid = K ∘L K.adjoint := by
  rw [hs.funCalcRight_eq]
  have h : hs.adjoint.funCalc id hid
      = ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint K) ∘L
        ContinuousLinearMap.adjoint K := hs.adjoint.funCalc_id hid
  rw [h, ContinuousLinearMap.adjoint_adjoint]

/-- `(g h)(KK*) = g(KK*) ∘ h(KK*)` for `g`, `h` bounded on `[0, κ]`. -/
public theorem IsSingularSystem.funCalcRight_mul (hs : IsSingularSystem K σ v u) {ψ χ : ℝ → ℝ}
    (hψ : ∃ C, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |ψ t| ≤ C)
    (hχ : ∃ C, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |χ t| ≤ C) :
    hs.funCalcRight (ψ * χ)
        (exists_forall_abs_mul_sq_le (hs.exists_bound_sq hψ) (hs.exists_bound_sq hχ))
      = hs.funCalcRight ψ (hs.exists_bound_sq hψ)
        ∘L hs.funCalcRight χ (hs.exists_bound_sq hχ) := by
  have hn : ‖ContinuousLinearMap.adjoint K‖ = ‖K‖ := ContinuousLinearMap.norm_adjoint K
  rw [hs.funCalcRight_eq, hs.funCalcRight_eq, hs.funCalcRight_eq]
  exact hs.adjoint.funCalc_mul (by rwa [hn]) (by rwa [hn])

/-- `𝟏(KK*) = Id_Y`. -/
public theorem IsSingularSystem.funCalcRight_one (hs : IsSingularSystem K σ v u)
    (h1 : ∃ C, ∀ i, |(fun _ : ℝ => (1 : ℝ)) (σ i ^ 2)| ≤ C) :
    hs.funCalcRight (fun _ => 1) h1 = ContinuousLinearMap.id 𝕜 F := by
  rw [hs.funCalcRight_eq]
  exact hs.adjoint.funCalc_one h1

/-- `√(KK*) ∘ √(KK*) = KK*`. -/
public theorem IsSingularSystem.funCalcRight_sqrt_comp_funCalcRight_sqrt
    (hs : IsSingularSystem K σ v u) (hb : ∃ C, ∀ i, |Real.sqrt (σ i ^ 2)| ≤ C) :
    hs.funCalcRight Real.sqrt hb ∘L hs.funCalcRight Real.sqrt hb
      = K ∘L K.adjoint := by
  rw [hs.funCalcRight_eq]
  have h := hs.adjoint.funCalc_sqrt_comp_funCalc_sqrt hb
  rwa [ContinuousLinearMap.adjoint_adjoint] at h

/-- `(g + h)(KK*) = g(KK*) + h(KK*)` for `g`, `h` bounded on `[0, κ]`. -/
public theorem IsSingularSystem.funCalcRight_add (hs : IsSingularSystem K σ v u) {ψ χ : ℝ → ℝ}
    (hψ : ∃ C, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |ψ t| ≤ C)
    (hχ : ∃ C, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |χ t| ≤ C) :
    hs.funCalcRight (ψ + χ)
        (exists_forall_abs_add_sq_le (hs.exists_bound_sq hψ) (hs.exists_bound_sq hχ))
      = hs.funCalcRight ψ (hs.exists_bound_sq hψ)
        + hs.funCalcRight χ (hs.exists_bound_sq hχ) := by
  have hn : ‖ContinuousLinearMap.adjoint K‖ = ‖K‖ := ContinuousLinearMap.norm_adjoint K
  rw [hs.funCalcRight_eq, hs.funCalcRight_eq, hs.funCalcRight_eq]
  exact hs.adjoint.funCalc_add (by rwa [hn]) (by rwa [hn])

/-- `(c g)(KK*) = c g(KK*)` for `g` bounded on `[0, κ]` and `c ∈ ℝ`. -/
public theorem IsSingularSystem.funCalcRight_smul (hs : IsSingularSystem K σ v u) (c : ℝ)
    {ψ : ℝ → ℝ} (hψ : ∃ C, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |ψ t| ≤ C) :
    hs.funCalcRight (c • ψ) (exists_forall_abs_smul_sq_le c (hs.exists_bound_sq hψ))
      = (c : 𝕜) • hs.funCalcRight ψ (hs.exists_bound_sq hψ) := by
  have hn : ‖ContinuousLinearMap.adjoint K‖ = ‖K‖ := ContinuousLinearMap.norm_adjoint K
  rw [hs.funCalcRight_eq, hs.funCalcRight_eq]
  exact hs.adjoint.funCalc_smul c (by rwa [hn])

/-- `φ_ν(KK*) uₙ = σₙ^ν uₙ` for every index `n`, where `φ_ν(t) = t^{ν/2}`. The exponent `ν` is
any real for which `φ_ν` is bounded at the `σₙ²`, not only `ν > 0`. -/
public theorem IsSingularSystem.funCalcRight_rpow_apply_u (hs : IsSingularSystem K σ v u)
    (ν : ℝ) (hb : ∃ C, ∀ i, |(fun t : ℝ => t ^ (ν / 2)) (σ i ^ 2)| ≤ C) (i : ι) :
    hs.funCalcRight (fun t => t ^ (ν / 2)) hb (u i) = ((σ i ^ ν : ℝ) : 𝕜) • u i := by
  rw [hs.funCalcRight_eq]
  exact hs.adjoint.funCalc_rpow_apply_v ν hb i

end _lem_fun_calc_y
