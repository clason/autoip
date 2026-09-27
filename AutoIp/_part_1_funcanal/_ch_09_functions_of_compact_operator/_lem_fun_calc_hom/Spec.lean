/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_fun_calc
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_fun_calc_basic
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound
import AutoIp.Auxiliary.Rpow
import AutoIp.Auxiliary.BoundedOnIcc

section _lem_fun_calc_hom

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- `(g + h)(K*K) = g(K*K) + h(K*K)` for `g`, `h` bounded on `[0, κ]`. -/
public theorem IsSingularSystem.funCalc_add (hs : IsSingularSystem K σ v u) {φ ψ : ℝ → ℝ}
    (hφ : ∃ C, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |φ t| ≤ C)
    (hψ : ∃ C, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |ψ t| ≤ C) :
    hs.funCalc (φ + ψ) (exists_forall_abs_add_sq_le (hs.exists_bound_sq hφ) (hs.exists_bound_sq hψ))
      = hs.funCalc φ (hs.exists_bound_sq hφ) + hs.funCalc ψ (hs.exists_bound_sq hψ) :=
  hs.funCalc_add' (hs.exists_bound_sq hφ) (hs.exists_bound_sq hψ)

/-- `(c g)(K*K) = c g(K*K)` for `g` bounded on `[0, κ]` and `c ∈ ℝ`. -/
public theorem IsSingularSystem.funCalc_smul (hs : IsSingularSystem K σ v u) (c : ℝ) {φ : ℝ → ℝ}
    (hφ : ∃ C, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |φ t| ≤ C) :
    hs.funCalc (c • φ) (exists_forall_abs_smul_sq_le c (hs.exists_bound_sq hφ))
      = (c : 𝕜) • hs.funCalc φ (hs.exists_bound_sq hφ) :=
  hs.funCalc_smul' c (hs.exists_bound_sq hφ)

/-- `(g h)(K*K) = g(K*K) ∘ h(K*K)` for `g`, `h` bounded on `[0, κ]`. -/
public theorem IsSingularSystem.funCalc_mul (hs : IsSingularSystem K σ v u) {φ ψ : ℝ → ℝ}
    (hφ : ∃ C, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |φ t| ≤ C)
    (hψ : ∃ C, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |ψ t| ≤ C) :
    hs.funCalc (φ * ψ) (exists_forall_abs_mul_sq_le (hs.exists_bound_sq hφ) (hs.exists_bound_sq hψ))
      = hs.funCalc φ (hs.exists_bound_sq hφ) ∘L hs.funCalc ψ (hs.exists_bound_sq hψ) :=
  hs.funCalc_mul' (hs.exists_bound_sq hφ) (hs.exists_bound_sq hψ)

/-- `φ_ν(K*K) vₙ = σₙ^ν vₙ` for every index `n`, where `φ_ν(t) = t^{ν/2}`. The exponent `ν` is
any real for which `φ_ν` is bounded at the `σₙ²`, not only `ν > 0`. -/
public theorem IsSingularSystem.funCalc_rpow_apply_v (hs : IsSingularSystem K σ v u) (ν : ℝ)
    (hb : ∃ C, ∀ i, |(fun t : ℝ => t ^ (ν / 2)) (σ i ^ 2)| ≤ C) (i : ι) :
    hs.funCalc (fun t => t ^ (ν / 2)) hb (v i) = ((σ i ^ ν : ℝ) : 𝕜) • v i := by
  rw [hs.funCalc_apply_v, AutoIp.rpow_sq_div_two (hs.pos i).le]

end _lem_fun_calc_hom
