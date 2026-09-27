/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_residual_constant.Spec
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound
import AutoIp._part_2_reg._ch_15_spectral_regularization._lem_spectral_residual_form

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- For `C ≥ C_r`, `‖p - K R_α p‖ ≤ ‖q - K R_α q‖ + C ‖p - q‖` for all `p, q ∈ Y`. -/
public theorem norm_residual_le_add (hs : IsSingularSystem K σ v u) (hK : K ≠ 0)
    {φ : Set.Ioi (0 : ℝ) → ℝ → ℝ} {Cφ : ℝ} (hφ : IsRegularizingFilter K φ Cφ) {C : ℝ}
    (hC : (⨆ b : Set.Ioi (0 : ℝ), ⨆ lam ∈ Set.Ioc (0 : ℝ) (‖K‖ ^ 2),
      |1 - lam * φ b lam|) ≤ C)
    {β : Set.Ioi (0 : ℝ)} (p q : F) :
    ‖p - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β p)‖
      ≤ ‖q - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β q)‖ + C * ‖p - q‖ := by
  obtain ⟨-, -, hresid⟩ := one_le_iSup_abs_one_sub_mul_and_norm_residual_le hs hK hφ
  have hd : p - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β p)
      = (q - K (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β q)) + ((p - q) - K
          (spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β (p - q))) := by
    have hl : spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β p
        = spectralReg hs φ (hφ.exists_bound_on_spectrum
            hs) β q + spectralReg hs φ (hφ.exists_bound_on_spectrum hs) β (p - q) := by
      rw [← map_add]; congr 1; abel
    rw [hl, map_add]; abel
  rw [hd]
  refine (norm_add_le _ _).trans ?_
  have h2 := mul_le_mul_of_nonneg_right hC (norm_nonneg (p - q))
  linarith [hresid (p - q) β]

end AutoIp
