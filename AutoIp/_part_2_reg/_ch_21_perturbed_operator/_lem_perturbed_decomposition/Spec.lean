/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
public import AutoIp._part_2_reg._ch_15_spectral_regularization._def_spectral_reg
import AutoIp._part_2_reg._ch_13_regularization._lem_error_decomposition

section _lem_perturbed_decomposition

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K Kh : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F} {ι' : Type*}
variable {σ' : ι' → ℝ} {v' : ι' → E} {u' : ι' → F}

/-- Three-term error decomposition: for every `α > 0`,
`‖x^{h,δ}_α - x†‖ ≤ ‖(R_α[K_h] - R_α[K]) y^δ‖ + δ ‖R_α[K]‖ + ‖R_α[K] y - x†‖`, with
`x† = K† y`.

Of the admissibility of the data only `‖y - y^δ‖ ≤ δ` is used. The Lean holds for every `y` in
`Dom(K†)`, not only `Ran(K)`, and for every family `φ` bounded on both spectra, not only a
regularizing filter. -/
public theorem norm_sub_moorePenrose_le_perturbed (hs : IsSingularSystem K σ v u)
    (hsh : IsSingularSystem Kh σ' v' u') (φ : Set.Ioi (0 : ℝ) → ℝ → ℝ)
    (hbd : ∀ α : Set.Ioi (0 : ℝ), ∃ C, ∀ i, |φ α (σ i ^ 2)| ≤ C)
    (hbdh : ∀ α : Set.Ioi (0 : ℝ), ∃ C, ∀ i, |φ α (σ' i ^ 2)| ≤ C)
    {y z : F} (α : Set.Ioi (0 : ℝ)) {δ : ℝ}
    (hy : y ∈ mpDomain K) (hz : ‖y - z‖ ≤ δ) :
    ‖spectralReg hsh φ hbdh α z - moorePenrose K ⟨y, hy⟩‖ ≤
      ‖(spectralReg hsh φ hbdh α - spectralReg hs φ hbd α) z‖
        + δ * ‖spectralReg hs φ hbd α‖
        + ‖spectralReg hs φ hbd α y - moorePenrose K ⟨y, hy⟩‖ := by
  have h1 : ‖spectralReg hs φ hbd α z - moorePenrose K ⟨y, hy⟩‖ ≤
      δ * ‖spectralReg hs φ hbd α‖ + ‖spectralReg hs φ hbd α y - moorePenrose K ⟨y, hy⟩‖ :=
    norm_sub_moorePenrose_le (T := K) (fun a => spectralReg hs φ hbd a) hy hz
  have hsplit : spectralReg hsh φ hbdh α z - moorePenrose K ⟨y, hy⟩ =
      (spectralReg hsh φ hbdh α - spectralReg hs φ hbd α) z +
        (spectralReg hs φ hbd α z - moorePenrose K ⟨y, hy⟩) := by
    rw [sub_apply]
    abel
  have h2 : ‖spectralReg hsh φ hbdh α z - moorePenrose K ⟨y, hy⟩‖ ≤
      ‖(spectralReg hsh φ hbdh α - spectralReg hs φ hbd α) z‖ +
        ‖spectralReg hs φ hbd α z - moorePenrose K ⟨y, hy⟩‖ := by
    rw [hsplit]; exact norm_add_le _ _
  linarith

end AutoIp

end _lem_perturbed_decomposition
