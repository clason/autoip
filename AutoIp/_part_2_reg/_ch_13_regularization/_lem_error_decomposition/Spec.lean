/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose

section _lem_error_decomposition

namespace AutoIp

open Filter Topology
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Error decomposition: for `y ∈ Dom(T†)`, `y^δ ∈ B_δ(y)` and `α > 0`,
`‖R_α y^δ − T†y‖ ≤ δ ‖R_α‖ + ‖R_α y − T†y‖`. The family `{R_α} ⊆ L(Y,X)` is arbitrary, and
`δ = 0` is allowed. -/
public theorem norm_sub_moorePenrose_le {T : E →L[𝕜] F} (R : Set.Ioi (0 : ℝ) → F →L[𝕜] E)
    {y z : F} {δ : ℝ} {α : Set.Ioi (0 : ℝ)}
    (hy : y ∈ mpDomain T) (hz : ‖y - z‖ ≤ δ) :
    ‖R α z - moorePenrose T ⟨y, hy⟩‖ ≤ δ * ‖R α‖ + ‖R α y - moorePenrose T ⟨y, hy⟩‖ := by
  have h1 := norm_sub_le_norm_sub_add_norm_sub (R α z) (R α y) (moorePenrose T ⟨y, hy⟩)
  have hmap : R α z - R α y = R α (z - y) := by rw [map_sub]
  have h2 : ‖R α z - R α y‖ ≤ δ * ‖R α‖ := by
    rw [hmap]
    calc ‖R α (z - y)‖ ≤ ‖R α‖ * ‖z - y‖ := (R α).le_opNorm _
      _ ≤ ‖R α‖ * δ := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [norm_sub_rev]; exact hz
      _ = δ * ‖R α‖ := mul_comm _ _
  linarith

end AutoIp

end _lem_error_decomposition
