/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_13_regularization._def_regularization
import AutoIp._part_2_reg._ch_13_regularization._thm_reg_diverges_outside_domain

section _thm_discrepancy_well_defined

namespace AutoIp

open Filter Topology
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The discrepancy principle is realisable: for a regularization `{R_α}` of `T†` with `Ran(T)`
dense in `Y` and `sup_{α>0} ‖T R_α‖ < ∞`, a null sequence `{α_n}` and `τ > 0`, for all `δ > 0`
and `y^δ ∈ Y` there is a smallest `n*` with
`‖T R_{α_{n*}} y^δ − y^δ‖ ≤ τδ < ‖T R_{α_n} y^δ − y^δ‖` for all `n < n*`. The sequence
`{α_n}` is not required to be strictly decreasing. -/
public theorem exists_discrepancy_index {T : E →L[𝕜] F} {R : Set.Ioi (0 : ℝ) → F →L[𝕜] E}
    (hR : IsRegularization T R)
    (hdense : Dense (T.toLinearMap.range : Set F))
    (hbdd : ∃ C : ℝ, ∀ α : Set.Ioi (0 : ℝ), ‖T ∘L R α‖ ≤ C)
    {α : ℕ → Set.Ioi (0 : ℝ)}
    (hnull : Tendsto α atTop atBot) {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) (z : F) :
    ∃ n : ℕ, ‖T (R (α n) z) - z‖ ≤ τ * δ ∧ ∀ m < n, τ * δ < ‖T (R (α m) z) - z‖ := by
  classical
  have hclos : (LinearMap.range T.toLinearMap).topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp hdense
  have hstep : Tendsto (fun α : Set.Ioi (0 : ℝ) => T (R α z)) atBot (𝓝 z) := by
    have h := tendsto_apply_starProjection hR hbdd z
    have hPz : (LinearMap.range T.toLinearMap).topologicalClosure.starProjection z = z :=
      Submodule.starProjection_eq_self_iff.mpr (by rw [hclos]; exact Submodule.mem_top)
    rwa [hPz] at h
  have hlim : Tendsto (fun n => ‖T (R (α n) z) - z‖) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n => T (R (α n) z)) atTop (𝓝 z) := hstep.comp hnull
    simpa using (h2.sub (tendsto_const_nhds (x := z))).norm
  have hex : ∃ n : ℕ, ‖T (R (α n) z) - z‖ ≤ τ * δ := by
    obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (mul_pos hτ hδ))).exists
    exact ⟨n, hn.le⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, fun m hm => ?_⟩
  have hnm := Nat.find_min hex hm
  push Not at hnm
  exact hnm

end AutoIp

end _thm_discrepancy_well_defined
