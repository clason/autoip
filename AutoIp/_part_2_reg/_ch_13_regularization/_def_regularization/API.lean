/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_13_regularization._def_regularization.Spec
import AutoIp._part_1_funcanal._ch_01_bounded_operators._prop_dense_ptwise_filter
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_domain_dense
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_equations
import AutoIp._part_1_funcanal._ch_01_bounded_operators._prop_dense_ptwise_filter
import AutoIp._part_1_funcanal._ch_05_weak_convergence._lem_strong_to_weak
import AutoIp._part_1_funcanal._ch_05_weak_convergence._lem_weak_limit_unique
import AutoIp._part_1_funcanal._ch_05_weak_convergence._lem_weak_seq_cont
import AutoIp._part_1_funcanal._ch_05_weak_convergence._thm_weak_compactness
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_domain
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_domain_dense
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_equations

open Filter Topology
namespace AutoIp

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- For a regularization `{R_α}` of `T†` with `sup_{α>0} ‖T R_α‖ < ∞`, `T R_α z → P_R z` as
`α → 0` for every `z ∈ Y`, where `P_R` is the orthogonal projection onto the closure of
`Ran(T)`. -/
public theorem tendsto_apply_starProjection {T : E →L[𝕜] F} {R : Set.Ioi (0 : ℝ) → F →L[𝕜] E}
    (hR : IsRegularization T R) (hbdd : ∃ C : ℝ, ∀ α : Set.Ioi (0 : ℝ), ‖T ∘L R α‖ ≤ C)
    (z : F) :
    Tendsto (fun α => T (R α z)) atBot
      (𝓝 (T.toLinearMap.range.topologicalClosure.starProjection z)) := by
  obtain ⟨C, hC⟩ := hbdd
  have hMdense : Dense (Submodule.span 𝕜 ((mpDomain T : Set F)) : Set F) := by
    rw [Submodule.span_eq]
    exact dense_domain_moorePenrose
  have hTM : ∀ w ∈ (mpDomain T : Set F), Tendsto (fun α => (T ∘L R α) w) atBot
      (𝓝 ((LinearMap.range T.toLinearMap).topologicalClosure.starProjection w)) := by
    intro w hw
    have h1 : Tendsto (fun α => T (R α w)) atBot (𝓝 (T (moorePenrose T ⟨w, hw⟩))) :=
      (T.continuous.tendsto _).comp (hR w hw)
    rwa [apply_moorePenrose ⟨_, hw⟩] at h1
  exact ContinuousLinearMap.tendsto_of_dense_span_filter_of_eventually_norm_le
    atBot (fun α => T ∘L R α)
    ((LinearMap.range T.toLinearMap).topologicalClosure.starProjection) C
    (Filter.Eventually.of_forall hC)
    ((mpDomain T : Set F)) hMdense hTM z

end AutoIp
