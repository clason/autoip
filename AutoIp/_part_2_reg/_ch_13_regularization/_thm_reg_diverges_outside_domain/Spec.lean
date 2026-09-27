/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_13_regularization._def_regularization
import AutoIp._part_1_funcanal._ch_01_bounded_operators._prop_dense_ptwise_filter
import AutoIp._part_1_funcanal._ch_05_weak_convergence._lem_strong_to_weak
import AutoIp._part_1_funcanal._ch_05_weak_convergence._lem_weak_limit_unique
import AutoIp._part_1_funcanal._ch_05_weak_convergence._lem_weak_seq_cont
import AutoIp._part_1_funcanal._ch_05_weak_convergence._thm_weak_compactness
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_domain
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_domain_dense
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_equations

section _thm_reg_diverges_outside_domain

namespace AutoIp

open Filter Topology
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Divergence outside the domain: for a regularization `{R_α}` of `T†` with
`sup_{α>0} ‖T R_α‖ < ∞`, `‖R_α y‖ → ∞` as `α → 0`, for every `y ∉ Dom(T†)`. -/
public theorem tendsto_norm_atTop_of_notMem_mpDomain {T : E →L[𝕜] F}
    {R : Set.Ioi (0 : ℝ) → F →L[𝕜] E} (hR : IsRegularization T R)
    (hbdd : ∃ C : ℝ, ∀ α : Set.Ioi (0 : ℝ), ‖T ∘L R α‖ ≤ C)
    {y : F} (hy : y ∉ mpDomain T) :
    Tendsto (fun α : Set.Ioi (0 : ℝ) => ‖R α y‖) atBot atTop := by
  by_contra hcon
  rw [tendsto_atTop, not_forall] at hcon
  obtain ⟨M, hM⟩ := hcon
  rw [Filter.not_eventually] at hM
  obtain ⟨u, hu, hup⟩ := Filter.exists_seq_forall_of_frequently hM
  have hbound : ∀ n, ‖R (u n) y‖ ≤ M := fun n => (not_le.mp (hup n)).le
  obtain ⟨φ, x, hφ, hwk⟩ :=
    exists_tendstoWeakly_subseq_of_bounded (𝕜 := 𝕜) (fun n => R (u n) y) M hbound
  have husub : Tendsto (fun k => u (φ k)) atTop atBot := hu.comp hφ.tendsto_atTop
  have h1 : Tendsto (fun k => T (R (u (φ k)) y)) atTop
      (𝓝 ((LinearMap.range T.toLinearMap).topologicalClosure.starProjection y)) :=
    (tendsto_apply_starProjection hR hbdd y).comp husub
  have hw2 : TendstoWeakly 𝕜 (fun k => T (R (u (φ k)) y)) (T x) := hwk.map T
  have hTx : T x = (LinearMap.range T.toLinearMap).topologicalClosure.starProjection y :=
    hw2.unique (TendstoWeakly.of_tendsto h1)
  exact hy (mem_mpDomain_iff.mpr ⟨x, hTx⟩)

end AutoIp

end _thm_reg_diverges_outside_domain
