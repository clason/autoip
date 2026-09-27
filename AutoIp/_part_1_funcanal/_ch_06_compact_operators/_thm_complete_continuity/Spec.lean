/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_05_weak_convergence._def_weak_conv
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import AutoIp._part_1_funcanal._ch_05_weak_convergence._lem_strong_to_weak
import AutoIp._part_1_funcanal._ch_05_weak_convergence._lem_weak_bounded
import AutoIp._part_1_funcanal._ch_05_weak_convergence._lem_weak_limit_unique
import AutoIp._part_1_funcanal._ch_05_weak_convergence._lem_weak_seq_cont
import AutoIp._part_1_funcanal._ch_05_weak_convergence._thm_weak_compactness
import AutoIp._part_1_funcanal._ch_06_compact_operators._lem_compact_seq

section _thm_complete_continuity

section

open scoped InnerProductSpace Topology
variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [CompleteSpace H] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The converse: when the domain `H` is a Hilbert space, an operator T ∈ 𝓛(H, F) that maps
weakly convergent sequences to norm convergent ones is compact. The hypothesis names the norm
limit, xₙ ⇀ a giving Txₙ → Ta. -/
public theorem isCompactOperator_of_tendstoWeakly_tendsto {T : H →L[𝕜] F}
    (h : ∀ (x : ℕ → H) (a : H), TendstoWeakly 𝕜 x a →
      Filter.Tendsto (fun n => T (x n)) Filter.atTop (nhds (T a))) :
    IsCompactOperator T := by
  -- Every bounded sequence has a weakly convergent subsequence (Hilbert), and the
  -- hypothesis upgrades that to norm convergence of the image.
  refine (isCompactOperator_iff_tendsto_subseq T).mpr fun x C hC => ?_
  obtain ⟨φ, a, hφ, ha⟩ := exists_tendstoWeakly_subseq_of_bounded (𝕜 := 𝕜) x C hC
  exact ⟨φ, T a, hφ, h _ a ha⟩


end

section

open scoped Topology
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If T ∈ 𝓛(E, F) between normed spaces is compact then T maps weakly convergent sequences
to norm convergent ones: xₙ ⇀ a gives Txₙ → Ta. -/
public theorem IsCompactOperator.tendsto_of_tendstoWeakly {T : E →L[𝕜] F}
    (hT : IsCompactOperator T) {x : ℕ → E} {a : E}
    (h : TendstoWeakly 𝕜 x a) :
    Filter.Tendsto (fun n => T (x n)) Filter.atTop (nhds (T a)) := by
  -- It suffices that every subsequence has a further subsequence converging to `T a`.
  refine Filter.tendsto_of_subseq_tendsto fun ns hns => ?_
  -- Weakly convergent sequences are bounded, so the sequential characterisation of
  -- compactness extracts a subsequence whose image converges in norm.
  obtain ⟨C, hC⟩ := h.exists_norm_le
  obtain ⟨ψ, w, hψ, hw⟩ :=
    (isCompactOperator_iff_tendsto_subseq T).mp hT (fun k => x (ns k)) C (fun k => hC _)
  -- The norm limit is also a weak limit, and the image sequence converges weakly to `T a`.
  refine ⟨ψ, ?_⟩
  have hweq : w = T a :=
    (TendstoWeakly.of_tendsto hw).unique ((h.map T).comp (hns.comp hψ.tendsto_atTop))
  rwa [hweq] at hw


end

end _thm_complete_continuity
