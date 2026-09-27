/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_18_discretization._def_dual_lsq_projection
public import AutoIp._part_2_reg._ch_18_discretization._lem_dual_lsq_range_closed
import AutoIp._part_2_reg._ch_18_discretization._lem_dual_lsq_formula
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.GDelta.MetrizableSpace

section _thm_dual_lsq_convergence

namespace AutoIp

open Filter Topology
open scoped InnerProductSpace ENNReal
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Convergence of the dual least-squares projection: for every `y ∈ Dom(T†)`, `xₙ → x†`,
for nested subspaces `Y n` with `dim Yₙ = n` and `closure(⋃ₙ Yₙ) = Ker(T*)ᗮ`.

The inclusions `Yₙ ⊆ Ker(T*)ᗮ` and `dim Ran(T)‾ = ∞` of the blueprint follow from these
hypotheses and are not assumed separately. -/
public theorem dualLsq_tendsto (T : E →L[𝕜] F) (Y : ℕ → Submodule 𝕜 F)
    [∀ n, (Y n).HasOrthogonalProjection]
    (hmono : Monotone Y) (hfin : ∀ n, Module.finrank 𝕜 (Y n) = n)
    (hdenseY : (⨆ n, Y n).topologicalClosure =
      (T.adjoint.toLinearMap.ker)ᗮ)
    {y : F} (hy : y ∈ mpDomain T) :
    Tendsto (fun n => dualLsqProjection T Y y (mem_mpDomain_dualLsq T Y hmono hfin y) n) atTop
      (𝓝 (moorePenrose T ⟨y, hy⟩)) := by
  have hyd : ∀ m, (Y m).starProjection y ∈ mpDomain ((Y m).starProjection ∘L T) :=
    mem_mpDomain_dualLsq T Y hmono hfin y
  classical
  have hsub : ∀ n, Y n ≤ (LinearMap.ker (ContinuousLinearMap.adjoint T).toLinearMap)ᗮ := by
    intro n
    rw [← hdenseY]
    exact le_trans (le_iSup Y n) (Submodule.le_topologicalClosure _)
  have hfd : ∀ m, FiniteDimensional 𝕜 (Y m) := by
    intro m
    have : FiniteDimensional 𝕜 (Y (m + 1)) :=
      FiniteDimensional.of_finrank_pos (by rw [hfin]; omega)
    exact Submodule.finiteDimensional_of_le (hmono (Nat.le_succ m))
  set Ts : F →L[𝕜] E := ContinuousLinearMap.adjoint T with hTs
  set X : ℕ → Submodule 𝕜 E := fun m => Submodule.map Ts.toLinearMap (Y m) with hXdef
  have hXm : ∀ m, X m = Submodule.map Ts.toLinearMap (Y m) := fun _ => rfl
  have hXfd : ∀ m, FiniteDimensional 𝕜 (X m) := by
    intro m
    have := hfd m
    rw [hXm m]
    infer_instance
  have hXop : ∀ m, (X m).HasOrthogonalProjection := by
    intro m
    have := hXfd m
    infer_instance
  have hXmono : Monotone X := fun a b hab => Submodule.map_mono (hmono hab)
  have hker : (LinearMap.range Ts.toLinearMap)ᗮ = LinearMap.ker T.toLinearMap := by
    have h := Ts.orthogonal_range
    rwa [hTs, ContinuousLinearMap.adjoint_adjoint] at h
  have hclosureRange : (LinearMap.range Ts.toLinearMap).topologicalClosure
      = (LinearMap.ker T.toLinearMap)ᗮ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hker]
  have hUle : (⨆ m, X m).topologicalClosure ≤ (LinearMap.ker T.toLinearMap)ᗮ := by
    rw [← hclosureRange]
    refine Submodule.topologicalClosure_mono (iSup_le fun m => ?_)
    rintro z ⟨w, -, rfl⟩
    exact ⟨w, rfl⟩
  have hperp : (⨆ m, X m)ᗮ ≤ LinearMap.ker T.toLinearMap := by
    intro z hz
    have hTz1 : T z ∈ (⨆ m, Y m)ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro u hu
      rw [Submodule.mem_iSup_of_directed _ hmono.directed_le] at hu
      obtain ⟨m, hm⟩ := hu
      have hmemX : Ts u ∈ ⨆ m, X m := (le_iSup X m) ⟨u, hm, rfl⟩
      have h0 := (Submodule.mem_orthogonal _ _).1 hz (Ts u) hmemX
      rwa [hTs, ContinuousLinearMap.adjoint_inner_left] at h0
    rw [← Submodule.orthogonal_closure, hdenseY] at hTz1
    have hTz3 : T z ∈ (LinearMap.ker Ts.toLinearMap)ᗮ := by
      have hrng : (LinearMap.range T.toLinearMap)ᗮ = LinearMap.ker Ts.toLinearMap :=
        T.orthogonal_range
      rw [← hrng]
      exact Submodule.le_orthogonal_orthogonal _ ⟨z, rfl⟩
    have hmem : T z ∈ (LinearMap.ker Ts.toLinearMap)ᗮ ⊓ ((LinearMap.ker Ts.toLinearMap)ᗮ)ᗮ :=
      ⟨hTz3, hTz1⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hmem
    exact hmem
  have hclosure : (⨆ m, X m).topologicalClosure = (LinearMap.ker T.toLinearMap)ᗮ := by
    refine le_antisymm hUle ?_
    calc (LinearMap.ker T.toLinearMap)ᗮ ≤ ((⨆ m, X m)ᗮ)ᗮ := Submodule.orthogonal_le hperp
      _ = (⨆ m, X m).topologicalClosure := Submodule.orthogonal_orthogonal_eq_closure _
  have : ((⨆ m, X m).topologicalClosure).HasOrthogonalProjection := by
    rw [hclosure]; infer_instance
  have hxd : moorePenrose T ⟨y, hy⟩ ∈ (LinearMap.ker T.toLinearMap)ᗮ :=
    moorePenrose_mem_orthogonal_ker ⟨_, hy⟩
  have h := Submodule.starProjection_tendsto_closure_iSup X hXmono (moorePenrose T ⟨y, hy⟩)
  have hfix : (⨆ m, X m).topologicalClosure.starProjection (moorePenrose T ⟨y, hy⟩)
      = moorePenrose T ⟨y, hy⟩ := by
    refine Submodule.starProjection_eq_self_iff.2 ?_
    rw [hclosure]
    exact hxd
  rw [hfix] at h
  refine h.congr fun m => ?_
  exact (dualLsqProjection_eq_starProjection T Y X m rfl (hsub m) hy hyd).symm

end AutoIp

end _thm_dual_lsq_convergence
