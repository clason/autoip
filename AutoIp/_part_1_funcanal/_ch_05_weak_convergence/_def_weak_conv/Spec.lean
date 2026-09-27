/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.InnerProductSpace.Dual -- shake: keep
import Mathlib.Analysis.Normed.Module.WeakDual -- shake: keep

section _def_weak_conv

/-- A sequence xₙ in a normed space X converges weakly to a, written xₙ ⇀ a, if
⟨xₙ, f⟩ → ⟨a, f⟩ for every f ∈ X′. The scalar field is an explicit argument because it fixes
the dual X′. -/
@[expose]
public def TendstoWeakly (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (x : ℕ → E) (a : E) : Prop :=
  ∀ f : StrongDual 𝕜 E, Filter.Tendsto (fun n => f (x n)) Filter.atTop (nhds (f a))

end _def_weak_conv

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

example (x : ℕ → E) (a : E) :
    Filter.Tendsto (fun n => toWeakSpace 𝕜 E (x n)) Filter.atTop
        (nhds (toWeakSpace 𝕜 E a))
      ↔ TendstoWeakly 𝕜 x a :=
  WeakBilin.tendsto_iff_forall_eval_tendsto _ fun _ _ h =>
    SeparatingDual.eq_iff_forall_dual_eq.2 fun f => congrFun (congrArg DFunLike.coe h) f

/- In a Hilbert space weak convergence reads `⟨xₙ, z⟩ → ⟨x, z⟩` for all `z`. -/
example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (x : ℕ → H) (a : H) :
    TendstoWeakly 𝕜 x a ↔
      ∀ z : H, Filter.Tendsto (fun n => inner 𝕜 (x n) z) Filter.atTop (nhds (inner 𝕜 a z)) := by
  have hconj : ∀ (p : ℕ → 𝕜) (q : 𝕜), Filter.Tendsto p Filter.atTop (nhds q) →
      Filter.Tendsto (fun n => (starRingEnd 𝕜) (p n)) Filter.atTop (nhds ((starRingEnd 𝕜) q)) :=
    fun p q h => (RCLike.continuous_conj.tendsto q).comp h
  constructor
  · intro h z
    simpa only [innerSL_apply_apply, inner_conj_symm] using hconj _ _ (h (innerSL 𝕜 z))
  · intro h f
    have key := hconj _ _ (h ((InnerProductSpace.toDual 𝕜 H).symm f))
    simp only [inner_conj_symm, InnerProductSpace.toDual_symm_apply] at key
    exact key
