/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_05_weak_convergence._def_weak_conv
public import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.LinearMap

section _thm_radon_riesz

open scoped InnerProductSpace Topology
variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- In a Hilbert space, if xₙ ⇀ a and ‖xₙ‖ → ‖a‖ then xₙ → a strongly.
Completeness is not assumed: an inner product space suffices. -/
public theorem TendstoWeakly.tendsto_of_tendsto_norm
    {x : ℕ → H} {a : H} (hw : TendstoWeakly 𝕜 x a)
    (hn : Filter.Tendsto (fun n => ‖x n‖) Filter.atTop (nhds ‖a‖)) :
    Filter.Tendsto x Filter.atTop (nhds a) := by
  -- `‖xₙ - a‖² = ‖xₙ‖² - 2 Re⟪a, xₙ⟫ + ‖a‖² → ‖a‖² - 2‖a‖² + ‖a‖² = 0`.
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hinner : Filter.Tendsto (fun n => RCLike.re (inner 𝕜 a (x n) : 𝕜)) Filter.atTop
      (nhds (‖a‖ ^ 2)) := by
    have h1 := hw (innerSL 𝕜 a)
    have h2 := ((RCLike.reCLM (K := 𝕜)).continuous.tendsto _).comp h1
    simpa [Function.comp_def, inner_self_eq_norm_sq] using h2
  have hsq : Filter.Tendsto (fun n => ‖x n - a‖ ^ 2) Filter.atTop (nhds 0) := by
    have hcomb := ((hn.pow 2).sub
      ((tendsto_const_nhds (x := (2 : ℝ)) (f := Filter.atTop)).mul hinner)).add
      (tendsto_const_nhds (x := ‖a‖ ^ 2) (f := (Filter.atTop : Filter ℕ)))
    have hzero : ‖a‖ ^ 2 - 2 * ‖a‖ ^ 2 + ‖a‖ ^ 2 = 0 := by ring
    rw [hzero] at hcomb
    refine hcomb.congr fun n => ?_
    have hre : RCLike.re (inner 𝕜 (x n) a : 𝕜) = RCLike.re (inner 𝕜 a (x n) : 𝕜) := by
      rw [inner_re_symm]
    rw [norm_sub_sq (𝕜 := 𝕜), hre]
  have := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this

end _thm_radon_riesz
