/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal

section _lem_inner_through_series

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*}

/-- The inner product commutes with a series in its second slot, the display (*) of the
node's proof: if `∑ₙ xₙ` converges to `x`, then `∑ₙ ⟨z, xₙ⟩` converges to `⟨z, x⟩`. -/
public theorem HasSum.inner_right {f : ι → E} {x : E} (hf : HasSum f x) (z : E) :
    HasSum (fun i => inner 𝕜 z (f i)) (inner 𝕜 z x) := by
  simpa using hf.mapL (innerSL 𝕜 z)

/-- The inner product commutes with a series: if `∑ₙ xₙ` converges to `x`, then
`∑ₙ ⟨xₙ, z⟩` converges to `⟨x, z⟩`, so `⟨∑ₙ xₙ, z⟩ = ∑ₙ ⟨xₙ, z⟩`. -/
public theorem HasSum.inner_left {f : ι → E} {x : E} (hf : HasSum f x) (z : E) :
    HasSum (fun i => inner 𝕜 (f i) z) (inner 𝕜 x z) := by
  have h := (HasSum.inner_right hf z).map (starRingEnd 𝕜) continuous_star
  simpa only [Function.comp_def, inner_conj_symm] using h

/-- Consequently the coefficients of an expansion in an orthonormal system `{eₙ}` are unique:
if `∑ₙ cₙ eₙ` and `∑ₙ dₙ eₙ` both converge to `x`, then `cₙ = dₙ` for every `n`. -/
public theorem Orthonormal.eq_of_hasSum_smul {e : ι → E} (he : Orthonormal 𝕜 e) {c d : ι → 𝕜}
    {x : E} (hc : HasSum (fun i => c i • e i) x) (hd : HasSum (fun i => d i • e i) x) :
    c = d := by
  classical
  have key : ∀ b : ι → 𝕜, HasSum (fun i => b i • e i) x → ∀ j, inner 𝕜 (e j) x = b j := by
    intro b hb j
    have h := HasSum.inner_right (𝕜 := 𝕜) hb (e j)
    simp only [inner_smul_right, orthonormal_iff_ite.mp he, mul_ite, mul_one, mul_zero] at h
    have hfun : (fun i => if j = i then b i else 0) = fun i => if i = j then b j else 0 := by
      funext i
      by_cases hij : j = i
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    rw [hfun] at h
    exact h.unique (hasSum_ite_eq j (b j))
  funext j
  rw [← key c hc j, ← key d hd j]

end _lem_inner_through_series
