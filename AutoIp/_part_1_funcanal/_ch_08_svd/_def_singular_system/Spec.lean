/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

section _def_singular_system

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The conditions of a singular system `{(σ i, v i, u i)}` for `K` that do not concern the order of
the singular values: positivity from (1), and (2)–(4). The index set is an arbitrary type; the
initial segment of `ℕ`, the ordering and the null-sequence clause of (1) are the further conditions
of an ordered singular system. An orthonormal basis of a closed subspace is stated as an orthonormal
family whose closed span is that subspace. -/
public structure IsSingularSystem (K : E →L[𝕜] F) {ι : Type*}
    (σ : ι → ℝ) (v : ι → E) (u : ι → F) : Prop where
  /-- Condition (1), positivity: `σ i > 0` for every index. -/
  pos : ∀ i, 0 < σ i
  /-- Condition (2), orthonormality: `{v i}` is an orthonormal family. -/
  orthonormal_left : Orthonormal 𝕜 v
  /-- Condition (3), orthonormality: `{u i}` is an orthonormal family. -/
  orthonormal_right : Orthonormal 𝕜 u
  /-- Condition (2), completeness: the closed span of `{v i}` is `𝒩(K)ᗮ`. -/
  span_left : (Submodule.span 𝕜 (Set.range v)).topologicalClosure = (K.toLinearMap.ker)ᗮ
  /-- Condition (3), completeness: the closed span of `{u i}` is the closure of `ℛ(K)`. -/
  span_right :
    (Submodule.span 𝕜 (Set.range u)).topologicalClosure =
      K.toLinearMap.range.topologicalClosure
  /-- Condition (4), first half: `K v i = σ i u i`. -/
  map_left : ∀ i, K (v i) = (σ i : 𝕜) • u i
  /-- Condition (4), second half: `K* u i = σ i v i`. -/
  map_right : ∀ i, K.adjoint (u i) = (σ i : 𝕜) • v i

/-- A singular system `{(σₙ, vₙ, uₙ)}_{n ∈ I}` for `K`, indexed by an initial segment `I ⊆ ℕ`.
The indices start at `0` rather than `1`. -/
public structure IsOrderedSingularSystem (K : E →L[𝕜] F) {I : Set ℕ}
    (σ : I → ℝ) (v : I → E) (u : I → F) : Prop extends IsSingularSystem K σ v u where
  /-- The index set `I` is an initial segment of `ℕ`. -/
  isLowerSet : ∀ ⦃m n : ℕ⦄, n ∈ I → m ≤ n → m ∈ I
  /-- Condition (1), ordering: `σ₁ ≥ σ₂ ≥ ⋯`. -/
  antitone : Antitone σ
  /-- Condition (1), null sequence: `σₙ → 0` if `I` is infinite. -/
  tendsto_zero : I.Infinite → Filter.Tendsto σ Filter.atTop (nhds 0)

end _def_singular_system
