/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_11_moore_penrose._def_moore_penrose
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_domain_dense
import AutoIp._part_2_reg._ch_11_moore_penrose._lem_mp_equations
import AutoIp._part_2_reg._ch_11_moore_penrose._thm_mp_minnorm

section _thm_mp_inverse

section

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- `T̃ := T|_{Ker(T)ᗮ} : Ker(T)ᗮ → Ran(T)` is bijective. -/
public theorem ContinuousLinearMap.bijOn_orthogonal_ker [CompleteSpace E] (T : E →L[𝕜] F) :
    Set.BijOn T (T.toLinearMap.kerᗮ : Set E)
      T.toLinearMap.range := by
  refine ⟨fun x _ => ⟨x, rfl⟩, ?_, ?_⟩
  · intro a ha b hb hab
    have hsub : a - b ∈ LinearMap.ker T.toLinearMap := by
      simp [LinearMap.mem_ker, map_sub, hab]
    have hsub' : a - b ∈ (LinearMap.ker T.toLinearMap)ᗮ :=
      Submodule.sub_mem _ ha hb
    have := (Submodule.mem_orthogonal _ _).1 hsub' _ hsub
    rw [inner_self_eq_zero] at this
    exact sub_eq_zero.1 this
  · intro y hy
    obtain ⟨x, rfl⟩ := hy
    refine ⟨x - (LinearMap.ker T.toLinearMap).starProjection x, ?_, ?_⟩
    · exact (LinearMap.ker T.toLinearMap).sub_starProjection_mem_orthogonal x
    · have h0 : T ((LinearMap.ker T.toLinearMap).starProjection x) = 0 :=
        LinearMap.mem_ker.1 (Submodule.starProjection_apply_mem _ _)
      simp [map_sub, h0]


end

section

namespace AutoIp

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- `Ker(T†) = Ran(T)ᗮ`: for `y ∈ Dom(T†)`, `T† y = 0` if and only if `y ∈ Ran(T)ᗮ`. -/
public theorem moorePenrose_eq_zero_iff {T : E →L[𝕜] F} (y : (moorePenrose T).domain) :
    moorePenrose T y = 0 ↔ (y : F) ∈ T.toLinearMap.rangeᗮ := by
  have hmp := moorePenrose_isMinimumNorm y
  constructor
  · intro h
    obtain ⟨h1, -⟩ := isMinimumNorm_iff.1 hmp
    rw [h] at h1
    simpa using h1
  · intro h
    exact hmp.unique (isMinimumNorm_iff.2 ⟨by simpa using h, Submodule.zero_mem _⟩)

/-- `T†` extends `T̃⁻¹`: `T† (T x) = x` for every `x ∈ Ker(T)ᗮ`. -/
public theorem moorePenrose_apply_apply_of_mem_orthogonal {T : E →L[𝕜] F} {x : E}
    (hx : x ∈ T.toLinearMap.kerᗮ) :
    moorePenrose T ⟨(T x), (Submodule.mem_sup_left ⟨x, rfl⟩)⟩ = x := by
  rw [moorePenrose_apply_apply, (Submodule.starProjection_apply_eq_zero_iff _).2 hx, sub_zero]

/-- `T†` is the unique linear extension of `T̃⁻¹` to `Dom(T†)` with kernel `Ran(T)ᗮ`: a map
`S` that extends `T̃⁻¹` and whose kernel contains `Ran(T)ᗮ` agrees with `T†` on `Dom(T†)`.
Of `S` the Lean asks only additivity on `Dom(T†)` and `Ran(T)ᗮ ⊆ Ker(S)`, weaker than the
blueprint's linearity and `Ker(S) = Ran(T)ᗮ`. -/
public theorem eq_moorePenrose_of_apply_eq_of_eq_zero {T : E →L[𝕜] F} {S : F → E}
    (hadd : ∀ y ∈ mpDomain T, ∀ z ∈ mpDomain T, S (y + z) = S y + S z)
    (hinv : ∀ x ∈ T.toLinearMap.kerᗮ, S (T x) = x)
    (hzero : ∀ y ∈ T.toLinearMap.rangeᗮ, S y = 0)
    {y : F} (hy : y ∈ mpDomain T) : S y = moorePenrose T ⟨y, hy⟩ := by
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨w, hwperp, hTw⟩ := (ContinuousLinearMap.bijOn_orthogonal_ker T).surjOn hy₁
  have h1 : y₁ ∈ mpDomain T := Submodule.mem_sup_left hy₁
  have h2 : y₂ ∈ mpDomain T := Submodule.mem_sup_right hy₂
  have hL : S (y₁ + y₂) = w := by
    rw [hadd _ h1 _ h2, hzero _ hy₂, add_zero, ← hTw, hinv w hwperp]
  -- Proof irrelevance makes this the value the goal names, whatever membership proof it
  -- carries, so `exact` closes what `rw` could not: the motive mentions the proof.
  have hR : moorePenrose T ⟨(y₁ + y₂), (Submodule.add_mem _ h1 h2)⟩ = w := by
    rw [show (⟨y₁ + y₂, Submodule.add_mem _ h1 h2⟩ : (moorePenrose T).domain)
        = ⟨y₁, h1⟩ + ⟨y₂, h2⟩ from rfl, (moorePenrose T).map_add,
      moorePenrose_eq_zero_of_mem_orthogonal_range hy₂, add_zero]
    subst hTw
    exact moorePenrose_apply_apply_of_mem_orthogonal hwperp
  rw [hL]
  exact hR.symm

end AutoIp

end

end _thm_mp_inverse
