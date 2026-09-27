/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_2_reg._ch_19_general_source_conditions._def_index_function
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Data.EReal.Inv
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Algebra

section _def_theta_function

namespace AutoIp

open Filter Topology

/-- The balancing function `Θ_φ(α) := √α φ(α)`.

It is defined for every real `α` and every `φ`, not only on `[0, κ]` for an index
function. -/
public noncomputable def thetaIndex (φ : ℝ → ℝ) (α : ℝ) : ℝ :=
  Real.sqrt α * φ α

/-- The defining formula `Θ_φ(α) = √α φ(α)`. -/
public theorem thetaIndex_apply (φ : ℝ → ℝ) (α : ℝ) :
    thetaIndex φ α = Real.sqrt α * φ α := by
  unfold thetaIndex
  rfl

/-- For an index function `φ` on `[0, κ]`, `Θ_φ` is again an index function on `[0, κ]`. -/
public theorem isIndexFunction_thetaIndex {κ : ℝ} {φ : ℝ → ℝ} (hφ : IsIndexFunction κ φ) :
    IsIndexFunction κ (thetaIndex φ) :=
  by
  refine ⟨?_, ?_, ?_⟩
  · rw [thetaIndex_apply, Real.sqrt_zero, zero_mul]
  · rw [funext (thetaIndex_apply φ)]
    exact Real.continuous_sqrt.continuousOn.mul hφ.continuousOn
  · exact fun a ha b hb hab =>
      mul_lt_mul'' (Real.sqrt_lt_sqrt ha.1 hab) (hφ.strictMonoOn ha hb hab)
        (Real.sqrt_nonneg a) (hφ.nonneg a ha)

/-- For an index function `φ` on `[0, κ]`, `Θ_φ` has an inverse on `(0, Θ_φ(κ)]`: every
`t` there is `Θ_φ(α)` for exactly one `α ∈ (0, κ]`. -/
public theorem existsUnique_thetaIndex_eq {κ : ℝ} {φ : ℝ → ℝ} (hφ : IsIndexFunction κ φ) {t : ℝ}
    (ht : t ∈ Set.Ioc (0 : ℝ) (thetaIndex φ κ)) :
    ∃! α, α ∈ Set.Ioc (0 : ℝ) κ ∧ thetaIndex φ α = t :=
  by
  have hΘ := isIndexFunction_thetaIndex hφ
  have hk : (0:ℝ) < κ := by
    by_contra hcon
    push Not at hcon
    have hz : thetaIndex φ κ = 0 := by
      rw [thetaIndex_apply, Real.sqrt_eq_zero_of_nonpos hcon, zero_mul]
    rw [hz] at ht
    linarith [ht.1, ht.2]
  have hmem : t ∈ Set.Icc (thetaIndex φ 0) (thetaIndex φ κ) := by
    refine ⟨?_, ht.2⟩
    rw [hΘ.map_zero]
    exact ht.1.le
  obtain ⟨α, hαmem, hαeq⟩ := intermediate_value_Icc hk.le hΘ.continuousOn hmem
  have hα0 : (0:ℝ) < α := by
    rcases hαmem.1.eq_or_lt with h | h
    · exfalso
      rw [← h, hΘ.map_zero] at hαeq
      linarith [ht.1]
    · exact h
  refine ⟨α, ⟨⟨hα0, hαmem.2⟩, hαeq⟩, ?_⟩
  rintro β ⟨hβmem, hβeq⟩
  exact hΘ.strictMonoOn.injOn ⟨hβmem.1.le, hβmem.2⟩ hαmem (by rw [hβeq, hαeq])

/-- `Θ_φ` has a continuous strictly increasing inverse `Θ_φ⁻¹` on `[0, Θ_φ(κ)]`: `Θ_φ` is an
order isomorphism of `[0, κ]` onto `[0, Θ_φ(κ)]`, and its inverse is continuous. -/
public theorem exists_orderIso_thetaIndex {κ : ℝ} (hκ : 0 ≤ κ) {φ : ℝ → ℝ}
    (hφ : IsIndexFunction κ φ) :
    ∃ e : Set.Icc (0 : ℝ) κ ≃o Set.Icc (0 : ℝ) (thetaIndex φ κ),
      (∀ x, (e x : ℝ) = thetaIndex φ x) ∧ Continuous e.symm := by
  have hΘ := isIndexFunction_thetaIndex hφ
  have himg : thetaIndex φ '' Set.Icc 0 κ = Set.Icc 0 (thetaIndex φ κ) := by
    rw [hΘ.continuousOn.image_Icc_of_monotoneOn hκ hΘ.strictMonoOn.monotoneOn, hΘ.map_zero]
  refine ⟨(hΘ.strictMonoOn.orderIso _ _).trans (OrderIso.setCongr _ _ himg), fun x => rfl,
    OrderIso.continuous _⟩

end AutoIp

end _def_theta_function
