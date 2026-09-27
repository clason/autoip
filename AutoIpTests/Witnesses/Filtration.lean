/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# A filtration of `ℓ²` by finite-dimensional subspaces

The spans of the first `n` vectors of the standard Hilbert basis of `ℓ²(ℕ, ℝ)`: nested, of
dimension `n`, with dense union. Also the rank-one operator from the line to `ℓ²` onto the span
of the first basis vector, and its adjoint.
-/

namespace Witnesses.Filtration

open scoped InnerProductSpace

/-- The sequence space `ℓ²(ℕ, ℝ)`. -/
public abbrev H : Type := lp (fun _ : ℕ => ℝ) 2

/-- The standard Hilbert basis of `ℓ²`. -/
@[expose]
public noncomputable def b : HilbertBasis ℕ ℝ H := default

/-- The span of the first `n` basis vectors. -/
@[expose]
public noncomputable def X (n : ℕ) : Submodule ℝ H :=
  Submodule.span ℝ (Set.range fun i : Fin n => b i)

public instance instFiniteDimensional (n : ℕ) : FiniteDimensional ℝ (X n) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

public instance instHasOrthogonalProjection (n : ℕ) : (X n).HasOrthogonalProjection :=
  inferInstance

/-- The subspaces are nested. -/
public theorem mono : Monotone X := by
  intro m n hmn
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨i, lt_of_lt_of_le i.2 hmn⟩, rfl⟩

/-- The span of the first `n` basis vectors has dimension `n`. -/
public theorem finrank_X (n : ℕ) : Module.finrank ℝ (X n) = n := by
  have hli : LinearIndependent ℝ (fun i : Fin n => b i) :=
    (b.orthonormal.comp _ (Fin.val_injective)).linearIndependent
  rw [X, finrank_span_eq_card hli, Fintype.card_fin]

/-- The first basis vector lies in the span of the first `n` basis vectors when `0 < n`. -/
public theorem b_zero_mem {n : ℕ} (hn : 0 < n) : b 0 ∈ X n :=
  Submodule.subset_span ⟨⟨0, hn⟩, rfl⟩

/-- The union of the spans is dense. -/
public theorem dense : (⨆ n, X n).topologicalClosure = ⊤ := by
  have h : (⨆ n, X n) = Submodule.span ℝ (Set.range b) := by
    rw [show X = fun n => Submodule.span ℝ (Set.range fun i : Fin n => b i) from rfl,
      Submodule.iSup_span]
    congr 1
    ext x
    simp only [Set.mem_iUnion, Set.mem_range]
    constructor
    · rintro ⟨n, i, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i + 1, ⟨i, Nat.lt_succ_self i⟩, rfl⟩
  rw [h]
  exact b.dense_span

/-- The span of the first `n` basis vectors is not the zero subspace when `0 < n`. -/
public theorem X_ne_bot {n : ℕ} (hn : 0 < n) : X n ≠ ⊥ := by
  intro h
  have h0 : b 0 ∈ (⊥ : Submodule ℝ H) := h ▸ b_zero_mem hn
  exact (b.orthonormal.ne_zero 0) ((Submodule.mem_bot ℝ).1 h0)

/-- The rank-one operator from the line to `ℓ²` sending `r` to `r` times the first basis vector. -/
@[expose]
public noncomputable def K : ℝ →L[ℝ] H := ContinuousLinearMap.toSpanSingleton ℝ (b 0)

public theorem K_apply (r : ℝ) : K r = r • b 0 := by
  rw [K, ContinuousLinearMap.toSpanSingleton_apply]

/-- The adjoint of the rank-one operator is the inner product against the first basis vector. -/
public theorem adjoint_K_apply (h : H) : ContinuousLinearMap.adjoint K h = ⟪b 0, h⟫_ℝ := by
  rw [K, ContinuousLinearMap.adjoint_toSpanSingleton]
  rfl

/-- The first basis vector is a unit vector. -/
public theorem inner_b_zero_self : ⟪b 0, b 0⟫_ℝ = 1 :=
  real_inner_self_eq_norm_sq (b 0) ▸ by rw [b.orthonormal.1 0]; norm_num

end Witnesses.Filtration
