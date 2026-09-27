/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Order.AtTopBotIxx

/-!
# A diagonal operator on `ℓ²`

The diagonal operator on `ℓ²(ℕ, ℝ)` with weights `1/(n + 1)`: compact and injective, with
dense, non-closed, infinite-dimensional range, and diagonalised by the unit vectors. Also a
datum outside its Moore--Penrose domain, the non-compactness of the identity of `ℓ²`, and facts
about vectors of `ℓ²` through their coordinates.
-/

namespace Witnesses.Diagonal

open Filter Topology
open scoped InnerProductSpace ENNReal

/-- The sequence space `ℓ²(ℕ, ℝ)`. -/
public abbrev H : Type := lp (fun _ : ℕ => ℝ) 2

-- The `lp` API states its facts with the exponent `(2 : ℝ≥0∞).toReal` and real powers; the
-- three below restate the ones used here once, with squares.

/-- A sequence lies in `ℓ²` exactly when its squares are summable. -/
public theorem memℓp_two_iff {x : ℕ → ℝ} : Memℓp x 2 ↔ Summable fun n => ‖x n‖ ^ 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]

/-- A bound on every finite sum of squares of coordinates bounds the norm. -/
public theorem norm_le_of_forall_sum_sq_le {x : H} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ s : Finset ℕ, ∑ i ∈ s, ‖x i‖ ^ 2 ≤ C ^ 2) : ‖x‖ ≤ C :=
  lp.norm_le_of_forall_sum_le (by norm_num) hC fun s => by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h s

/-- A finite sum of squares of coordinates is at most the square of the norm. -/
public theorem sum_sq_le_norm_sq (x : H) (s : Finset ℕ) : ∑ i ∈ s, ‖x i‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) x s

/-- The diagonal weights `1/(n+1)`. -/
public noncomputable def w (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

public theorem w_def (n : ℕ) : w n = ((n : ℝ) + 1)⁻¹ := by rfl

public theorem w_pos (n : ℕ) : 0 < w n := by
  have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  simpa [w] using inv_pos.2 this

public theorem w_le_one (n : ℕ) : w n ≤ 1 := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  simpa [w] using inv_le_one_of_one_le₀ h1

/-- The weights are non-increasing. -/
public theorem w_antitone : Antitone w := by
  intro m n hmn
  rw [w_def, w_def]
  have : (m : ℝ) ≤ n := by exact_mod_cast hmn
  gcongr

public theorem tendsto_w : Tendsto w atTop (𝓝 0) := by
  have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  rw [show w = fun n : ℕ => ((n : ℝ) + 1)⁻¹ from funext w_def]
  simpa [one_div] using this

/-- Scaling by the weights keeps a square-summable sequence square-summable. -/
theorem memℓp_smul {x : ℕ → ℝ} (hx : Memℓp x 2) : Memℓp (fun n => w n * x n) 2 := by
  rw [memℓp_two_iff] at hx ⊢
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hx
  have hle : ‖w n * x n‖ ≤ ‖x n‖ := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (w_pos n)]
    calc w n * ‖x n‖ ≤ 1 * ‖x n‖ := by
          exact mul_le_mul_of_nonneg_right (w_le_one n) (norm_nonneg _)
      _ = ‖x n‖ := one_mul _
  gcongr

/-- The diagonal operator, as a linear map. -/
noncomputable def Tlin : H →ₗ[ℝ] H where
  toFun x := ⟨fun n => w n * x n, memℓp_smul (lp.memℓp x)⟩
  map_add' x y := by
    refine lp.ext (funext fun n => ?_)
    simp only [Pi.add_apply, lp.coeFn_add]
    ring
  map_smul' c x := by
    refine lp.ext (funext fun n => ?_)
    simp only [Pi.smul_apply, lp.coeFn_smul, RingHom.id_apply, smul_eq_mul]
    ring

@[simp]
theorem Tlin_apply (x : H) (n : ℕ) : (Tlin x) n = w n * x n := by
  rfl

/-- The diagonal operator on `ℓ²`, of norm at most one. -/
public noncomputable def T : H →L[ℝ] H :=
  Tlin.mkContinuous 1 fun x => by
    rw [one_mul]
    refine lp.norm_mono (p := 2) (by norm_num) fun n => ?_
    rw [Tlin_apply, norm_mul, Real.norm_eq_abs, abs_of_pos (w_pos n)]
    calc w n * ‖x n‖ ≤ 1 * ‖x n‖ :=
          mul_le_mul_of_nonneg_right (w_le_one n) (norm_nonneg _)
      _ = ‖x n‖ := one_mul _

@[simp]
public theorem T_apply (x : H) (n : ℕ) : (T x) n = w n * x n := by
  rfl

/-- The weights are square-summable. -/
public theorem summable_w_sq : Summable fun n : ℕ => (w n) ^ 2 := by
  have hbase : Summable fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ :=
    Real.summable_nat_pow_inv.2 one_lt_two
  have hshift := (summable_nat_add_iff 1).2 hbase
  refine hshift.congr fun n => ?_
  have : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
  rw [this, w]
  rw [inv_pow]

public theorem memℓp_w : Memℓp w 2 := by
  rw [memℓp_two_iff]
  refine summable_w_sq.congr fun n => ?_
  rw [Real.norm_eq_abs, abs_of_pos (w_pos n)]

/-- The weights, as a vector of `ℓ²`. -/
@[expose]
public noncomputable def y : H := ⟨w, memℓp_w⟩

@[simp]
public theorem y_apply (n : ℕ) : (y : ℕ → ℝ) n = w n := rfl

/-- The diagonal operator is injective. -/
public theorem injective_T : Function.Injective T := by
  intro a b hab
  refine lp.ext (funext fun n => ?_)
  have h := congrArg (fun z : H => (z : ℕ → ℝ) n) hab
  simp only [T_apply] at h
  exact mul_left_cancel₀ (w_pos n).ne' h

/-- The constant sequence `1` is not square-summable. -/
theorem not_summable_one : ¬ Summable fun _ : ℕ => (1 : ℝ) := by
  intro h
  have := h.tendsto_atTop_zero
  have h0 : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds this
  exact one_ne_zero h0

/-- The weight vector is not in the range of the diagonal operator. -/
theorem notMem_range_y : y ∉ LinearMap.range (T : H →ₗ[ℝ] H) := by
  rintro ⟨x, hx⟩
  have hone : ∀ n, (x : ℕ → ℝ) n = 1 := by
    intro n
    have h := congrArg (fun z : H => (z : ℕ → ℝ) n) hx
    simp only [y_apply] at h
    exact mul_left_cancel₀ (w_pos n).ne' (h.trans (mul_one (w n)).symm)
  have hsum := memℓp_two_iff.1 (lp.memℓp x)
  refine not_summable_one (hsum.congr fun n => ?_)
  rw [hone n]
  norm_num

/-- The diagonal operator sends each unit vector to its weight times itself. -/
public theorem T_single (n : ℕ) :
    T (lp.single 2 n (1 : ℝ)) = lp.single 2 n (w n) := by
  refine lp.ext (funext fun m => ?_)
  rw [T_apply]
  by_cases hm : m = n
  · subst hm
    rw [lp.single_apply_self, lp.single_apply_self, mul_one]
  · rw [lp.single_apply_ne _ _ _ hm, lp.single_apply_ne _ _ _ hm, mul_zero]

/-- The orthogonal complement of the range of the diagonal operator is trivial. -/
public theorem orthogonal_range_eq_bot :
    (LinearMap.range (T : H →ₗ[ℝ] H))ᗮ = ⊥ := by
  classical
  refine Submodule.eq_bot_iff _ |>.2 fun z hz => ?_
  refine lp.ext (funext fun n => ?_)
  have h0 : (inner ℝ (T (lp.single 2 n (1 : ℝ))) z : ℝ) = 0 :=
    hz _ ⟨lp.single 2 n (1 : ℝ), rfl⟩
  rw [T_single, lp.inner_single_left] at h0
  have hsplit : (z : ℕ → ℝ) n = 0 ∨ w n = 0 := by simpa using h0
  simpa using hsplit.resolve_right (w_pos n).ne'

/-- The sum of the range of the diagonal operator and its orthogonal complement is the range. -/
public theorem sup_orthogonal_range_eq :
    LinearMap.range (T : H →ₗ[ℝ] H) ⊔ (LinearMap.range (T : H →ₗ[ℝ] H))ᗮ
      = LinearMap.range (T : H →ₗ[ℝ] H) := by
  rw [orthogonal_range_eq_bot, sup_bot_eq]

/-- The weight vector lies outside the sum of the range of the diagonal operator and its
orthogonal complement. -/
public theorem notMem_sup_orthogonal_range :
    y ∉ LinearMap.range (T : H →ₗ[ℝ] H) ⊔ (LinearMap.range (T : H →ₗ[ℝ] H))ᗮ := by
  rw [sup_orthogonal_range_eq]
  exact notMem_range_y

/-- The range of the diagonal operator is not all of `ℓ²`. -/
theorem range_ne_top : LinearMap.range (T : H →ₗ[ℝ] H) ≠ ⊤ := fun h =>
  notMem_range_y (h ▸ Submodule.mem_top)

/-- The range of the diagonal operator is not closed. -/
public theorem not_isClosed_range :
    ¬ IsClosed (LinearMap.range (T : H →ₗ[ℝ] H) : Set H) := by
  intro hclosed
  have hsup : LinearMap.range (T : H →ₗ[ℝ] H)
      ⊔ (LinearMap.range (T : H →ₗ[ℝ] H))ᗮ = ⊤ :=
    Submodule.sup_orthogonal_of_hasOrthogonalProjection
  rw [sup_orthogonal_range_eq] at hsup
  exact range_ne_top hsup

/-- The space `ℓ²` is infinite-dimensional. -/
theorem not_finiteDimensional : ¬ FiniteDimensional ℝ H := by
  intro h
  exact not_isClosed_range
    (LinearMap.range (T : H →ₗ[ℝ] H)).closed_of_finiteDimensional

/-- The range of the diagonal operator is infinite-dimensional. -/
public theorem not_finiteDimensional_range :
    ¬ FiniteDimensional ℝ (LinearMap.range (T : H →ₗ[ℝ] H)) := by
  intro h
  exact not_isClosed_range
    (LinearMap.range (T : H →ₗ[ℝ] H)).closed_of_finiteDimensional

/-- The weight vector is not zero. -/
theorem y_ne_zero : y ≠ 0 := by
  intro h
  have h0 : (y : ℕ → ℝ) 0 = (0 : H) 0 := by rw [h]
  rw [y_apply] at h0
  simp [w] at h0

public theorem norm_y_ne_zero : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 y_ne_zero

/-- The identity of `ℓ²` is not a compact operator. -/
theorem not_isCompactOperator_id :
    ¬ IsCompactOperator (id : H → H) := fun h =>
  not_finiteDimensional (FiniteDimensional.of_isCompactOperator_id h)

/-- The identity of `ℓ²`, as a continuous linear map, is not compact. -/
public theorem not_isCompactOperator_one :
    ¬ IsCompactOperator ((1 : H →L[ℝ] H) : H → H) := by
  intro h
  exact not_isCompactOperator_id h

/-! ### The unit vectors -/

/-- The `n`-th unit vector of `ℓ²`. -/
public noncomputable def e (n : ℕ) : H := lp.single 2 n (1 : ℝ)

public theorem e_def (n : ℕ) : e n = lp.single 2 n (1 : ℝ) := by rfl

public theorem e_apply (n m : ℕ) : (e n : ℕ → ℝ) m = if m = n then 1 else 0 := by
  simp only [e, lp.single_apply, Pi.single_apply]

/-- Pairing with a unit vector reads off a coordinate. -/
public theorem inner_e_left (n : ℕ) (x : H) : ⟪e n, x⟫_ℝ = x n := by
  rw [e, lp.inner_single_left]
  simp

theorem inner_e_right (n : ℕ) (x : H) : ⟪x, e n⟫_ℝ = x n := by
  rw [real_inner_comm, inner_e_left]

public theorem norm_e (n : ℕ) : ‖e n‖ = 1 := by
  rw [e, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  simp

theorem e_ne_zero (n : ℕ) : e n ≠ 0 := by
  intro h
  have := norm_e n
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- The unit vectors are the vectors of the standard Hilbert basis of `ℓ²`. -/
theorem coe_default_hilbertBasis :
    ⇑(default : HilbertBasis ℕ ℝ H) = e := by
  funext n
  exact (HilbertBasis.repr_symm_single (default : HilbertBasis ℕ ℝ H) n).symm

public theorem orthonormal_e : Orthonormal ℝ e := by
  rw [← coe_default_hilbertBasis]
  exact HilbertBasis.orthonormal _

public theorem span_e_dense : (Submodule.span ℝ (Set.range e)).topologicalClosure = ⊤ := by
  rw [← coe_default_hilbertBasis]
  exact HilbertBasis.dense_span _

/-- The unit vectors converge weakly to zero. -/
public theorem tendsto_dual_e (f : StrongDual ℝ H) :
    Tendsto (fun n => f (e n)) atTop (𝓝 0) := by
  set z : H := (InnerProductSpace.toDual ℝ H).symm f
  have hf : ∀ n, f (e n) = z n := fun n => by
    rw [← InnerProductSpace.toDual_symm_apply, inner_e_right]
  simp_rw [hf]
  have hsum := memℓp_two_iff.1 (lp.memℓp z)
  have h2 : Tendsto (fun n => ‖z n‖ ^ 2) atTop (𝓝 0) := hsum.tendsto_atTop_zero
  have h3 : Tendsto (fun n => Real.sqrt (‖z n‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp h2
  rw [Real.sqrt_zero] at h3
  have h4 : ∀ n, Real.sqrt (‖z n‖ ^ 2) = ‖z n‖ := fun n => Real.sqrt_sq (norm_nonneg _)
  simp_rw [h4] at h3
  exact tendsto_zero_iff_norm_tendsto_zero.2 h3

/-- A vector given as a sum along the unit vectors has the coefficients as coordinates. -/
public theorem apply_of_hasSum {c : ℕ → ℝ} {x : H} (h : HasSum (fun i => c i • e i) x)
    (n : ℕ) : x n = c n := by
  classical
  have h2 := h.mapL (innerSL ℝ (e n))
  simp only [map_smul, innerSL_apply_apply] at h2
  have hfun : (fun i => c i • ⟪e n, e i⟫_ℝ) = fun i => if i = n then c n else 0 := by
    funext i
    rw [orthonormal_iff_ite.1 orthonormal_e n i]
    by_cases hi : i = n
    · subst hi; simp
    · simp [hi, Ne.symm hi]
  have h3 : HasSum (fun i => c i • ⟪e n, e i⟫_ℝ) (c n) := by
    rw [hfun]; exact hasSum_ite_eq n (c n)
  rw [← inner_e_left]
  exact h2.unique h3

/-- Coordinatewise domination gives domination of the norms. -/
public theorem norm_le_of_abs_le {x y : H} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n, |x n| ≤ C * |y n|) : ‖x‖ ≤ C * ‖y‖ := by
  refine norm_le_of_forall_sum_sq_le (by positivity) fun s => ?_
  have hpt : ∀ n, ‖x n‖ ^ 2 ≤ C ^ 2 * ‖y n‖ ^ 2 := by
    intro n
    rw [← mul_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact h n
  calc ∑ i ∈ s, ‖x i‖ ^ 2
      ≤ ∑ i ∈ s, C ^ 2 * ‖y i‖ ^ 2 := Finset.sum_le_sum fun i _ => hpt i
    _ = C ^ 2 * ∑ i ∈ s, ‖y i‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ C ^ 2 * ‖y‖ ^ 2 := mul_le_mul_of_nonneg_left (sum_sq_le_norm_sq y s) (by positivity)
    _ = (C * ‖y‖) ^ 2 := (mul_pow _ _ _).symm

/-! ### The diagonal operator on the unit vectors -/

/-- The diagonal operator sends each unit vector to its weight times itself. -/
public theorem T_e (n : ℕ) : T (e n) = w n • e n := by
  refine lp.ext (funext fun m => ?_)
  rw [T_apply, lp.coeFn_smul, Pi.smul_apply, e_apply, smul_eq_mul]
  split_ifs with h
  · subst h; ring
  · ring

/-- The adjoint of the diagonal operator sends each unit vector to its weight times itself. -/
public theorem adjoint_T_e (n : ℕ) : ContinuousLinearMap.adjoint T (e n) = w n • e n := by
  refine ext_inner_right ℝ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, inner_e_left, T_apply,
    real_inner_smul_left, inner_e_left]

/-- Each weight lies in the spectrum of the diagonal operator. -/
public theorem mem_spectrum_T (n : ℕ) : w n ∈ spectrum ℝ T := by
  rw [spectrum.mem_iff]
  rintro ⟨u, hu⟩
  have h0 : (u : H →L[ℝ] H) (e n) = 0 := by
    rw [hu, Algebra.algebraMap_eq_smul_one, sub_apply,
      smul_apply, one_apply_eq_self, T_e, sub_self]
  have h1 : (↑u⁻¹ * ↑u : H →L[ℝ] H) (e n) = e n := by
    rw [Units.inv_mul, one_apply_eq_self]
  rw [mul_apply_eq_comp, h0, map_zero] at h1
  exact e_ne_zero n h1.symm

/-- The kernel of the diagonal operator is trivial. -/
public theorem ker_T : LinearMap.ker (T : H →ₗ[ℝ] H) = ⊥ :=
  LinearMap.ker_eq_bot.2 injective_T

/-- The range of the diagonal operator is dense. -/
public theorem topologicalClosure_range_T :
    (LinearMap.range (T : H →ₗ[ℝ] H)).topologicalClosure = ⊤ := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, orthogonal_range_eq_bot,
    Submodule.bot_orthogonal_eq_top]

/-! ### Compactness -/

/-- The truncation of the diagonal operator to the first `N` coordinates. -/
noncomputable def trunc (N : ℕ) : H →L[ℝ] H :=
  ∑ n ∈ Finset.range N,
    w n • ((ContinuousLinearMap.toSpanSingleton ℝ (e n)).comp (innerSL ℝ (e n)))

theorem isCompactOperator_trunc (N : ℕ) : IsCompactOperator (trunc N) := by
  unfold trunc
  induction N with
  | zero => simpa using (isCompactOperator_zero : IsCompactOperator (0 : H → H))
  | succ N ih =>
    rw [Finset.sum_range_succ, FunLike.coe_add]
    refine ih.add ?_
    rw [FunLike.coe_smul]
    refine IsCompactOperator.smul ?_ _
    rw [ContinuousLinearMap.coe_comp]
    exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL ℝ (e N))).clm_comp _

theorem trunc_apply (N : ℕ) (x : H) (m : ℕ) :
    (trunc N x : ℕ → ℝ) m = if m < N then w m * x m else 0 := by
  unfold trunc
  simp only [FunLike.coe_sum, Finset.sum_apply, lp.coeFn_sum,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, innerSL_apply_apply, ContinuousLinearMap.toSpanSingleton_apply,
    lp.coeFn_smul, inner_e_left, e_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_range]

theorem norm_sub_trunc_le (N : ℕ) : ‖T - trunc N‖ ≤ w N := by
  refine ContinuousLinearMap.opNorm_le_bound _ (w_pos N).le fun x => ?_
  rw [← abs_of_pos (w_pos N), ← Real.norm_eq_abs, ← norm_smul]
  refine lp.norm_mono (p := 2) (by norm_num) fun m => ?_
  rw [sub_apply, lp.coeFn_sub, Pi.sub_apply, T_apply, trunc_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, norm_mul]
  split_ifs with h
  · rw [sub_self, norm_zero]; positivity
  · rw [sub_zero, norm_mul]
    gcongr
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (w_pos _), abs_of_pos (w_pos _)]
    exact w_antitone (not_lt.1 h)

theorem tendsto_trunc : Tendsto trunc atTop (𝓝 T) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) tendsto_w
  rw [norm_sub_rev]
  exact norm_sub_trunc_le N

/-- The diagonal operator is compact. -/
public theorem isCompactOperator_T : IsCompactOperator T :=
  isCompactOperator_of_tendsto tendsto_trunc (Eventually.of_forall isCompactOperator_trunc)

/-! ### A limit of powers -/

/-- A positive power of a positive level tends to zero as the level decreases to zero. -/
public theorem tendsto_rpow_atBot {p : ℝ} (hp : 0 < p) :
    Tendsto (fun δ : Set.Ioi (0 : ℝ) => (δ : ℝ) ^ p) atBot (𝓝 0) := by
  refine (tendsto_comp_coe_Ioi_atBot (f := fun t : ℝ => t ^ p)).2 ?_
  have h := (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto
  rw [Real.zero_rpow hp.ne'] at h
  exact h.mono_left nhdsWithin_le_nhds

end Witnesses.Diagonal
