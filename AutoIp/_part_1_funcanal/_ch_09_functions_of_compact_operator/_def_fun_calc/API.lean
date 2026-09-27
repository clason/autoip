/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_fun_calc.Spec
import all AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_fun_calc.Spec
import AutoIp._part_1_funcanal._ch_03_hilbert_spaces._lem_proj_characterisation
import AutoIp._part_1_funcanal._ch_04_orthonormal_series._lem_inner_through_series
import AutoIp._part_1_funcanal._ch_08_svd._lem_svd_companion
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound
import AutoIp.Auxiliary.BoundedOnIcc

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- The series part `φ(K*K) x - φ(0) P_{𝒩(K)} x` lies in `𝒩(K)ᗮ`. -/
public theorem IsSingularSystem.funCalc_sub_smul_starProjection_mem_orthogonal
    (hs : IsSingularSystem K σ v u) {φ : ℝ → ℝ} (hφ : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C) (x : E) :
    hs.funCalc φ hφ x
      - (φ 0 : 𝕜) • K.toLinearMap.ker.starProjection x
      ∈ (K.toLinearMap.ker)ᗮ := by
  refine (Submodule.isClosed_orthogonal _).mem_of_tendsto
    (hs.hasSum_funCalc_sub_starProjection hφ x) ?_
  exact Filter.Eventually.of_forall fun s =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hs.mem_orthogonal_ker i)

/-- `φ(K*K) = ψ(K*K)` if `φ` and `ψ` agree at `0` and at the squared singular values. -/
public theorem IsSingularSystem.funCalc_congr' (hs : IsSingularSystem K σ v u) {φ ψ : ℝ → ℝ}
    (hφ : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C) (hψ : ∃ C, ∀ i, |ψ (σ i ^ 2)| ≤ C)
    (h0 : φ 0 = ψ 0) (hval : ∀ i, φ (σ i ^ 2) = ψ (σ i ^ 2)) :
    hs.funCalc φ hφ = hs.funCalc ψ hψ := by
  ext x
  unfold IsSingularSystem.funCalc
  simp only [add_apply, FunLike.coe_smul, Pi.smul_apply, h0,
    LinearMap.mkContinuous_apply, IsSingularSystem.funCalcLinear]
  congr 1
  exact tsum_congr fun i => by rw [hval i]

/-- `φ(K*K) = ψ(K*K)` if `φ` and `ψ` agree on `[0, ‖K‖²]`. -/
public theorem IsSingularSystem.funCalc_congr (hs : IsSingularSystem K σ v u) {φ ψ : ℝ → ℝ}
    (hφ : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C) (hψ : ∃ C, ∀ i, |ψ (σ i ^ 2)| ≤ C)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), φ t = ψ t) :
    hs.funCalc φ hφ = hs.funCalc ψ hψ :=
  hs.funCalc_congr' hφ hψ (h 0 ⟨le_rfl, by positivity⟩) fun i => h _ (hs.sq_mem_Icc i)

/-- `φ(K*K) vᵢ = φ(σᵢ²) vᵢ`. -/
public theorem IsSingularSystem.funCalc_apply_v (hs : IsSingularSystem K σ v u) {φ : ℝ → ℝ}
    (hφ : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C) (i : ι) :
    hs.funCalc φ hφ (v i) = (φ (σ i ^ 2) : 𝕜) • v i := by
  classical
  have h := hs.hasSum_funCalc_sub_starProjection hφ (v i)
  have hp : (LinearMap.ker K.toLinearMap).starProjection (v i) = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact hs.mem_orthogonal_ker i
  rw [hp, smul_zero, sub_zero] at h
  have hij := (orthonormal_iff_ite (𝕜 := 𝕜)).1 hs.orthonormal_left
  have heq : ∀ j : ι,
      ((RCLike.ofReal (φ (σ j ^ 2)) : 𝕜) * inner 𝕜 (v j) (v i)) • v j
        = if j = i then (RCLike.ofReal (φ (σ i ^ 2)) : 𝕜) • v i else 0 := by
    intro j
    rw [hij j i]
    rcases eq_or_ne j i with rfl | hji
    · rw [ite_eq_left rfl, ite_eq_left rfl, mul_one]
    · rw [ite_eq_right hji, ite_eq_right hji, mul_zero, zero_smul]
  simp only [heq] at h
  exact h.unique (hasSum_ite_eq i ((RCLike.ofReal (φ (σ i ^ 2)) : 𝕜) • v i))

/-- The calculus of a real function is self-adjoint. -/
public theorem IsSingularSystem.isSelfAdjoint_funCalc (hs : IsSingularSystem K σ v u)
    {φ : ℝ → ℝ} (hφ : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C) :
    IsSelfAdjoint (hs.funCalc φ hφ) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  set c : 𝕜 := RCLike.ofReal (φ 0) with hc
  set P := (LinearMap.ker K.toLinearMap).starProjection with hP
  have hx := hs.hasSum_funCalc_sub_starProjection hφ x
  have hy := hs.hasSum_funCalc_sub_starProjection hφ y
  -- The inner product of the `x`-series with `y` and that of `x` with the `y`-series have
  -- equal terms.
  have hterm : ∀ i, (inner 𝕜 (((RCLike.ofReal (φ (σ i ^ 2)) : 𝕜) * inner 𝕜 (v i) x) • v i) y
      : 𝕜) = inner 𝕜 x (((RCLike.ofReal (φ (σ i ^ 2)) : 𝕜) * inner 𝕜 (v i) y) • v i) := by
    intro i
    rw [inner_smul_left, inner_smul_right, map_mul, RCLike.conj_ofReal, inner_conj_symm]
    ring
  have hser : (inner 𝕜 (hs.funCalc φ hφ x - c • P x) y : 𝕜)
      = inner 𝕜 x (hs.funCalc φ hφ y - c • P y) :=
    ((HasSum.inner_left hx y).congr_fun fun i => (hterm i).symm).unique
      (HasSum.inner_right hy x)
  -- The kernel term is a real multiple of an orthogonal projection, so symmetric.
  have hproj := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1
    (isSelfAdjoint_starProjection (LinearMap.ker K.toLinearMap))) x y
  have hker : (inner 𝕜 (c • P x) y : 𝕜) = inner 𝕜 x (c • P y) := by
    rw [inner_smul_left, inner_smul_right, hc, RCLike.conj_ofReal, hP]
    exact congrArg _ hproj
  rw [inner_sub_left, inner_sub_right] at hser
  linear_combination hser + hker

/-- The Fourier series of `x` against the left singular vectors sums to its component off `ker
K`. -/
public theorem IsSingularSystem.hasSum_sub_starProjection (hs : IsSingularSystem K σ v u) (x : E) :
    HasSum (fun i => (inner 𝕜 (v i) x : 𝕜) • v i)
      (x - K.toLinearMap.ker.starProjection x) := by
  have hsum : Summable (fun i => (inner 𝕜 (v i) x : 𝕜) • v i) := by
    rw [hs.orthonormal_left.summable_iff_norm_sq_summable]
    exact hs.orthonormal_left.inner_products_summable (x := x)
  set z := ∑' i, (inner 𝕜 (v i) x : 𝕜) • v i with hzdef
  have hz : HasSum (fun i => (inner 𝕜 (v i) x : 𝕜) • v i) z := hsum.hasSum
  have hzU : z ∈ (LinearMap.ker K.toLinearMap)ᗮ := by
    refine (Submodule.isClosed_orthogonal _).mem_of_tendsto hz ?_
    exact Filter.Eventually.of_forall fun s =>
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hs.mem_orthogonal_ker i)
  have hKz : K z = K x := by
    have h1 := hz.mapL K
    simp only [ContinuousLinearMap.map_smul, hs.map_left, smul_smul] at h1
    have h3 : (fun i => ((inner 𝕜 (v i) x : 𝕜) * (RCLike.ofReal (σ i) : 𝕜)) • u i)
        = fun i => ((RCLike.ofReal (σ i) : 𝕜) * inner 𝕜 (v i) x) • u i := by
      funext i; rw [mul_comm]
    rw [h3] at h1
    exact h1.unique (hs.hasSum x)
  have hzx : z - x ∈ LinearMap.ker K.toLinearMap := by
    simp [LinearMap.mem_ker, hKz]
  have hz' : z = x - (LinearMap.ker K.toLinearMap).starProjection x := by
    have h4 : z = (LinearMap.ker K.toLinearMap)ᗮ.starProjection x := by
      rw [Submodule.eq_starProjection_iff]
      exact ⟨hzU, by rw [Submodule.orthogonal_orthogonal]; exact hzx⟩
    rw [h4, Submodule.starProjection_orthogonal_val]
  exact hz' ▸ hz

/-- Off the kernel, the Fourier series against the left singular vectors sums to the
vector itself. -/
public theorem IsSingularSystem.hasSum_inner_smul (hs : IsSingularSystem K σ v u) {x : E}
    (hx : x ∈ (K.toLinearMap.ker)ᗮ) :
    HasSum (fun i => (inner 𝕜 (v i) x : 𝕜) • v i) x := by
  simpa [(Submodule.starProjection_apply_eq_zero_iff _).2 hx]
    using hs.hasSum_sub_starProjection x

/-- A function bounded on `[0, ‖K‖²]` is bounded at the squared singular values. -/
public theorem IsSingularSystem.exists_bound_sq (hs : IsSingularSystem K σ v u) {φ : ℝ → ℝ}
    (hφ : ∃ C, ∀ t ∈ Set.Icc (0 : ℝ) (‖K‖ ^ 2), |φ t| ≤ C) :
    ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C :=
  hφ.imp fun _ hC i => hC _ (hs.sq_mem_Icc i)

/-- Two functions bounded at the squares of a real family have a sum bounded there. -/
public theorem exists_forall_abs_add_sq_le
    {φ ψ : ℝ → ℝ} (hbφ : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C) (hbψ : ∃ C, ∀ i, |ψ (σ i ^ 2)| ≤ C) :
    ∃ C, ∀ i, |(φ + ψ) (σ i ^ 2)| ≤ C := by
  obtain ⟨Cφ, hCφ⟩ := hbφ
  obtain ⟨Cψ, hCψ⟩ := hbψ
  refine ⟨Cφ + Cψ, fun i => ?_⟩
  simp only [Pi.add_apply]
  calc |φ (σ i ^ 2) + ψ (σ i ^ 2)| ≤ |φ (σ i ^ 2)| + |ψ (σ i ^ 2)| := abs_add_le _ _
    _ ≤ Cφ + Cψ := add_le_add (hCφ i) (hCψ i)

/-- A function bounded at the squares of a real family has every scalar multiple bounded
there. -/
public theorem exists_forall_abs_smul_sq_le (c : ℝ)
    {φ : ℝ → ℝ} (hbφ : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C) :
    ∃ C, ∀ i, |(c • φ) (σ i ^ 2)| ≤ C := by
  obtain ⟨Cφ, hCφ⟩ := hbφ
  refine ⟨|c| * Cφ, fun i => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hCφ i) (abs_nonneg c)

/-- Two functions bounded at the squares of a real family have a difference bounded
there. -/
public theorem exists_forall_abs_sub_sq_le
    {φ ψ : ℝ → ℝ} (hbφ : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C) (hbψ : ∃ C, ∀ i, |ψ (σ i ^ 2)| ≤ C) :
    ∃ C, ∀ i, |(φ - ψ) (σ i ^ 2)| ≤ C := by
  obtain ⟨Cφ, hCφ⟩ := hbφ
  obtain ⟨Cψ, hCψ⟩ := hbψ
  refine ⟨Cφ + Cψ, fun i => ?_⟩
  simp only [Pi.sub_apply]
  calc |φ (σ i ^ 2) - ψ (σ i ^ 2)| ≤ |φ (σ i ^ 2)| + |ψ (σ i ^ 2)| := abs_sub _ _
    _ ≤ Cφ + Cψ := add_le_add (hCφ i) (hCψ i)

/-- Two functions bounded at the squares of a real family have a product bounded there. -/
public theorem exists_forall_abs_mul_sq_le
    {φ ψ : ℝ → ℝ} (hbφ : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C) (hbψ : ∃ C, ∀ i, |ψ (σ i ^ 2)| ≤ C) :
    ∃ C, ∀ i, |(φ * ψ) (σ i ^ 2)| ≤ C := by
  obtain ⟨Cφ, hCφ⟩ := hbφ
  obtain ⟨Cψ, hCψ⟩ := hbψ
  refine ⟨Cφ * Cψ, fun i => ?_⟩
  rw [Pi.mul_apply, abs_mul]
  exact mul_le_mul (hCφ i) (hCψ i) (abs_nonneg _) (le_trans (abs_nonneg _) (hCφ i))

/-- `(φ + ψ)(K*K) = φ(K*K) + ψ(K*K)` for `φ`, `ψ` bounded at the squared singular values. -/
public theorem IsSingularSystem.funCalc_add' (hs : IsSingularSystem K σ v u) {φ ψ : ℝ → ℝ}
    (hbφ : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C) (hbψ : ∃ C, ∀ i, |ψ (σ i ^ 2)| ≤ C) :
    hs.funCalc (φ + ψ) (exists_forall_abs_add_sq_le hbφ hbψ)
      = hs.funCalc φ hbφ + hs.funCalc ψ hbψ := by
  set hbs := exists_forall_abs_add_sq_le hbφ hbψ with hbs_def
  clear_value hbs
  ext x
  have h1 := hs.hasSum_funCalc_sub_starProjection hbφ x
  have h2 := hs.hasSum_funCalc_sub_starProjection hbψ x
  have h3 := hs.hasSum_funCalc_sub_starProjection hbs x
  have h4 := h1.add h2
  have hfun : (fun i => ((RCLike.ofReal (φ (σ i ^ 2)) : 𝕜) * inner 𝕜 (v i) x) • v i
        + ((RCLike.ofReal (ψ (σ i ^ 2)) : 𝕜) * inner 𝕜 (v i) x) • v i)
      = fun i => ((RCLike.ofReal ((φ + ψ) (σ i ^ 2)) : 𝕜) * inner 𝕜 (v i) x) • v i := by
    funext i
    rw [Pi.add_apply, RCLike.ofReal_add, add_mul, add_smul]
  rw [hfun] at h4
  have h5 := h3.unique h4
  have h6 : (RCLike.ofReal ((φ + ψ) 0) : 𝕜) = RCLike.ofReal (φ 0) + RCLike.ofReal (ψ 0) := by
    rw [Pi.add_apply, RCLike.ofReal_add]
  rw [h6, add_smul] at h5
  simp only [add_apply]
  have h7 : hs.funCalc (φ + ψ) hbs x
      - ((RCLike.ofReal (φ 0) : 𝕜) • (LinearMap.ker K.toLinearMap).starProjection x
        + (RCLike.ofReal (ψ 0) : 𝕜) • (LinearMap.ker K.toLinearMap).starProjection x)
      = (hs.funCalc φ hbφ x + hs.funCalc ψ hbψ x)
      - ((RCLike.ofReal (φ 0) : 𝕜) • (LinearMap.ker K.toLinearMap).starProjection x
        + (RCLike.ofReal (ψ 0) : 𝕜) • (LinearMap.ker K.toLinearMap).starProjection x) := by
    rw [h5]; abel
  exact sub_left_injective h7

/-- `(c φ)(K*K) = c φ(K*K)` for `φ` bounded at the squared singular values. -/
public theorem IsSingularSystem.funCalc_smul' (hs : IsSingularSystem K σ v u) (c : ℝ) {φ : ℝ → ℝ}
    (hbφ : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C) :
    hs.funCalc (c • φ) (exists_forall_abs_smul_sq_le c hbφ)
      = (c : 𝕜) • hs.funCalc φ hbφ := by
  set hbs := exists_forall_abs_smul_sq_le c hbφ with hbs_def
  clear_value hbs
  ext x
  have h1 := hs.hasSum_funCalc_sub_starProjection hbφ x
  have h3 := hs.hasSum_funCalc_sub_starProjection hbs x
  have h4 := h1.const_smul (RCLike.ofReal c : 𝕜)
  have hfun : (fun i => (RCLike.ofReal c : 𝕜) •
        (((RCLike.ofReal (φ (σ i ^ 2)) : 𝕜) * inner 𝕜 (v i) x) • v i))
      = fun i => ((RCLike.ofReal ((c • φ) (σ i ^ 2)) : 𝕜) * inner 𝕜 (v i) x) • v i := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul, RCLike.ofReal_mul, smul_smul, mul_assoc]
  rw [hfun] at h4
  have h5 := h3.unique h4
  have h6 : (RCLike.ofReal ((c • φ) 0) : 𝕜) = RCLike.ofReal c * RCLike.ofReal (φ 0) := by
    rw [Pi.smul_apply, smul_eq_mul, RCLike.ofReal_mul]
  rw [h6, smul_sub, smul_smul] at h5
  simp only [FunLike.coe_smul, Pi.smul_apply]
  have h7 : hs.funCalc (c • φ) hbs x
      - (RCLike.ofReal c * RCLike.ofReal (φ 0) : 𝕜)
        • (LinearMap.ker K.toLinearMap).starProjection x
      = (RCLike.ofReal c : 𝕜) • hs.funCalc φ hbφ x
      - (RCLike.ofReal c * RCLike.ofReal (φ 0) : 𝕜)
        • (LinearMap.ker K.toLinearMap).starProjection x := by
    rw [h5]
  exact sub_left_injective h7

/-- `(φ ψ)(K*K) = φ(K*K) ∘ ψ(K*K)` for `φ`, `ψ` bounded at the squared singular values. -/
public theorem IsSingularSystem.funCalc_mul' (hs : IsSingularSystem K σ v u) {φ ψ : ℝ → ℝ}
    (hbφ : ∃ C, ∀ i, |φ (σ i ^ 2)| ≤ C) (hbψ : ∃ C, ∀ i, |ψ (σ i ^ 2)| ≤ C) :
    hs.funCalc (φ * ψ) (exists_forall_abs_mul_sq_le hbφ hbψ)
      = hs.funCalc φ hbφ ∘L hs.funCalc ψ hbψ := by
  set hbs := exists_forall_abs_mul_sq_le hbφ hbψ with hbs_def
  clear_value hbs
  have hPv : ∀ i, (LinearMap.ker K.toLinearMap).starProjection (v i) = 0 := fun i =>
    (Submodule.starProjection_apply_eq_zero_iff _).mpr (hs.mem_orthogonal_ker i)
  ext x
  have h2 := hs.hasSum_funCalc_sub_starProjection hbψ x
  have hSmem := hs.funCalc_sub_smul_starProjection_mem_orthogonal hbψ x
  have hzero : ∀ i, (inner 𝕜 (v i)
      ((LinearMap.ker K.toLinearMap).starProjection x) : 𝕜) = 0 := fun i => by
    rw [← Submodule.inner_starProjection_left_eq_right, hPv i, inner_zero_left]
  have hcoef : ∀ i, (inner 𝕜 (v i) (hs.funCalc ψ hbψ x) : 𝕜)
      = (RCLike.ofReal (ψ (σ i ^ 2)) : 𝕜) * inner 𝕜 (v i) x := fun i => by
    have h := hs.orthonormal_left.inner_right_of_hasSum h2 i
    rw [inner_sub_right, inner_smul_right, hzero i, mul_zero, sub_zero] at h
    exact h
  have hPy : (LinearMap.ker K.toLinearMap).starProjection (hs.funCalc ψ hbψ x)
      = (RCLike.ofReal (ψ 0) : 𝕜) • (LinearMap.ker K.toLinearMap).starProjection x := by
    have h1 : (LinearMap.ker K.toLinearMap).starProjection (hs.funCalc ψ hbψ x
        - (RCLike.ofReal (ψ 0) : 𝕜)
          • (LinearMap.ker K.toLinearMap).starProjection x) = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff _).mpr hSmem
    rw [map_sub, map_smul, Submodule.starProjection_eq_self_iff.mpr
      ((LinearMap.ker K.toLinearMap).starProjection_apply_mem x)] at h1
    exact sub_eq_zero.mp h1
  have h1 := hs.hasSum_funCalc_sub_starProjection hbφ (hs.funCalc ψ hbψ x)
  have h3 := hs.hasSum_funCalc_sub_starProjection hbs x
  have hfun : (fun i => ((RCLike.ofReal (φ (σ i ^ 2)) : 𝕜)
        * inner 𝕜 (v i) (hs.funCalc ψ hbψ x)) • v i)
      = fun i => ((RCLike.ofReal ((φ * ψ) (σ i ^ 2)) : 𝕜) * inner 𝕜 (v i) x) • v i := by
    funext i
    rw [hcoef i, Pi.mul_apply, RCLike.ofReal_mul, mul_assoc]
  rw [hfun, hPy, smul_smul] at h1
  have h6 : (RCLike.ofReal ((φ * ψ) 0) : 𝕜) = RCLike.ofReal (φ 0) * RCLike.ofReal (ψ 0) := by
    rw [Pi.mul_apply, RCLike.ofReal_mul]
  have h5 := h3.unique h1
  rw [h6] at h5
  simpa only [ContinuousLinearMap.comp_apply] using sub_left_injective h5
