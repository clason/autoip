/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._def_fun_calc
import AutoIp._part_1_funcanal._ch_09_functions_of_compact_operator._lem_sigma_bound

section _def_frac_power

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {K : E →L[𝕜] F} {ι : Type*} {σ : ι → ℝ} {v : ι → E} {u : ι → F}

/-- The fractional power `|K|^ν := φ(K*K)` with `φ(t) = t^{ν/2}`. The exponent may be `0`,
where the prose asks for `ν > 0`; `|K|^0` is then the identity. -/
public noncomputable def IsSingularSystem.absRpow (hs : IsSingularSystem K σ v u) (ν : ℝ)
    (hν : 0 ≤ ν) : E →L[𝕜] E :=
  hs.funCalc (fun t => t ^ (ν / 2)) (hs.exists_bound_rpow_sq (by linarith))

/-- The defining equation `|K|^ν = φ(K*K)` with `φ(t) = t^{ν/2}`. The boundedness of `φ` is an
argument because `φ(K*K)` takes it. -/
public theorem IsSingularSystem.absRpow_def (hs : IsSingularSystem K σ v u) (ν : ℝ) (hν : 0 ≤ ν)
    (hb : ∃ C, ∀ i, |(fun t : ℝ => t ^ (ν / 2)) (σ i ^ 2)| ≤ C) :
    hs.absRpow ν hν = hs.funCalc (fun t => t ^ (ν / 2)) hb := by
  -- The residual goal is the two boundedness proofs, not the body.
  unfold IsSingularSystem.absRpow
  rfl

end _def_frac_power
