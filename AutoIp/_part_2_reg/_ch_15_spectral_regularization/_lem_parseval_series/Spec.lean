/-
Copyright (c) 2026 Tapio Helin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tapio Helin, Lauri Oksanen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal
import AutoIp._part_1_funcanal._ch_04_orthonormal_series._lem_riesz_fischer

section _lem_parseval_series

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*}

/-- Parseval identity for orthonormal series: for an orthonormal system `{e_n}_{n ∈ I}` in a
Hilbert space `H` and scalars `{c_n}` with `∑ |c_n|² < ∞`, the series `z := ∑ c_n e_n`
converges in `H`, `‖z‖² = ∑ |c_n|²` and `⟨e_m, z⟩ = c_m` for every `m ∈ I`. -/
public theorem Orthonormal.exists_hasSum_of_summable_norm_sq [CompleteSpace E] {e : ι → E}
    (he : Orthonormal 𝕜 e) {c : ι → 𝕜} (hc : Summable fun n => ‖c n‖ ^ 2) :
    ∃ z : E, HasSum (fun n => c n • e n) z ∧ ‖z‖ ^ 2 = ∑' n, ‖c n‖ ^ 2 ∧
      ∀ m, (inner 𝕜 (e m) z : 𝕜) = c m := by
  obtain ⟨z, hz⟩ := (he.summable_iff_norm_sq_summable c).mpr hc
  exact ⟨z, hz, he.norm_sq_eq_tsum_norm_sq hz, fun m => he.inner_right_of_hasSum hz m⟩

end _lem_parseval_series
