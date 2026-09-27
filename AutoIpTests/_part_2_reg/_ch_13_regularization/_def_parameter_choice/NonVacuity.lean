module

import AutoIp._part_2_reg._ch_13_regularization._def_parameter_choice.Spec -- shake: keep

open Filter Topology

/-- The hypotheses of `AutoIp.ParameterChoice.scale` can hold together. -/
theorem AutoIp.ParameterChoice.scale_satisfiable : ∃ (F : Type), ∃ (a : AutoIp.ParameterChoice F), ∃ (τ : ℝ), (0 : ℝ) < τ :=
  by
  refine ⟨Empty, ⟨fun _ _ => 1, fun _ _ => one_pos⟩, 1, ?_⟩
  exact by norm_num

/-- The hypotheses of `AutoIp.ParameterChoice.scale` can fail. -/
theorem AutoIp.ParameterChoice.scale_nontrivial : ∃ (F : Type), ∃ (a : AutoIp.ParameterChoice F), ∃ (τ : ℝ), ¬ ((0 : ℝ) < τ) :=
  by
  refine ⟨Empty, ⟨fun _ _ => 1, fun _ _ => one_pos⟩, 0, ?_⟩
  intro H
  exact absurd H (lt_irrefl 0)
