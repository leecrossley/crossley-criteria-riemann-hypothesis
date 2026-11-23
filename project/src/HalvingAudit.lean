import FirstLayerCriterion
import ShallowRemainder
import HalvingExample
import HalvingPower
import HalvingDivisors
import FirstShallowCriterion
import FirstShallowShells
import Lean.Util.FoldConsts

open Lean Elab Command

private partial def reachable (env : Environment) (todo : List Name) (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then reachable env rest seen
    else
      let used := (env.checked.get.find? n).map (·.getUsedConstantsAsSet.toList)
      reachable env (used.getD [] ++ rest) (seen.insert n)

private def audit (env : Environment) (short : Name) (inputs : List Name := [])
    (criterion := false) : CommandElabM Unit := do
  let root := `RiemannReduction.ShortTail.LossFrequency ++ short
  unless env.contains root do throwError "Missing declaration {root}"
  let ax ← collectAxioms root
  for a in ax do
    unless [`propext,`Classical.choice,`Quot.sound].contains a do throwError "Unexpected axiom {a} in {root}"
  let seen := reachable env [root]
  for a in [`sorryAx, `Lean.ofReduceBool, `Lean.trustCompiler,
      `RiemannReduction.ConductorOne.rh_from_second_seed] do
    if seen.contains a then throwError "Unexpected dependency {a} in {root}"
  if seen.contains `RiemannHypothesis != criterion then throwError "Unexpected RH dependency in {root}"
  for a in inputs do
    unless seen.contains a do throwError "Expected dependency {a} in {root}"
  logInfo m!"{short} | reachable {seen.toList.length} | RH definition {criterion} | axioms {ax.toList}"

run_cmd do
  let env ← getEnv
  let f := fun n : Name => `RiemannReduction.ShortTail.LossFrequency ++ n
  for n in [`clipped_parity_net_sums,`consecutive_net_endpoints,`kernel_at_larger_quotient,
      `halved_net_size,`adverse_layer_zero,`adverse_layer_positive_depth,`first_layer_difference,
      `joint_alarm_factorization,`clipped_sign_event_exact,`clipped_frequency_of_overlap,
      `retained_dyadic_reversal,`retained_selected_layer,`event_subpower_from_height] do audit env n
  audit env `grouped_layer_mass_bounds [f `adverse_layer_in_group,f `adverse_group_of_clipped_alarm]
  audit env `odd_frequency_of_grouped_halvings [f `grouped_layers_of_later_event]
  for n in [`clipped_net_sum_terms,`double_row_at_next_depth,`layer_divisors_lt_double,
      `doubled_divisor_absent,`odd_double_cancels_across_depths] do audit env n
  audit env `deep_layer_frequency [f `signed_layer_ceiling,f `event_frequency_from_height]
  audit env `deep_layer_subpower [f `signed_layer_ceiling,f `event_subpower_from_height]
  audit env `odd_frequency_of_residual_signed [f `deep_layer_subpower,f `odd_frequency_of_clipped_layers]
  audit env `first_layer_forces_clipped [f `clipped_sign_event_exact]
  audit env `score_to_early_or_first [f `first_layer_difference,f `sign_split]
  audit env `score_frequency_first_layer [f `score_to_early_or_first]
  for n in [`deep_first_layer_cover,`clipped_divisor_quotient_range,`quarter_shallow_first_iff,
      `first_frequency_of_shallow,`first_frequency_of_residual,`event_mass_below_one,
      `residual_first_real_thresholds] do audit env n
  audit env `first_shell_event_eventually
  audit env `first_shell_shared_iff [f `first_shell_event_eventually]
  audit env `clipped_net_of_ordinary_prefix [f `signed_kernel_quotient_cells]
  audit env `adverse_layer_height [f `clipped_net_of_ordinary_prefix]
  audit env `selected_log_frequency_of_cubic_contour [f `adverse_layer_height]
  audit env `selected_four_of_cubic_contour [f `selected_log_frequency_of_cubic_contour]
  audit env `selected_layer_frequency_of_prefix_exponent [`HalvingMertens.PrefixExponent,f `adverse_layer_height]
  audit env `shared_layers_of_prefix_exponent [f `selected_layer_frequency_of_prefix_exponent]
  audit env `rh_of_residual_signed [f `odd_frequency_of_residual_signed,f `rh_iff_frequency] true
  audit env `rh_of_first_layer_frequency [f `score_frequency_first_layer,f `rh_iff_frequency] true
  audit env `rh_of_residual_first [f `first_frequency_of_residual,f `rh_of_first_layer_frequency] true
  audit env `rh_of_full_first_shells [f `first_shell_shared_iff,f `rh_of_residual_first] true
