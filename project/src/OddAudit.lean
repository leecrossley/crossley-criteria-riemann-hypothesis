import OddMertensFrequency
import OddGeometricBudget
import OddFiniteAllocations
import FiniteOddCounts
import OddDilation
import OddLocalOscillation
import OddBandDilation
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
  for n in [`odd_moment_recurrence,`odd_prefix_recurrence,`odd_prefix_sqrt,`quotient_rows_interval,
      `cofactor_interval,`odd_abel_bound,`event_split,`event_mass_split,`prefix_event_frequency,
      `full_odd_above_four,`score_le_separated,`geometric_of_separated,`geometric_covers,`geometric_frequency_four,
      `finite_mertens_sqrt,`second_quotient_finite_blocks,`FiniteOdd.exact_counts,
      `FiniteOdd.exact_numerators,`FiniteOdd.all_dyadic,`finite_allocated_frequency,
      `signed_kernel_quotient_cells,`signed_kernel_variation_bound,`complete_odd_dyadic,
      `complete_odd_fourth_dilation,`complete_odd_finite_difference] do audit env n
  audit env `odd_frequency_of_tail [f `prefix_event_frequency,f `event_mass_split]
  audit env `both_signed_dyadic_of_mertens [f `signed_kernel_quotient_cells,f `odd_abel_bound]
  audit env `odd_frequency_of_finite_prefix [f `both_signed_dyadic_of_mertens]
  audit env `odd_frequency_of_cofinal_mertens [f `odd_frequency_of_finite_prefix]
  audit env `odd_frequency_of_mertens_power [f `odd_frequency_of_cofinal_mertens]
  audit env `odd_subpower_of_mertens_subpower [f `odd_frequency_of_mertens_power]
  audit env `odd_frequency_hurst_blocks [f `odd_frequency_of_finite_prefix,f `finite_mertens_sqrt]
  audit env `complete_odd_real_halve [f `fold_signed_rows]
  audit env `complete_odd_of_prime_envelope [f `complete_odd_real_halve]
  audit env `complete_odd_finite_blocks [f `complete_odd_of_prime_envelope,f `full_odd_rows]
  audit env `both_signed_of_local_oscillations [f `variation_on_original_samples,f `odd_abel_anchored_identity]
  audit env `normalized_event_of_odd_alarm [f `both_signed_of_local_oscillations]
  audit env `odd_frequency_of_local_events [f `local_event_mass_covers,f `normalized_event_of_odd_alarm]
  audit env `band_parity_net_sums [f `interval_odd_halve,f `interval_odd_log_telescope]
  audit env `band_alarm_signed_net [f `band_parity_net_sums]
  audit env `score_signed_net_witness [f `band_alarm_signed_net,f `odd_band_driving_hit]
  audit env `odd_frequency_of_signed_nets [f `signed_net_event_mass_covers,f `band_alarm_signed_net]
  audit env `rh_of_odd_event_bounds [f `rh_iff_frequency,f `frequency_odd_witness] true
