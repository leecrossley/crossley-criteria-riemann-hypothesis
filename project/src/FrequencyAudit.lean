import FiniteDriver
import ShortFrequency
import QuotientSignFold
import DistantMobiusPairs
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

private def audit (env : Environment) (short : Name) (inputs : List Name) (criterion := false) : CommandElabM Unit := do
  let root := `RiemannReduction.ShortTail.LossFrequency ++ short
  let seen := reachable env [root]
  let ax ← collectAxioms root
  for a in ax do
    unless [`propext,`Classical.choice,`Quot.sound].contains a do throwError "Unexpected axiom {a} in {root}"
  for a in [`sorryAx, `RiemannReduction.ConductorOne.rh_from_second_seed] do
    if seen.contains a then throwError "Unexpected dependency {a} in {root}"
  if seen.contains `RiemannHypothesis != criterion then throwError "Incorrect RH dependency in {root}"
  for a in inputs do
    unless seen.contains a do throwError "Expected {a} in {root}"
  logInfo m!"{short} | reachable {seen.toList.length} | RH definition {criterion} | axioms {ax.toList}"

run_cmd do
  let env ← getEnv
  let f := fun n : Name => `RiemannReduction.ShortTail.LossFrequency ++ n
  let s := fun n : Name => `RiemannReduction.ShortTail ++ n
  let p := fun n : Name => `RiemannReduction.ShortTail.SignPairs ++ n
  audit env `score_is_paid_loss [p `full_payment]
  audit env `weighted_score_eq_outstanding [p `allocation_window]
  audit env `weak_le_weighted [f `frequency,f `weighted]
  audit env `weighted_le_levels [f `frequency,f `weighted]
  audit env `score_polynomial [p `payment_at_each_sample,p `selected_gain_upper]
  audit env `weak_iff_outstanding [f `weighted_le_levels,f `score_polynomial,f `weak_le_weighted]
  audit env `rh_iff_frequency [f `weak_iff_outstanding,`RiemannReduction.DivisorBand.FourthMass.rh_iff_subpower_quartic_budget] true
  audit env `all_thresholds_of_contact [p `payment_window_of_contact,f `weak_le_weighted]
  audit env `low_thresholds [s `harmonic_window]
  audit env `cut_absolute [f `row_envelope,s `term]
  audit env `high_negative [f `cut_absolute,f `highSum]
  audit env `band_split [f `bandSum,f `quotientLevel]
  audit env `band_driving_hit [f `band_split,f `high_negative]
  audit env `row_uniform [s `term,`ArithmeticFunction.abs_moebius_le_one]
  audit env `pair_square [f `nearProducts,f `farProducts,s `core]
  audit env `near_absolute [f `row_uniform,f `nearProducts]
  audit env `far_positive_at_hit [f `pair_square,f `near_absolute]
  audit env `frequency_from_far [f `far_positive_at_hit,f `frequency]
  audit env `discarded_identity [`RiemannReduction.BalancedSquare.balanced_square,`RiemannReduction.DyadicBands.null,
    `RiemannGaussian.AlpogeMined.fixedBandHalfTail_error]
  audit env `score_distance_subpower [f `discarded_identity,f `cut_absolute]
  audit env `identical_large_hits_up_to_factor_two [f `score_distance_subpower]
  audit env `positive_annulus_at_hit [f `discarded_identity,f `cut_absolute]
  audit env `finite_annulus [f `positive_annulus_at_hit,`RiemannReduction.BalancedSquare.balanced_square]
  audit env `finite_annulus_blocks [f `finite_annulus]
  audit env `finite_frequency_annulus [f `finite_annulus,f `frequency]
  audit env `short_frequency_iff [f `identical_large_hits_up_to_factor_two,f `low_thresholds]
  audit env `quotient_sign_fold [f `fold_signed_rows,`ArithmeticFunction.isMultiplicative_moebius]
  audit env `halved_quotient [f `oddHalves]
  audit env `halved_dyadic_band [f `oddHalves,f `quotientBandRows]
  audit env `odd_band_driving_hit [f `band_driving_hit,f `fold_signed_rows]
  audit env `frequency_odd_witness [f `odd_band_driving_hit,f `frequency]
