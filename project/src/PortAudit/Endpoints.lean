import UniformShellCriterion
import SquareSignedConverse
import FourthSignedCriterion
import FrequencyCriterion
import PrimeWindow
import SparseProducts
import FirstMomentEndpoint
import ZeroFreeShellCriterion
import RampWindowEquivalence
import FourthPowerSparseRH
import FourthPrimeTail
import ReciprocalPrimeCutoff
import PrimePeriodAverage
import PrimeCentreConverse
import SparseTentFourthRH
import TentWidthTwoMargin
import TentComplex
import TentWindow
import TentMean
import TentMassIdentity
import Crossley.WindowConverse
import Lean.Util.FoldConsts

/-! Audit of the ported endpoints: axioms, absence of `sorryAx`, absence of external archive
modules, and absence of any residual archive-mirrored declaration names (`Formalism.*`,
`GlobalTheory.*`, `Deduction.*`, `Development.*`, `PI.PC.*`, `CharFamily`) across the entire
transitive kernel dependency closure. -/

open Lean Elab Command

private partial def usedBy (env : Environment) (pending : List Name) (seen : NameSet := {}) :
    NameSet :=
  match pending with
  | [] => seen
  | n :: rest =>
    if seen.contains n then usedBy env rest seen
    else
      let deps := (env.checked.get.find? n).map (·.getUsedConstantsAsSet.toList)
      usedBy env (deps.getD [] ++ rest) (seen.insert n)

private def packages : List String :=
  ["Mathlib", "Init", "Lean", "Std", "Batteries", "Aesop", "Qq", "Plausible", "ProofWidgets", "ImportGraph", "LeanSearchClient", "Cli"]
private def independent : List String :=
  ["IndependentLandau", "Crossley", "ZetaShared", "ZetaCount", "ZetaRegion", "ZetaRamp", "ZetaPerron", "ZetaStrip", "ZetaExplicit", "ZetaClassical"]
private def archiveMods : List String :=
  ["Development", "Formalism", "GlobalTheory", "Deduction", "GroundTheory", "ReciprocityTheory", "CompanionTheory", "PositivityTheory", "UpperTheory", "Supplements", "Lemmata", "BuildAid", "Main", "Statements"]
private def forbiddenDeclPrefixes : List String :=
  ["Formalism.", "GlobalTheory.", "Deduction.", "Development.", "GroundTheory.", "ReciprocityTheory.", "CompanionTheory.", "PositivityTheory.", "UpperTheory.", "PI.PC."]

run_cmd do
  let env ← getEnv
  for root in [``ThetaTransfer.rh_of_prime_sign_windows,
      ``RiemannReduction.PrimeGrid.rh_of_integer_product_blocks,
      ``RiemannReduction.PrimeGrid.rh_of_doubled_prime_blocks,
      ``RiemannReduction.DivisorBand.square_blocks_iff_rh,
      ``RiemannReduction.DivisorBand.FourthMass.rh_iff_subpower_quartic_budget,
      ``RiemannReduction.ShortTail.LossFrequency.rh_iff_frequency,
      ``RiemannReduction.ShortTail.LossFrequency.rh_of_uniform_shell_score,
      ``RiemannReduction.ShortTail.LossFrequency.rh_of_far_gap,
      ``RiemannReduction.ShortTail.LossFrequency.rh_of_uniform_first_moments,
      ``RiemannReduction.ShortTail.LossFrequency.rh_iff_same_block_shell_frequency,
      ``RiemannReduction.ShortTail.LossFrequency.rh_iff_same_block_far_gap,
      ``RiemannReduction.ShortTail.LossFrequency.rh_iff_cofinal_shell_first_moment,
      ``DirectRampEquivalence.rh_iff_ordinaryWindowUnit_above_half,
      ``FourthPowerSparseRH.rh_iff_fourthPower_sparse_failures,
      ``FourthPrimeTail.rh_iff_cofinal_prime_tail,
      ``FourthPrimeTail.comparison_of_oscillation,
      ``PrimePeriodAverage.residue_average,
      ``PrimeCentreMean.rh_iff_all_smallPrimeCentreBudget,
      ``PrimeCentreMean.Sparse.rh_iff_subpowerFourthSamples,
      ``TentWidthTwoMargin.widthTwoMargin_bounds_d14,
      ``TentZeroBudget.line_mass_bound_and_equality,
      ``TentMassIdentity.line_mass_bound_and_equality_zeta,
      ``TentWindow.rh_of_bounded_signed_remainder,
      ``TentWindow.rh_of_signed_negative_part_mean,
      ``Crossley.WindowConverse.primeSum_lt_eventually,
      ``Crossley.window_criterion_iff] do
    let ax ← collectAxioms root
    unless ax.all ([`propext, `Classical.choice, `Quot.sound].contains ·) do
      throwError "Unexpected axioms at {root}: {ax}"
    let used := usedBy env [root]
    if used.contains `sorryAx then throwError "sorryAx reachable from {root}"
    let mut indep := 0
    let mut compat := 0
    let mut sanft := 0
    let mut project := 0
    for n in used.toList do
      let ns := n.toString
      if forbiddenDeclPrefixes.any (fun p => ns.startsWith p) || ns.contains "CharFamily" then
        throwError "Forbidden archive-stub declaration {n} reached from {root}"
      if let some idx := env.getModuleIdxFor? n then
        let s := (env.header.moduleNames[idx.toNat]!).toString
        unless packages.any (fun p => s == p || s.startsWith (p ++ ".")) do
          if archiveMods.any (fun p => s == p || s.startsWith (p ++ ".")) then
            throwError "Archive module {s} reached through {n}"
          if independent.any (fun p => s == p || s.startsWith (p ++ ".")) then indep := indep + 1
          else if s.startsWith "Compat." then compat := compat + 1
          else if s.startsWith "CheckAlpoge" || s.startsWith "RiemannGaussian." then sanft := sanft + 1
          else project := project + 1
    IO.println s!"AUDIT {root}: reachable {used.toList.length}; project {project}, compat {compat}, independent {indep}, Sanftenberg {sanft}, archive/stub 0; axioms {ax.toList}"
