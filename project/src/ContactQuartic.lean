import StripQuarticBudget
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-! Transfer Joseph Bebel's exact all-moduli nonvanishing statement to the paired
fourth-power mass. The three named input types correspond to Candidate.bound,
Candidate.bound_le and Candidate.bound_isolated from QuasiRiemannTracker #143.
This side of the version boundary runs on the archive's Lean 4.33.1. -/
namespace RiemannReduction.DivisorBand.FourthMass.Contact
noncomputable section

def roots : Set ℝ := {x | (13 / 15) < x ∧ x < (7 / 8) ∧ ((-274959111914881) + x * (2643837682856883 + x * ((-11291220876239226) + x * (28111661257098222 + x * ((-44964545308854309) + x * (47916748658170215 + x * ((-34020380857037616) + x * (15517896164111592 + x * ((-4126408710053184) + x * 487371101862528))))))))) = 0}
def boundary : ℝ := sInf roots
def rankedUpper : ℝ := 9908119238306612133369374975000622988619121777878229799765263366946606045502455625911569003364955967645745531862430068266267717 /
  11345012023616779600791582323373494582287250283647959965785871011074347975117040113347744503437234376916434871293982689424818700

def AllDirichletAbove (t : ℝ) : Prop :=
  ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ},
    t < s.re → ¬(χ = 1 ∧ s = 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- Specialization to modulus one also handles the analytic pole in Mathlib's total function. -/
theorem ordinaryAbove {t : ℝ} (given : AllDirichletAbove t) :
    RiemannReduction.ZetaWindow.Strip.ZeroFreeTo t := by
  intro s hs
  by_cases pole : s = 1
  · simpa [pole] using riemannZeta_one_ne_zero
  · simpa only [DirichletCharacter.LFunction_modOne_eq] using
      given (1 : DirichletCharacter ℂ 1) hs (fun pair => pole pair.2)

theorem boundary_in_interval (unique : ∃! z : ℝ, z ∈ roots) :
    13/15 < boundary ∧ boundary < 7/8 := by
  obtain ⟨z,hz,only⟩ := unique
  have eqn : roots = {z} := Set.ext fun x => ⟨fun hx => only _ hx, fun hx => (Set.mem_singleton_iff.mp hx) ▸ hz⟩
  have atRoot : boundary = z := by simp [boundary,eqn]
  rw [atRoot]
  exact ⟨hz.1,hz.2.1⟩

theorem mass_at_contact (given : AllDirichletAbove boundary) (unique : ∃! z : ℝ, z ∈ roots) :
    ∃ C > (0 : ℝ), ∀ s : ℝ, (s=1 ∨ s= -1) → ∀ m : ℕ, 10^8 ≤ m →
      mass (signedRemainder s) m ≤ C*(m:ℝ)^(8*boundary-4) := by
  have loc := boundary_in_interval unique
  exact quartic_bound_of_strip ((by norm_num : (1/2:ℝ)<13/15).trans loc.1)
    loc.2.le (ordinaryAbove given)

theorem mass_below_2986767 (given : AllDirichletAbove boundary) (upper : boundary ≤ rankedUpper) :
    ∃ C > (0 : ℝ), ∀ s : ℝ, (s=1 ∨ s= -1) → ∀ m : ℕ, 10^8 ≤ m →
      mass (signedRemainder s) m ≤ C*(m:ℝ)^(2986767/1000000:ℝ) := by
  have roundUp : rankedUpper < 6986767/8000000 := by norm_num [rankedUpper]
  have free : RiemannReduction.ZetaWindow.Strip.ZeroFreeTo (6986767/8000000) := by
    intro z hs
    exact ordinaryAbove given (upper.trans_lt (roundUp.trans hs))
  simpa only [show 8*(6986767/8000000:ℝ)-4=2986767/1000000 by norm_num] using
    quartic_bound_of_strip (by norm_num : (1/2:ℝ) < 6986767/8000000)
      (by norm_num : (6986767/8000000:ℝ) ≤ 7/8) free

#print axioms mass_at_contact
#print axioms mass_below_2986767
end
end RiemannReduction.DivisorBand.FourthMass.Contact
