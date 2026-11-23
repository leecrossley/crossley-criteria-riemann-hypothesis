import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace HalvingMertens

/-- An exponent for the ordinary integer Möbius prefix, with an arbitrary
positive loss. This interface uses the same sum at every toolchain pin. -/
def PrefixExponent (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    |∑ d ∈ Finset.range (N + 1), (ArithmeticFunction.moebius d : ℝ)| ≤
      C * ((N : ℝ) + 1) ^ (θ + ε)

end HalvingMertens
