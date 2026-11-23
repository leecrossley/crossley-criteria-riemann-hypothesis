import Mathlib
import IndependentLandau.Ramp

/-! Target statements for the classical inputs of the arithmetic route, for the
Riemann zeta function. Mathlib only. Each statement is the zeta case of a theorem
the route currently imports, with the same shape, so a proof can replace the import. -/

open Complex

noncomputable section

namespace ZetaShared

/-- Nontrivial zeros with imaginary part within 1 of `t`. -/
def zerosNear (t : ℝ) : Set ℂ :=
  {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ riemannZeta ρ = 0}

/-- Nontrivial zeros of height below `T`. -/
def zerosBelow (T : ℝ) : Set ℂ :=
  {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ riemannZeta ρ = 0}

/-- Multiplicity of a zero. -/
def mult (ρ : ℂ) : ℕ := analyticOrderNatAt riemannZeta ρ

/-- Zeros in unit windows, counted with multiplicity, number at most `C log (|t| + 2)`. -/
def ZeroCountStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, (zerosNear t).Finite ∧
    ∑ᶠ ρ ∈ zerosNear t, (mult ρ : ℝ) ≤ C * Real.log (|t| + 2)

/-- Truncated explicit formula for the Chebyshev function. -/
def ExplicitFormulaStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ u T : ℝ, 2 ≤ T → T ≤ u → (zerosBelow T).Finite ∧
    ‖((Chebyshev.psi u - u : ℝ) : ℂ) + ∑ᶠ ρ ∈ zerosBelow T, (mult ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
      C * (u * Real.log (u * T) ^ 2 / T + Real.log u +
        ∑ᶠ ρ ∈ zerosBelow 1, (mult ρ : ℝ) / ‖ρ‖)

/-- Prime number theorem for the centred ramp with the classical error term. -/
def RampPNTStatement : Prop :=
  ∃ c K : ℝ, 0 < c ∧ ∀ y : ℝ, 2 ≤ y →
    |IndependentLandau.rampG y| ≤ K * y * Real.exp (-c * Real.sqrt (Real.log y))

/-- A classical zero-free region with a bound for the logarithmic derivative inside it. -/
structure RegionData (c C : ℝ) : Prop where
  c_pos : 0 < c
  C_pos : 0 < C
  nonvanishing : ∀ s : ℂ, 1 - c / Real.log (|s.im| + 2) ≤ s.re → s ≠ 1 → riemannZeta s ≠ 0
  logDeriv : ∀ s : ℂ, 1 - c / Real.log (|s.im| + 2) ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
    ‖deriv riemannZeta s / riemannZeta s‖ ≤ C * Real.log (|s.im| + 2) ^ 2

def RegionStatement : Prop := ∃ c C : ℝ, RegionData c C

end ZetaShared
