import Mathlib
import ZetaShared.Statements

/-! Intermediate statements for the truncated explicit formula. Mathlib only. -/

open Complex

noncomputable section

namespace ZetaShared

/-- The abscissa used in the truncated Perron integral. -/
def perronAbscissa (u : ℝ) : ℝ := 1 + 1 / Real.log u

/-- The integrand `(-ζ'/ζ)(s) u^s / s`. -/
def perronIntegrand (u : ℝ) (s : ℂ) : ℂ :=
  -(deriv riemannZeta s / riemannZeta s) * (u : ℂ) ^ s / s

/-- `(1/2πi) ∫` of the integrand over the segment from `c - iT` to `c + iT`, `c = perronAbscissa u`. -/
def perronIntegral (u T : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) * ∫ t in (-T)..T, perronIntegrand u ((perronAbscissa u : ℂ) + (t : ℂ) * I)

/-- Truncated Perron formula for the Chebyshev function. -/
def PerronStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ u T : ℝ, 2 ≤ T → T ≤ u →
    ‖((Chebyshev.psi u : ℝ) : ℂ) - perronIntegral u T‖ ≤ C * (u * Real.log u ^ 2 / T + Real.log u)

/-- Bounds for the logarithmic derivative on the line `re s = -1/2` and on horizontal
segments at well-chosen heights, with nonvanishing to the left of the critical strip. -/
def StripLogDerivStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    (∀ s : ℂ, -1/2 ≤ s.re → s.re ≤ 0 → riemannZeta s ≠ 0) ∧
    (∀ t : ℝ, ‖deriv riemannZeta ((-1/2 : ℂ) + (t : ℂ) * I) / riemannZeta ((-1/2 : ℂ) + (t : ℂ) * I)‖
        ≤ C * Real.log (|t| + 2)) ∧
    (∀ T : ℝ, 2 ≤ T → ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧ ∀ σ : ℝ, -1/2 ≤ σ → σ ≤ 2 →
        riemannZeta ((σ : ℂ) + (T' : ℂ) * I) ≠ 0 ∧
        ‖deriv riemannZeta ((σ : ℂ) + (T' : ℂ) * I) / riemannZeta ((σ : ℂ) + (T' : ℂ) * I)‖
          ≤ C * Real.log (T + 2) ^ 2)

end ZetaShared
