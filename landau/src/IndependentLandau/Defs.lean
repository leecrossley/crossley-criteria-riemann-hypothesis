import Mathlib

/-! Interface for a window form of Landau's theorem. Mathlib only.

`PoleData` and `WindowHypU` state the hypotheses. Their field lists follow the
interface used by the project's window criterion, so results proved here can
replace the imported lemma without changing its callers. -/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace IndependentLandau

/-- `Φ` is the Laplace transform of `g` on `re s > 2` and continues to `re s > 0`
with simple poles exactly on `Z`. A real pole has positive real residue. -/
structure PoleData (g : ℝ → ℝ) (Φ : ℂ → ℂ) (Z : Set ℂ) : Prop where
  meas : Measurable g
  growth : ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2 * u)
  laplace : ∀ s : ℂ, 2 < s.re → Φ s = ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-s * u)
  pos : ∀ ρ ∈ Z, 0 < ρ.re
  diff : DifferentiableOn ℂ Φ ({s : ℂ | 0 < s.re} \ Z)
  iso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z
  pole : ∀ ρ ∈ Z, ∃ c : ℂ, c ≠ 0 ∧ (ρ.im = 0 → 0 < c.re ∧ c.im = 0) ∧
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, Φ s = c / (s - ρ) + h s

/-- On arbitrarily late windows `[U, (1+δ)U]`, `g` has a nonnegative majorant whose
`exp (-θ u)`-weighted mass is at most `exp (η U)`, for every `η > 0`. -/
def WindowHypU (g : ℝ → ℝ) (θ δ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧ ∃ R : ℝ → ℝ,
    IntegrableOn (fun u => R u * Real.exp (-θ * u)) (Icc U ((1 + δ) * U)) ∧
    (∀ u ∈ Icc U ((1 + δ) * U), 0 ≤ R u ∧ g u ≤ R u) ∧
    ∫ u in Icc U ((1 + δ) * U), R u * Real.exp (-θ * u) ≤ Real.exp (η * U)

end IndependentLandau
