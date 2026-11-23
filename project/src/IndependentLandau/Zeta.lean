import Mathlib
import IndependentLandau.Laplace
import IndependentLandau.Analytic

/-! The centred ramp sum over prime powers has a Laplace transform with simple poles exactly at
the zeros of the Riemann zeta function in `re s > 0`. -/

open scoped ArithmeticFunction.vonMangoldt
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace IndependentLandau

/-- On `re s > 2` the continuation agrees with the Laplace transform of the centred ramp. -/
theorem zetaPhi_eq_laplace {s : ℂ} (hs : 2 < s.re) :
    zetaPhi s = ∫ u in Ioi (0 : ℝ), ((rampG (Real.exp u) : ℝ) : ℂ) * cexp (-s * u) := by
  have hs1 : 1 < s.re := by linarith
  have h1 : s ≠ 1 := by rintro rfl; simp at hs1
  have h0 : s ≠ 0 := by rintro rfl; simp at hs1; linarith
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs1.le
  rw [laplace_rampG hs, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1,
    zetaPhi_eq h1 h0 hζ]

theorem zeta_poleData :
    ∃ Φ : ℂ → ℂ, PoleData (fun u => rampG (Real.exp u)) Φ zetaZeros :=
  ⟨zetaPhi,
    { meas := measurable_rampG_exp
      growth := ⟨5, fun _ hu => abs_rampG_exp_le hu⟩
      laplace := fun _ hs => zetaPhi_eq_laplace hs
      pos := fun _ hρ => hρ.1
      diff := differentiableOn_zetaPhi
      iso := fun z _ => zetaZeros_iso z
      pole := fun _ hρ => zetaPhi_pole hρ }⟩

end IndependentLandau

#print axioms IndependentLandau.zeta_poleData
