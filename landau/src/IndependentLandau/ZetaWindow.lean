import IndependentLandau.Zeta
import IndependentLandau.WindowLemma

/-! The window form of Landau's theorem applied to zeta. Mathlib only. -/

open Complex

namespace IndependentLandau

/-- A one-sided window bound for the centred ramp excludes zeros of zeta to the right of `θ`. -/
theorem zeta_zeroFree_of_window {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ)
    (hW : WindowHypU (fun u => rampG (Real.exp u)) θ δ) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 := by
  obtain ⟨Φ, hP⟩ := zeta_poleData
  have h := landau_window hP hθ hθ1 hδ hW
  intro s hs hz
  have hmem : s ∈ zetaZeros := ⟨hθ.trans hs, hz⟩
  exact absurd (h s hmem) (not_le.mpr hs)

#print axioms zeta_zeroFree_of_window

end IndependentLandau
