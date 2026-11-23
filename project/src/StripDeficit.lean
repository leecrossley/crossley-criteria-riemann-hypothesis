import StripIntegral
import FourthSignedCriterion

open Finset MeasureTheory
open scoped Interval
namespace RiemannReduction.DivisorBand.FourthMass
noncomputable section

/-- The ordinary prime-power deficit inherits the exact exponent of the supplied strip. -/
theorem deficit_of_strip {σ : ℝ} (lower : 1/2 ≤ σ) (upper : σ ≤ 7/8)
    (free : ZetaWindow.Strip.ZeroFreeTo σ) :
    ∃ C > (0:ℝ), ∀ x : ℝ, 8 ≤ x → |D x| ≤ C*x^σ := by
  obtain ⟨M,mp,h⟩ := ZetaWindow.Strip.smoothed_psi_of_strip lower upper free
  refine ⟨6*M,by positivity,fun x hx => ?_⟩
  let y := x/4
  have big : 2 ≤ y := by dsimp [y]; linarith
  have yp : 0 < y := by linarith
  have first := h big le_rfl (show y≤2*y by linarith) (show 2*y≤4*y by linarith)
  have second := h big (show y≤2*y by linarith) (show 2*y≤4*y by linarith) le_rfl
  have scale : y*y^(σ-1) = y^σ := calc
    _ = y^(1:ℝ)*y^(σ-1) := by rw [Real.rpow_one]
    _ = _ := by rw [←Real.rpow_add yp]; ring_nf
  have grow : y^σ ≤ x^σ :=
    Real.rpow_le_rpow yp.le (by dsimp [y]; linarith) (by linarith)
  have eq := deficit_eq_centered_integrals (show 1≤y by linarith)
  rw [show 4*y=x by dsimp [y]; ring] at eq
  rw [eq]
  calc _ ≤ |2*y*(∫ u in y..2*y,density u)| + |x*(∫ u in 2*y..x,density u)| := abs_sub _ _
       _ ≤ (2*y)*(M*y^(σ-1))+(4*y)*(M*y^(σ-1)) := by
         rw [show x=4*y by dsimp [y]; ring, abs_mul (2*y),abs_mul (4*y),
           abs_of_pos (show 0<2*y by linarith),abs_of_pos (show 0<4*y by linarith)]
         exact add_le_add (mul_le_mul_of_nonneg_left first (by positivity))
           (mul_le_mul_of_nonneg_left second (by positivity))
       _ = (6*M)*y^σ := by rw [←scale]; ring
       _ ≤ _ := mul_le_mul_of_nonneg_left grow (by positivity)

#print axioms deficit_of_strip
end
end RiemannReduction.DivisorBand.FourthMass
