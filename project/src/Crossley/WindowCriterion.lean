import PrimeWindow

/-! Crossley's window criterion under its own name. Both theorems restate the core's proof in
`PrimeWindow`, which uses only Mathlib, so the tree keeps one proof of the criterion. -/

open Set

namespace Crossley

/-- Crossley's window criterion, zero-free form: a nonnegative ordinary-prime deficit on
arbitrarily late windows `[U, (1+δ)U]` excludes zeros of zeta to the right of one half. -/
theorem window_criterion_zeroFree {δ : ℝ} (hδ : 0 < δ)
    (sign : ∀ U₀ : ℝ, ∃ U ≥ U₀, ∀ u ∈ Icc U ((1+δ)*U), 0 ≤ ThetaTransfer.primeDeficit u) :
    ∀ s : ℂ, 1/2 < s.re → riemannZeta s ≠ 0 :=
  ThetaTransfer.zeroFree_of_prime_sign_windows hδ sign

/-- Crossley's window criterion: if the tent-weighted sum over ordinary primes stays at or
below its main term on arbitrarily late windows `[X, X^(1+δ)]`, then RH holds. -/
theorem window_criterion {δ : ℝ} (hδ : 0 < δ)
    (sign : ∀ X₀ : ℝ, ∃ X ≥ X₀, ∀ x ∈ Icc X (X ^ (1 + δ)),
      ThetaTransfer.primeSum (x / 4) ≤ (x / 2) * Real.log 2) : RiemannHypothesis :=
  ThetaTransfer.rh_of_prime_sign_windows hδ sign

#print axioms window_criterion_zeroFree
#print axioms window_criterion

end Crossley
