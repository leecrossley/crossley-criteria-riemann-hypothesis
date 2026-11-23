import ShellFirstMoment

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency

/-- The exact first-moment statement with one constant per exponent, on
arbitrarily late square blocks, would imply RH. The estimate is a premise. -/
theorem rh_of_uniform_first_moments
    (bound : ∀ δ > (0:ℝ), cofinalMomentBound uniformShellScore δ) : RiemannHypothesis :=
  rh_of_uniform_shell_score (uniform_weak_iff_first_moment.mpr (all_cofinal_moments_iff.mp bound))

/-- Any b satisfying 0 ≤ b < δ/4 may be chosen separately for each exponent.
Only quotient shells strictly below n^(1-b) need an arithmetic estimate. -/
theorem rh_of_inner_first_moments (b : ℝ → ℝ)
    (slope : ∀ δ > (0:ℝ), 0 ≤ b δ ∧ 4*b δ < δ)
    (bound : ∀ δ > (0:ℝ), cofinalMomentBound
      (maskedShellScore (fun n j => (2:ℝ)^j < (n:ℝ)^(1-b δ))) δ) : RiemannHypothesis := by
  apply rh_of_uniform_first_moments
  intro δ ep
  obtain ⟨hb,gap⟩ := slope δ ep
  apply (low_quotient_first_moment_iff_below (κ:=16*b δ/3) (by positivity)
    (show 3*(16*b δ/3)/4 < δ by linarith only [gap])).mp
  simpa only [lowQuotientScore,show 3*(16*b δ/3)/16=b δ by ring] using bound δ ep

end RiemannReduction.ShortTail.LossFrequency
