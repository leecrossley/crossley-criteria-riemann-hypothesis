import PrimeWindow

noncomputable section
open Set

namespace TentWindow

/-- A constant square-root loss in the prime-power deficit can be absorbed at every θ > 1/2. -/
theorem rh_of_fixed_prime_power_allowance {δ K : ℝ} (hδ : 0 < δ)
    (floor : ∀ U₀ : ℝ, ∃ U ≥ U₀, ∀ u ∈ Icc U ((1 + δ) * U),
      -(K * Real.exp (u / 2)) ≤ ThetaTransfer.primePowerDeficit u) : RiemannHypothesis := by
  apply ZetaShared.Reflection.rh_of_right
  intro s hs _
  let θ := (1 / 2 + min 1 s.re) / 2
  have ht : 1 / 2 < θ := by dsimp [θ]; linarith [lt_min (by norm_num : (1 : ℝ) / 2 < 1) hs]
  have ht1 : θ < 1 := by dsimp [θ]; linarith [min_le_left (1 : ℝ) s.re]
  have hts : θ < s.re := by dsimp [θ]; linarith [min_le_right (1 : ℝ) s.re]
  apply ThetaTransfer.zeta_zeroFree_of_surplus (by linarith : 0 < θ) ht1 hδ _ s hts
  apply ThetaTransfer.window_of_point_bounds hδ
  intro U₀
  let A := max 1 K
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have gap : 0 < θ - 1 / 2 := by linarith
  obtain ⟨U, hU, hf⟩ := floor (max U₀ (Real.log A / (θ - 1 / 2)))
  refine ⟨U, (le_max_left _ _).trans hU, fun u hu => ?_⟩
  have lo := ((le_max_right _ _).trans hU).trans hu.1
  have scale : A ≤ Real.exp ((θ - 1 / 2) * u) :=
    (Real.log_le_iff_le_exp hA).mp (by linarith [(div_le_iff₀ gap).mp lo])
  have hK : K ≤ Real.exp ((θ - 1 / 2) * u) := (le_max_right _ _).trans scale
  calc -(ThetaTransfer.primePowerDeficit u) ≤ K * Real.exp (u / 2) := by linarith [hf u hu]
       _ ≤ Real.exp ((θ - 1 / 2) * u) * Real.exp (u / 2) :=
         mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le
       _ = Real.exp (θ * u) := by rw [← Real.exp_add]; congr 1; ring

/-- The analytic estimate needed from the height cutoff is an eventual lower comparison
with the actual prime-power deficit. The constants are fixed before choosing a window. -/
theorem rh_of_bounded_signed_remainder {δ C L U₁ : ℝ} (hδ : 0 < δ)
    (R : ℝ → ℝ → ℝ)
    (comparison : ∀ U ≥ U₁, ∀ u ∈ Icc U ((1 + δ) * U),
      (R U u - L) * Real.exp (u / 2) ≤ ThetaTransfer.primePowerDeficit u)
    (bounded : ∀ U₀ : ℝ, ∃ U ≥ U₀, ∀ u ∈ Icc U ((1 + δ) * U), -C ≤ R U u) :
    RiemannHypothesis := by
  apply rh_of_fixed_prime_power_allowance (K := C + L) hδ
  intro U₀
  obtain ⟨U, hU, hb⟩ := bounded (max U₀ U₁)
  refine ⟨U, (le_max_left _ _).trans hU, fun u hu => ?_⟩
  have cmp := comparison U ((le_max_right _ _).trans hU) u hu
  have h := mul_le_mul_of_nonneg_right (hb u hu) (Real.exp_pos (u / 2)).le
  linarith

#print axioms rh_of_fixed_prime_power_allowance
#print axioms rh_of_bounded_signed_remainder
end TentWindow
