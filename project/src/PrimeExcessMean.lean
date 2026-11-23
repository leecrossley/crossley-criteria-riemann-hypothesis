import PrimeWindow

open Filter MeasureTheory Set

noncomputable section
namespace PrimeCentreMean

/-- Positive excess of Crossley's ordinary-prime tent, parametrised by its right endpoint. -/
def excess (x : ℝ) : ℝ :=
  max 0 (ThetaTransfer.primeSum (x/4) - (x/2) * Real.log 2)

/-- Logarithmic-coordinate form of the ordinary-prime excess integral on a power window. -/
def excessDensity (θ u : ℝ) : ℝ :=
  excess (Real.exp u) * Real.exp (-θ*u)

def SmallExcessMean (θ δ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ U₀ : ℝ, ∃ U ≥ U₀,
    IntegrableOn (excessDensity θ) (Icc U ((1+δ)*U)) ∧
      (∫ u in Icc U ((1+δ)*U), excessDensity θ u) ≤ Real.exp (ε*U)

private theorem cover_prime_powers :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ,
      -ThetaTransfer.primePowerDeficit u ≤ excess (Real.exp u) + K * Real.exp (u/2) := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨max 0 C, le_max_left _ _, fun u => ?_⟩
  have gap := ThetaTransfer.primePowerGap_le (Real.exp u / 4)
  rw [show 4*(Real.exp u / 4) = Real.exp u by ring] at gap
  have sqrtExp : Real.sqrt (Real.exp u) = Real.exp (u/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]; congr 1; ring
  have bound := gap.trans (hC _)
  rw [sqrtExp] at bound
  have scale := mul_le_mul_of_nonneg_right (le_max_right 0 C) (Real.exp_pos (u/2)).le
  have pos := le_max_right 0
    (ThetaTransfer.primeSum (Real.exp u/4) - Real.exp u/2 * Real.log 2)
  unfold excess ThetaTransfer.primePowerDeficit
  linarith

/-- A subpower allowance for the weighted positive excess on common windows rules out
ordinary zeta zeros to the right of the fixed exponent. -/
theorem zeroFree_of_excessMean {θ δ : ℝ} (half : 1/2 ≤ θ) (one : θ < 1)
    (width : 0 < δ) (small : SmallExcessMean θ δ) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 := by
  obtain ⟨K, nonneg, cover⟩ := cover_prime_powers
  apply ThetaTransfer.zeta_zeroFree_of_surplus (by linarith) one width
  intro η hη U₀
  let a := η / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have eventually_large : ∀ᶠ U : ℝ in atTop,
      0 < U ∧ K*δ*U ≤ Real.exp (a*U) ∧ 2 ≤ Real.exp (a*U) := by
    filter_upwards [eventually_gt_atTop (0:ℝ),
      (tendsto_exp_mul_div_rpow_atTop 1 a ha).eventually_ge_atTop (K*δ),
      (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop ha)).eventually_ge_atTop 2]
      with U hu linear room
    exact ⟨hu, (le_div_iff₀ hu).mp (by simpa using linear), room⟩
  obtain ⟨V, hV⟩ := eventually_atTop.mp eventually_large
  obtain ⟨U, hU, hint, hsize⟩ := small a ha (max U₀ V)
  obtain ⟨hpos, hlin, hroom⟩ := hV U ((le_max_right _ _).trans hU)
  let major (u : ℝ) := K * Real.exp (θ*u) + excess (Real.exp u)
  have weighted : (fun u => major u * Real.exp (-θ*u)) =
      fun u => K + excessDensity θ u := by
    funext u
    unfold major excessDensity
    rw [add_mul, mul_assoc, ← Real.exp_add]
    ring_nf
    simp
  have hk : IntegrableOn (fun _ : ℝ => K) (Icc U ((1+δ)*U)) :=
    continuousOn_const.integrableOn_Icc
  refine ⟨U, (le_max_left _ _).trans hU, major, ?_, ?_, ?_⟩
  · rw [weighted]; exact hk.add hint
  · intro u hu
    have late := hpos.le.trans hu.1
    have grow : Real.exp (u/2) ≤ Real.exp (θ*u) :=
      Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg (sub_nonneg.mpr half) late])
    have scaled := mul_le_mul_of_nonneg_left grow nonneg
    exact ⟨add_nonneg (mul_nonneg nonneg (Real.exp_pos _).le) (le_max_left _ _),
      by dsimp [major]; linarith [cover u]⟩
  · rw [weighted, integral_add hk hint, setIntegral_const, Real.volume_real_Icc_of_le
      (by nlinarith only [mul_pos width hpos] : U ≤ (1+δ)*U), smul_eq_mul]
    calc ((1+δ)*U-U)*K + (∫ u in Icc U ((1+δ)*U), excessDensity θ u)
          ≤ 2*Real.exp (a*U) := by linarith only [hlin, hsize]
         _ ≤ Real.exp (a*U)*Real.exp (a*U) :=
           mul_le_mul_of_nonneg_right hroom (Real.exp_pos _).le
         _ = Real.exp (η*U) := by rw [← Real.exp_add]; congr 1; dsimp [a]; ring

end PrimeCentreMean
