import Mathlib

/-! The Riemann zeta function has no zero on the real interval `(0, 1)`.

For `re s > 1`, Abel summation gives `ζ(s) = s/(s-1) - s ∫_1^∞ {t} t^(-s-1) dt`. The integral is a
Mellin transform of a bounded function supported on `(1, ∞)`, hence holomorphic on `re s > 0`, so
the identity `(s-1) ζ(s) = s - s (s-1) ∫_1^∞ {t} t^(-s-1) dt` continues to `re s > 0`. For real
`0 < s < 1` the right side is at least `s > 0`. -/

open Complex MeasureTheory Set Filter Topology

noncomputable section
namespace Crossley

/-- The fractional part, cut off to `(1, ∞)`. -/
def fractTail : ℝ → ℂ := (Ioi (1 : ℝ)).indicator (fun t => ((Int.fract t : ℝ) : ℂ))

lemma norm_fractTail_le (t : ℝ) : ‖fractTail t‖ ≤ 1 := by
  unfold fractTail
  by_cases h : t ∈ Ioi (1 : ℝ)
  · rw [indicator_of_mem h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t)]
    exact (Int.fract_lt_one t).le
  · rw [indicator_of_notMem h]; simp

lemma measurable_fractTail : Measurable fractTail :=
  (Complex.measurable_ofReal.comp measurable_fract).indicator measurableSet_Ioi

lemma locallyIntegrableOn_fractTail : LocallyIntegrableOn fractTail (Ioi 0) := by
  refine (LocallyIntegrable.mono (locallyIntegrable_const (1 : ℝ))
    measurable_fractTail.aestronglyMeasurable (Eventually.of_forall fun t => ?_)).locallyIntegrableOn _
  simpa using norm_fractTail_le t

lemma differentiableAt_mellin_fractTail {w : ℂ} (hw : w.re < 0) :
    DifferentiableAt ℂ (mellin fractTail) w := by
  refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := w.re - 1)
    locallyIntegrableOn_fractTail ?_ hw ?_ (by linarith)
  · refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)
    simpa using norm_fractTail_le t
  · have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
      (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
    have h2 : fractTail =ᶠ[𝓝[>] 0] fun _ => (0 : ℂ) := by
      filter_upwards [h1] with t ht
      simp [fractTail, not_lt.mpr ht.le]
    exact h2.trans_isBigO (Asymptotics.isBigO_zero _ _)

lemma mellin_fractTail (w : ℂ) :
    mellin fractTail w = ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (w - 1) := by
  unfold mellin
  have h : (fun t : ℝ => (t : ℂ) ^ (w - 1) • fractTail t) =
      (Ioi (1 : ℝ)).indicator (fun t => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (w - 1)) := by
    funext t
    by_cases h : t ∈ Ioi (1 : ℝ)
    · simp [fractTail, indicator_of_mem h, mul_comm]
    · simp [fractTail, indicator_of_notMem h]
  rw [h, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_right.mpr zero_le_one]

/-- Abel summation for zeta on `re s > 1`. -/
lemma zeta_eq_fract {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) - s * mellin fractTail (-s) := by
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, ‖(1 : ℕ → ℂ) k‖) =O[atTop]
      fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    simp
  have h1 := LSeries_eq_mul_integral' (1 : ℕ → ℂ) zero_le_one hs hO
  rw [LSeries_one_eq_riemannZeta hs] at h1
  have hint1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one
  have hint2' : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one
  have hint2 : IntegrableOn (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))
      (Ioi 1) := by
    refine Integrable.mono' hint2'.norm ?_ ?_
    · exact (Complex.measurable_ofReal.comp measurable_fract).aestronglyMeasurable.mul
        hint2'.aestronglyMeasurable
    · refine Eventually.of_forall fun t => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one t).le
  have hcongr : ∫ t in Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℕ → ℂ) k) * (t : ℂ) ^ (-(s + 1)) =
      ∫ t in Ioi (1 : ℝ), ((t : ℂ) ^ (-s) - ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    have hfl : ((⌊t⌋₊ : ℕ) : ℂ) = (t : ℂ) - ((Int.fract t : ℝ) : ℂ) := by
      have h : ((⌊t⌋₊ : ℕ) : ℝ) = t - Int.fract t := by
        rw [natCast_floor_eq_intCast_floor ht0.le, Int.fract]; ring
      rw [← Complex.ofReal_sub, ← h]; simp
    have hpow : (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = (t : ℂ) ^ (-s) := by
      have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      rw [show -s = 1 + -(s + 1) by ring, Complex.cpow_add _ _ htc, Complex.cpow_one]
    simp only [Pi.one_apply, Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul,
      mul_one]
    rw [hfl, sub_mul, hpow]
  have hs1 : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hs1' : -s + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hexp : -s - 1 = -(s + 1) := by ring
  rw [h1, hcongr, integral_sub hint1 hint2, integral_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one,
    mellin_fractTail, hexp]
  simp only [Complex.ofReal_one, Complex.one_cpow]
  field_simp
  ring

/-- The continued identity on the right half-plane. -/
lemma zeta₁_eq_fract {s : ℂ} (hs : 0 < s.re) :
    riemannZeta₁ s = s - s * (s - 1) * mellin fractTail (-s) := by
  let D : ℂ → ℂ := fun s => riemannZeta₁ s - (s - s * (s - 1) * mellin fractTail (-s))
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hD : DifferentiableOn ℂ D {s : ℂ | 0 < s.re} := by
    intro z hz
    have hz' : (-z).re < 0 := by simpa using hz
    have hm : DifferentiableAt ℂ (fun s => mellin fractTail (-s)) z :=
      (differentiableAt_mellin_fractTail hz').comp z differentiableAt_id.neg
    exact ((differentiable_riemannZeta₁ z).sub (differentiableAt_id.sub
      ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul hm))).differentiableWithinAt
  have h0 : D =ᶠ[𝓝 2] 0 := by
    have h : ∀ᶠ z : ℂ in 𝓝 2, 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [h] with z hz
    have hz1 : z ≠ 1 := by rintro rfl; simp at hz
    have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have e1 := riemannZeta_eq_inv_sub_mul hz1
    have e2 := zeta_eq_fract hz
    have e3 : riemannZeta₁ z = (z - 1) * riemannZeta z := by rw [e1]; field_simp
    simp only [D, Pi.zero_apply]
    rw [e3, e2]; field_simp; ring
  have h := (hD.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_re_gt 0).isPreconnected (show (2 : ℂ) ∈ {s : ℂ | 0 < s.re} by simp) h0 hs
  simpa [D, sub_eq_zero] using h

/-- The Riemann zeta function has no zero on the real interval `(0, 1)`. -/
theorem riemannZeta_ne_zero_of_mem_Ioo {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    riemannZeta (x : ℂ) ≠ 0 := by
  have hx1 : (x : ℂ) ≠ 1 := by exact_mod_cast h1.ne
  have key := zeta₁_eq_fract (s := (x : ℂ)) (by simpa using h0)
  obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 ≤ r ∧ mellin fractTail (-(x : ℂ)) = (r : ℂ) := by
    refine ⟨∫ t in Ioi (1 : ℝ), Int.fract t * t ^ (-x - 1), ?_, ?_⟩
    · exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
        mul_nonneg (Int.fract_nonneg t) (Real.rpow_nonneg (zero_le_one.trans ht.le) _)
    · rw [mellin_fractTail, ← integral_complex_ofReal]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht0 : (0 : ℝ) ≤ t := zero_le_one.trans (le_of_lt ht)
      rw [Complex.ofReal_mul, Complex.ofReal_cpow ht0]
      push_cast
      rfl
  intro hz
  have e1 := riemannZeta_eq_inv_sub_mul hx1
  rw [hz] at e1
  have hζ1 : riemannZeta₁ (x : ℂ) = 0 := by
    rcases mul_eq_zero.mp e1.symm with h | h
    · exact absurd (inv_eq_zero.mp h) (sub_ne_zero.mpr hx1)
    · exact h
  rw [hζ1, hr] at key
  have hreal : (0 : ℝ) = x - x * (x - 1) * r := by exact_mod_cast key
  nlinarith [mul_nonneg (mul_nonneg h0.le (sub_nonneg.mpr h1.le)) hr0]

end Crossley

#print axioms Crossley.riemannZeta_ne_zero_of_mem_Ioo
