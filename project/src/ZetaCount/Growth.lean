import Mathlib
import Crossley.RealZeros
import IndependentLandau.Analytic

/-! Growth of `riemannZeta₁ s = (s - 1) ζ(s)` in the half-plane `re s ≥ 1/20`, and a lower bound
for `ζ` on the line `re s = 2`. -/

open Complex MeasureTheory Set Filter Topology

noncomputable section
namespace ZetaCount

/-- The Mellin integral of the fractional part is at most `1 / re s`. -/
lemma norm_mellin_fractTail_le {s : ℂ} (hs : 0 < s.re) :
    ‖mellin Crossley.fractTail (-s)‖ ≤ 1 / s.re := by
  rw [Crossley.mellin_fractTail]
  have hint : IntegrableOn (fun t : ℝ => t ^ (-s.re - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (1 : ℝ))) hint
    (f := fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t),
        Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      simp only [sub_re, neg_re, one_re]
      exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (Int.fract_lt_one t).le)
  rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one] at h
  have e : -(1 : ℝ) ^ (-s.re - 1 + 1) / (-s.re - 1 + 1) = 1 / s.re := by
    rw [Real.one_rpow, show (-s.re - 1 + 1) = -s.re by ring, neg_div_neg_eq]
  rwa [e] at h

/-- Polynomial growth of `(s - 1) ζ(s)` to the right of `re s = 1/20`. -/
lemma norm_zeta₁_le {s : ℂ} (hs : 1 / 20 ≤ s.re) :
    ‖riemannZeta₁ s‖ ≤ ‖s‖ + 20 * ‖s‖ * ‖s - 1‖ := by
  have hs0 : 0 < s.re := by linarith
  rw [Crossley.zeta₁_eq_fract hs0]
  have hm : ‖mellin Crossley.fractTail (-s)‖ ≤ 20 := by
    refine (norm_mellin_fractTail_le hs0).trans ?_
    rw [div_le_iff₀ hs0]; linarith
  calc ‖s - s * (s - 1) * mellin Crossley.fractTail (-s)‖
      ≤ ‖s‖ + ‖s * (s - 1) * mellin Crossley.fractTail (-s)‖ := norm_sub_le _ _
    _ = ‖s‖ + ‖s‖ * ‖s - 1‖ * ‖mellin Crossley.fractTail (-s)‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖s‖ + ‖s‖ * ‖s - 1‖ * 20 := by gcongr
    _ = ‖s‖ + 20 * ‖s‖ * ‖s - 1‖ := by ring

lemma hasSum_shift_one : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simpa using h

lemma hasSum_shift_two : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
  have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
  simpa [Finset.sum_range_succ] using h

/-- `ζ` is bounded below on the line `re s = 2`. -/
lemma norm_zeta_two_add_ge (t : ℝ) : 1 / 4 ≤ ‖riemannZeta (2 + t * I)‖ := by
  set s : ℂ := 2 + t * I with hs
  have hre : s.re = 2 := by simp [hs]
  have h1 : (1 : ℝ) < s.re := by rw [hre]; norm_num
  have hz := zeta_eq_tsum_one_div_nat_add_one_cpow h1
  have hnorm : ∀ n : ℕ, ‖1 / ((n : ℂ) + 1) ^ s‖ = 1 / ((n : ℝ) + 1) ^ 2 := by
    intro n
    have e : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [e, norm_div, norm_one, Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n), hre,
      Real.rpow_two]
    push_cast; ring
  have hsn : Summable fun n : ℕ => ‖1 / ((n : ℂ) + 1) ^ s‖ := by
    simp_rw [hnorm]; exact hasSum_shift_one.summable
  have hsum : Summable fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s := hsn.of_norm
  rw [hsum.tsum_eq_zero_add] at hz
  have h0 : (1 : ℂ) / (((0 : ℕ) : ℂ) + 1) ^ s = 1 := by simp
  rw [h0] at hz
  have htail : ‖∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s‖ ≤ Real.pi ^ 2 / 6 - 1 := by
    have hsn' : Summable fun n : ℕ => ‖1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s‖ :=
      (summable_nat_add_iff 1).mpr hsn
    refine (norm_tsum_le_tsum_norm hsn').trans (le_of_eq ?_)
    rw [← hasSum_shift_two.tsum_eq]
    refine tsum_congr fun n => ?_
    rw [hnorm]; push_cast; ring
  have hpi : Real.pi ^ 2 / 6 - 1 ≤ 3 / 4 := by
    have h := Real.pi_lt_d2
    have h3 := Real.pi_pos
    nlinarith
  rw [hz]
  have := norm_sub_norm_le (1 : ℂ) (-(∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s))
  rw [norm_one, norm_neg, sub_neg_eq_add] at this
  linarith

/-- `(s - 1) ζ(s)` is bounded below on the line `re s = 2`. -/
lemma norm_zeta₁_two_add_ge (t : ℝ) : 1 / 4 ≤ ‖riemannZeta₁ (2 + t * I)‖ := by
  have hne : (2 + t * I : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this
  rw [IndependentLandau.zeta₁_eq hne, norm_mul]
  have h1 : (1 : ℝ) ≤ ‖(2 + t * I : ℂ) - 1‖ := by
    have := Complex.abs_re_le_norm ((2 + t * I : ℂ) - 1)
    simp at this
    have e : |(2 : ℝ) - 1| = 1 := by norm_num
    linarith [e ▸ this]
  have h2 := norm_zeta_two_add_ge t
  nlinarith [norm_nonneg (riemannZeta (2 + t * I))]

end ZetaCount
