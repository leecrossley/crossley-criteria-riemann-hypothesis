import Mathlib
import ZetaShared.Perron

/-! Nonvanishing of the Riemann zeta function for `-1 < re s ≤ 0`, from the functional equation
and nonvanishing on `re s ≥ 1`. -/

open Complex

noncomputable section
namespace ZetaStrip

/-- `cos (π w / 2) ≠ 0` for `1 ≤ re w < 2`, `w ≠ 1`. -/
lemma cos_pi_mul_div_two_ne_zero {w : ℂ} (h1 : 1 ≤ w.re) (h2 : w.re < 2) (hw : w ≠ 1) :
    Complex.cos ((Real.pi : ℂ) * w / 2) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hw' : w = 2 * (k : ℂ) + 1 := by
    have h2' : (Real.pi : ℂ) * w = (Real.pi : ℂ) * (2 * (k : ℂ) + 1) := by
      have h3 : (Real.pi : ℂ) * w / 2 * 2 = (2 * (k : ℂ) + 1) * (Real.pi : ℂ) / 2 * 2 := by rw [hk]
      rw [div_mul_cancel₀ _ (two_ne_zero), div_mul_cancel₀ _ (two_ne_zero)] at h3
      rw [h3]; ring
    exact mul_left_cancel₀ hpi h2'
  have hre : w.re = 2 * (k : ℝ) + 1 := by
    rw [hw']; simp
  have hk0 : k = 0 := by
    have h3 : (0 : ℝ) ≤ (k : ℝ) := by linarith
    have h4 : (k : ℝ) < 1 := by linarith
    have h3' : (0 : ℤ) ≤ k := by exact_mod_cast h3
    have h4' : k < 1 := by exact_mod_cast h4
    omega
  apply hw
  rw [hw', hk0]; simp

/-- The Riemann zeta function has no zero with `-1 < re s ≤ 0`. -/
theorem riemannZeta_ne_zero_of_re_le_zero {s : ℂ} (h1 : -1 < s.re) (h0 : s.re ≤ 0) :
    riemannZeta s ≠ 0 := by
  rcases eq_or_ne s 0 with rfl | hs
  · rw [riemannZeta_zero]; norm_num
  set w : ℂ := 1 - s with hw
  have hwre : w.re = 1 - s.re := by simp [hw]
  have hw1 : w ≠ 1 := by
    intro h; apply hs
    have : s = 1 - w := by rw [hw]; ring
    rw [this, h]; ring
  have hn : ∀ n : ℕ, w ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    simp only [neg_re, natCast_re] at this
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hfe := riemannZeta_one_sub hn hw1
  have hs' : 1 - w = s := by rw [hw]; ring
  rw [hs'] at hfe
  rw [hfe]
  have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  have hpow : (2 * (Real.pi : ℂ)) ^ (-w) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero h2pi]; exact Complex.exp_ne_zero _
  have hG : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hcos := cos_pi_mul_div_two_ne_zero (w := w) (by linarith) (by linarith) hw1
  have hz : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpow) hG) hcos) hz

end ZetaStrip
