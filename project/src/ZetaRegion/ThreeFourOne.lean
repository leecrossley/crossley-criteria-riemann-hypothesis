import Mathlib

/-! The 3-4-1 inequality for `-ζ'/ζ`, from `-ζ'/ζ(s) = ∑ Λ(n) n^(-s)` and
`3 + 4 cos θ + cos 2θ = 2 (1 + cos θ)^2 ≥ 0`. -/

open Complex ArithmeticFunction LSeries.notation

noncomputable section
namespace ZetaRegion

lemma re_term_vonMangoldt {n : ℕ} (hn : n ≠ 0) (σ t : ℝ) (k : ℕ) :
    (LSeries.term ↗Λ ((σ : ℂ) + k * (t * I)) n).re =
      Λ n * (n : ℝ) ^ (-σ) * (((n : ℂ) ^ (-(t * I))) ^ k).re := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have e1 : (n : ℂ) ^ (-(σ : ℂ)) = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    simp
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← cpow_neg,
    show -((σ : ℂ) + k * (t * I)) = -(σ : ℂ) + (k : ℂ) * (-(t * I)) by ring,
    cpow_add _ _ hn', cpow_nat_mul, e1, ← mul_assoc, ← ofReal_mul, re_ofReal_mul]

lemma three_four_one_unit {w : ℂ} (hw : ‖w‖ = 1) :
    0 ≤ 3 * (w ^ 0).re + 4 * (w ^ 1).re + (w ^ 2).re := by
  have h : w.re * w.re + w.im * w.im = 1 := by
    have := Complex.normSq_eq_norm_sq w
    rw [hw, Complex.normSq_apply] at this
    linarith
  have e2 : (w ^ 2).re = w.re * w.re - w.im * w.im := by
    rw [pow_two, mul_re]
  rw [e2, pow_zero, pow_one, one_re]
  nlinarith [sq_nonneg (w.re + 1)]

lemma hasSum_re_logDeriv {σ : ℝ} (hσ : 1 < σ) (t : ℝ) (k : ℕ) :
    HasSum (fun n : ℕ => Λ n * (n : ℝ) ^ (-σ) * (((n : ℂ) ^ (-(t * I))) ^ k).re)
      (-(deriv riemannZeta ((σ : ℂ) + k * (t * I)) / riemannZeta ((σ : ℂ) + k * (t * I)))).re := by
  have hs : 1 < ((σ : ℂ) + k * (t * I)).re := by simpa using hσ
  have h1 := Complex.hasSum_re (LSeriesSummable_vonMangoldt hs).LSeriesHasSum
  rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, neg_div] at h1
  refine h1.congr_fun ?_ |>.mono_left le_rfl
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · exact (re_term_vonMangoldt hn σ t k).symm

/-- **The 3-4-1 inequality.** -/
theorem three_four_one {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (-(deriv riemannZeta σ / riemannZeta σ)).re
      + 4 * (-(deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I))).re
      + (-(deriv riemannZeta (σ + 2 * t * I) / riemannZeta (σ + 2 * t * I))).re := by
  have h0 := hasSum_re_logDeriv hσ t 0
  have h1 := hasSum_re_logDeriv hσ t 1
  have h2 := hasSum_re_logDeriv hσ t 2
  have e0 : (σ : ℂ) + ((0 : ℕ) : ℂ) * (t * I) = σ := by simp
  have e1 : (σ : ℂ) + ((1 : ℕ) : ℂ) * (t * I) = σ + t * I := by simp
  have e2 : (σ : ℂ) + ((2 : ℕ) : ℂ) * (t * I) = σ + 2 * t * I := by push_cast; ring
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  have h := ((h0.mul_left 3).add (h1.mul_left 4)).add h2
  refine h.nonneg fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hw : ‖(n : ℂ) ^ (-(t * I))‖ = 1 := by
      have := Complex.norm_cpow_eq_rpow_re_of_pos hpos (-(t * I))
      simpa using this
    have ha : 0 ≤ Λ n * (n : ℝ) ^ (-σ) :=
      mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg hpos.le _)
    have := mul_nonneg ha (three_four_one_unit hw)
    linarith

end ZetaRegion

#print axioms ZetaRegion.three_four_one
