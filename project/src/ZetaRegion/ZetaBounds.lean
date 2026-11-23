import Mathlib
import Crossley.RealZeros
import IndependentLandau.Analytic

/-! Bounds for `riemannZeta₁ s = (s - 1) ζ(s)` used in the zero-free region.

* `norm_zeta₁_le`: `‖ζ₁ s‖ ≤ ‖s‖ + ‖s‖ ‖s - 1‖ / re s` for `re s > 0`, from the Abel summation
  formula `ζ₁ s = s - s (s - 1) ∫_1^∞ {x} x^(-s-1) dx` proved in `Crossley.RealZeros`.
* `norm_zeta₁_le_of_strip`: the resulting polynomial bound in a strip.
* `one_le_norm_zeta_mul`: `1 ≤ ‖ζ s‖ ‖ζ (re s)‖` for `re s > 1`, from the Möbius series.
* `le_norm_zeta₁`: `(re s - 1)/3 ≤ ‖ζ₁ s‖` for `1 < re s ≤ 2`, `|im s| ≥ 1`.
* `logDeriv_zeta_eq`: `ζ'/ζ = ζ₁'/ζ₁ - 1/(s - 1)`.
* `exists_logDeriv_real_bound`: `-ζ'/ζ(σ) ≤ 1/(σ - 1) + E` on `(1, 2]`. -/

open Complex MeasureTheory Set Filter Topology

noncomputable section
namespace ZetaRegion

lemma norm_mellin_fractTail_le {s : ℂ} (hs : 0 < s.re) :
    ‖mellin Crossley.fractTail (-s)‖ ≤ 1 / s.re := by
  rw [Crossley.mellin_fractTail]
  have hσ : -s.re - 1 < -1 := by linarith
  have hint := integrableOn_Ioi_rpow_of_lt hσ zero_lt_one
  have h1 : ‖∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ ≤
      ∫ t in Ioi (1 : ℝ), t ^ (-s.re - 1) := by
    refine norm_integral_le_of_norm_le hint ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t),
      Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have : (-s - 1).re = -s.re - 1 := by simp
    rw [this]
    exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (Int.fract_lt_one t).le
  rw [integral_Ioi_rpow_of_lt hσ zero_lt_one] at h1
  refine h1.trans (le_of_eq ?_)
  rw [Real.one_rpow, show -s.re - 1 + 1 = -s.re by ring, neg_div_neg_eq]

lemma norm_zeta₁_le {s : ℂ} (hs : 0 < s.re) :
    ‖riemannZeta₁ s‖ ≤ ‖s‖ + ‖s‖ * ‖s - 1‖ / s.re := by
  rw [Crossley.zeta₁_eq_fract hs]
  have h := norm_mellin_fractTail_le hs
  calc ‖s - s * (s - 1) * mellin Crossley.fractTail (-s)‖
      ≤ ‖s‖ + ‖s * (s - 1) * mellin Crossley.fractTail (-s)‖ := norm_sub_le _ _
    _ ≤ ‖s‖ + ‖s‖ * ‖s - 1‖ * (1 / s.re) := by
        rw [norm_mul, norm_mul]
        gcongr
    _ = _ := by ring

lemma norm_zeta₁_le_of_strip {z : ℂ} {t : ℝ} (h1 : 1 / 2 ≤ z.re) (h2 : z.re ≤ 3)
    (h3 : |z.im| ≤ 2 * |t| + 1 / 2) : ‖riemannZeta₁ z‖ ≤ 8 * (|t| + 2) ^ 2 := by
  have hre : 0 < z.re := by linarith
  have hz : ‖z‖ ≤ 2 * |t| + 7 / 2 := by
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 3 + (2 * |t| + 1 / 2) := by
          rw [abs_of_pos hre]
          linarith
      _ = _ := by ring
  have hz1 : ‖z - 1‖ ≤ 2 * |t| + 5 / 2 := by
    have hr : |(z - 1).re| ≤ 2 := by
      rw [abs_le]
      constructor <;> simp <;> linarith
    have hi : (z - 1).im = z.im := by simp
    calc ‖z - 1‖ ≤ |(z - 1).re| + |(z - 1).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 2 + (2 * |t| + 1 / 2) := by
          rw [hi]
          linarith
      _ = _ := by ring
  have h := norm_zeta₁_le hre
  have h4 : ‖z‖ * ‖z - 1‖ / z.re ≤ 2 * (‖z‖ * ‖z - 1‖) := by
    rw [div_le_iff₀ hre]
    nlinarith [mul_nonneg (norm_nonneg z) (norm_nonneg (z - 1))]
  have ht := abs_nonneg t
  have h5 : ‖z‖ * ‖z - 1‖ ≤ (2 * |t| + 7 / 2) * (2 * |t| + 5 / 2) :=
    mul_le_mul hz hz1 (norm_nonneg _) (by linarith)
  nlinarith

lemma zeta₁_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta₁ s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | h
  · simp [riemannZeta₁_one]
  · rw [IndependentLandau.zeta₁_eq h]
    exact mul_ne_zero (sub_ne_zero.mpr h) (riemannZeta_ne_zero_of_one_le_re hs)

lemma zeta_ne_zero_of_zeta₁ {s : ℂ} (hs : s ≠ 1) (h : riemannZeta₁ s ≠ 0) : riemannZeta s ≠ 0 := by
  rw [IndependentLandau.zeta₁_eq hs] at h
  exact right_ne_zero_of_mul h

open ArithmeticFunction LSeries.notation ArithmeticFunction.Moebius in
lemma one_le_norm_zeta_mul {s : ℂ} (hs : 1 < s.re) :
    1 ≤ ‖riemannZeta s‖ * ‖riemannZeta (s.re : ℂ)‖ := by
  have hs' : 1 < ((s.re : ℝ) : ℂ).re := by simpa using hs
  have h1 := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at h1
  have hsum1 : LSeriesSummable 1 s := LSeriesSummable_one_iff.mpr hs
  have hsumμ : LSeriesSummable ↗μ s := LSeriesSummable_moebius_iff.mpr hs
  have hnorm1 : Summable fun n => ‖LSeries.term 1 s n‖ := hsum1.norm
  have hnormμ : Summable fun n => ‖LSeries.term ↗μ s n‖ := hsumμ.norm
  have key : ‖LSeries ↗μ s‖ ≤ ‖riemannZeta (s.re : ℂ)‖ := by
    have hterm : ∀ n, ((‖LSeries.term 1 s n‖ : ℝ) : ℂ) = LSeries.term 1 (s.re : ℂ) n := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · rw [LSeries.norm_term_eq, if_neg hn, LSeries.term_of_ne_zero hn]
        simp only [Pi.one_apply, norm_one, ofReal_div, ofReal_one]
        rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
        simp
    have hS : ((∑' n, ‖LSeries.term 1 s n‖ : ℝ) : ℂ) = riemannZeta (s.re : ℂ) := by
      rw [Complex.ofReal_tsum, ← LSeries_one_eq_riemannZeta hs']
      exact tsum_congr hterm
    calc ‖LSeries ↗μ s‖ ≤ ∑' n, ‖LSeries.term ↗μ s n‖ := norm_tsum_le_tsum_norm hnormμ
      _ ≤ ∑' n, ‖LSeries.term 1 s n‖ := by
          refine Summable.tsum_le_tsum (fun n => LSeries.norm_term_le s ?_) hnormμ hnorm1
          simp only [Pi.one_apply, norm_one]
          rw [Complex.norm_intCast]
          exact_mod_cast abs_moebius_le_one
      _ = ‖riemannZeta (s.re : ℂ)‖ := by
          rw [← hS, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun n => norm_nonneg _)]
  calc (1 : ℝ) = ‖riemannZeta s * LSeries ↗μ s‖ := by rw [h1, norm_one]
    _ = ‖riemannZeta s‖ * ‖LSeries ↗μ s‖ := norm_mul _ _
    _ ≤ _ := by gcongr

/-- Lower bound for `ζ₁` to the right of the line `re s = 1`, away from the real axis. -/
lemma le_norm_zeta₁ {s : ℂ} (hs1 : 1 < s.re) (hs2 : s.re ≤ 2) (him : 1 ≤ |s.im|) :
    (s.re - 1) / 3 ≤ ‖riemannZeta₁ s‖ := by
  have hne : s ≠ 1 := by
    rintro rfl
    simp at hs1
  have hσne : ((s.re : ℝ) : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hσ0 : (0 : ℝ) < s.re - 1 := by linarith
  -- upper bound for ζ at the real point
  have hup : ‖riemannZeta₁ (s.re : ℂ)‖ ≤ 3 := by
    have h := norm_zeta₁_le (s := (s.re : ℂ)) (by simpa using (by linarith : (0 : ℝ) < s.re))
    have e1 : ‖((s.re : ℝ) : ℂ)‖ = s.re := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have e2 : ‖((s.re : ℝ) : ℂ) - 1‖ = s.re - 1 := by
      rw [← ofReal_one, ← ofReal_sub, Complex.norm_real, Real.norm_of_nonneg hσ0.le]
    rw [e1, e2, ofReal_re, mul_div_assoc, mul_div_cancel₀ _ (by linarith : s.re ≠ 0)] at h
    · linarith
  have hreal : ‖riemannZeta (s.re : ℂ)‖ * (s.re - 1) ≤ 3 := by
    have e := IndependentLandau.zeta₁_eq hσne
    have e2 : ‖((s.re : ℝ) : ℂ) - 1‖ = s.re - 1 := by
      rw [← ofReal_one, ← ofReal_sub, Complex.norm_real, Real.norm_of_nonneg hσ0.le]
    rw [e, norm_mul, e2] at hup
    linarith
  have hprod := one_le_norm_zeta_mul hs1
  have hs1n : 1 ≤ ‖s - 1‖ := by
    have : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
    simp only [sub_im, one_im, sub_zero] at this
    linarith
  rw [IndependentLandau.zeta₁_eq hne, norm_mul]
  have hz0 : 0 ≤ ‖riemannZeta s‖ := norm_nonneg _
  have hr0 : 0 ≤ ‖riemannZeta (s.re : ℂ)‖ := norm_nonneg _
  -- (σ-1) ≤ (σ-1) ‖ζ s‖ ‖ζ σ‖ ≤ 3 ‖ζ s‖ ≤ 3 ‖s-1‖ ‖ζ s‖
  have h3 : s.re - 1 ≤ 3 * ‖riemannZeta s‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hreal hz0]
  nlinarith

/-- `ζ'/ζ = ζ₁'/ζ₁ - 1/(s - 1)`. -/
lemma logDeriv_zeta_eq {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    deriv riemannZeta s / riemannZeta s =
      deriv riemannZeta₁ s / riemannZeta₁ s - 1 / (s - 1) := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hd : HasDerivAt riemannZeta₁ (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s := by
    have h1 := ((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta hs).hasDerivAt
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    simpa using IndependentLandau.zeta₁_eq hz
  rw [hd.deriv, IndependentLandau.zeta₁_eq hs]
  field_simp
  ring

/-- On `(1, 2]`, `-ζ'/ζ(σ) ≤ 1/(σ - 1) + E`. -/
lemma exists_logDeriv_real_bound : ∃ E : ℝ, 0 ≤ E ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
    -(deriv riemannZeta σ / riemannZeta σ).re ≤ 1 / (σ - 1) + E := by
  have hcont : ContinuousOn (fun s : ℂ => deriv riemannZeta₁ s / riemannZeta₁ s)
      (Complex.ofReal '' Icc 1 2) := by
    refine ContinuousOn.div ?_ differentiable_riemannZeta₁.continuous.continuousOn ?_
    · exact (differentiable_riemannZeta₁.contDiff.continuous_deriv le_rfl).continuousOn
    · rintro _ ⟨x, hx, rfl⟩
      exact zeta₁_ne_zero_of_one_le_re (by simpa using hx.1)
  have hcomp : IsCompact (Complex.ofReal '' Icc (1 : ℝ) 2) :=
    isCompact_Icc.image Complex.continuous_ofReal
  obtain ⟨E, hE⟩ := hcomp.exists_bound_of_continuousOn hcont
  refine ⟨max E 0, le_max_right _ _, fun σ h1 h2 => ?_⟩
  have hne1 : (σ : ℂ) ≠ 1 := by exact_mod_cast h1.ne'
  have hz : riemannZeta σ ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simpa using h1.le)
  rw [logDeriv_zeta_eq hne1 hz, sub_re, neg_sub]
  have h3 : (1 / ((σ : ℂ) - 1)).re = 1 / (σ - 1) := by
    rw [← ofReal_one, ← ofReal_sub, ← ofReal_div, ofReal_re]
  have h4 := hE (σ : ℂ) ⟨σ, ⟨h1.le, h2⟩, rfl⟩
  have h5 := (abs_le.mp ((abs_re_le_norm _).trans h4)).1
  have := le_max_left E 0
  rw [h3]
  linarith

end ZetaRegion

#print axioms ZetaRegion.norm_zeta₁_le_of_strip
#print axioms ZetaRegion.le_norm_zeta₁
#print axioms ZetaRegion.exists_logDeriv_real_bound
