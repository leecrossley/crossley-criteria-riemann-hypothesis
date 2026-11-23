import Mathlib
import ZetaShared.Perron
import Crossley.RealZeros

/-! Growth of `riemannZeta₁ s = (s - 1) ζ(s)` on `re s > -1`, by the second-order
Euler–Maclaurin formula

  `ζ₁(s) = (s + 1)/2 - s (s - 1) (s + 1) ∫_1^∞ P₂(x) x^(-s-2) dx`,  `P₂(x) = ({x}² - {x})/2`. -/

open Complex MeasureTheory Set Filter Topology

noncomputable section
namespace ZetaStrip

/-- The periodic primitive `({x}² - {x})/2` of `{x} - 1/2`. -/
def p2 (x : ℝ) : ℝ := (Int.fract x ^ 2 - Int.fract x) / 2

lemma abs_p2_le (x : ℝ) : |p2 x| ≤ 1 / 8 := by
  unfold p2
  have h0 := Int.fract_nonneg x
  have h1 := (Int.fract_lt_one x).le
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (Int.fract x - 1 / 2)]

lemma p2_natCast (n : ℕ) : p2 n = 0 := by simp [p2]

lemma p2_one : p2 1 = 0 := by simp [p2]

lemma continuous_p2 : Continuous p2 := by
  have h : ContinuousOn (fun y : ℝ => (y ^ 2 - y) / 2) (Icc 0 1) := by fun_prop
  exact h.comp_fract'' (by norm_num)

lemma hasDerivAt_p2 {x : ℝ} (hx : x ∉ range (Int.cast : ℤ → ℝ)) :
    HasDerivAt p2 (Int.fract x - 1 / 2) x := by
  have hfl : (⌊x⌋ : ℝ) < x := lt_of_le_of_ne (Int.floor_le x) (fun h => hx ⟨⌊x⌋, h⟩)
  have hev : p2 =ᶠ[𝓝 x] fun y => ((y - ⌊x⌋) ^ 2 - (y - ⌊x⌋)) / 2 := by
    have hmem : Ioo (⌊x⌋ : ℝ) (⌊x⌋ + 1) ∈ 𝓝 x := Ioo_mem_nhds hfl (Int.lt_floor_add_one x)
    filter_upwards [hmem] with y hy
    have : ⌊y⌋ = ⌊x⌋ := Int.floor_eq_iff.mpr ⟨hy.1.le, hy.2⟩
    simp only [p2, Int.fract, this]
  have hd : HasDerivAt (fun y : ℝ => ((y - ⌊x⌋) ^ 2 - (y - ⌊x⌋)) / 2) (Int.fract x - 1 / 2) x := by
    have h1 : HasDerivAt (fun y : ℝ => y - (⌊x⌋ : ℝ)) 1 x := (hasDerivAt_id x).sub_const _
    have h2 : HasDerivAt (fun y : ℝ => ((y - ⌊x⌋) ^ 2 - (y - ⌊x⌋)) / 2) _ x :=
      ((h1.pow 2).sub h1).div_const 2
    exact h2.congr_deriv (by unfold Int.fract; norm_num; ring)
  exact hd.congr_of_eventuallyEq hev

/-- A real function cut off to `(1, ∞)`, complex valued. -/
def tail (g : ℝ → ℝ) : ℝ → ℂ := (Ioi (1 : ℝ)).indicator (fun t => ((g t : ℝ) : ℂ))

lemma fractTail_eq : Crossley.fractTail = tail Int.fract := rfl

lemma norm_tail_le {g : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B) (hg : ∀ t, |g t| ≤ B) (t : ℝ) :
    ‖tail g t‖ ≤ B := by
  unfold tail
  by_cases h : t ∈ Ioi (1 : ℝ)
  · rw [indicator_of_mem h, Complex.norm_real, Real.norm_eq_abs]; exact hg t
  · rw [indicator_of_notMem h]; simpa using hB

lemma measurable_tail {g : ℝ → ℝ} (hm : Measurable g) : Measurable (tail g) :=
  (Complex.measurable_ofReal.comp hm).indicator measurableSet_Ioi

lemma differentiableAt_mellin_tail {g : ℝ → ℝ} {B : ℝ} (hm : Measurable g)
    (hg : ∀ t, |g t| ≤ B) {w : ℂ} (hw : w.re < 0) : DifferentiableAt ℂ (mellin (tail g)) w := by
  have hB : 0 ≤ B := (abs_nonneg (g 0)).trans (hg 0)
  have hloc : LocallyIntegrableOn (tail g) (Ioi 0) := by
    refine (LocallyIntegrable.mono (locallyIntegrable_const (B : ℝ))
      (measurable_tail hm).aestronglyMeasurable (Eventually.of_forall fun t => ?_)).locallyIntegrableOn _
    simpa [abs_of_nonneg hB] using norm_tail_le hB hg t
  refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := w.re - 1) hloc ?_ hw ?_ (by linarith)
  · refine Asymptotics.IsBigO.of_bound B (Eventually.of_forall fun t => ?_)
    simpa using norm_tail_le hB hg t
  · have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
      (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
    have h2 : tail g =ᶠ[𝓝[>] 0] fun _ => (0 : ℂ) := by
      filter_upwards [h1] with t ht
      simp [tail, not_lt.mpr ht.le]
    exact h2.trans_isBigO (Asymptotics.isBigO_zero _ _)

lemma mellin_tail (g : ℝ → ℝ) (w : ℂ) :
    mellin (tail g) w = ∫ t in Ioi (1 : ℝ), ((g t : ℝ) : ℂ) * (t : ℂ) ^ (w - 1) := by
  unfold mellin
  have h : (fun t : ℝ => (t : ℂ) ^ (w - 1) • tail g t) =
      (Ioi (1 : ℝ)).indicator (fun t => ((g t : ℝ) : ℂ) * (t : ℂ) ^ (w - 1)) := by
    funext t
    by_cases h : t ∈ Ioi (1 : ℝ)
    · simp [tail, indicator_of_mem h, mul_comm]
    · simp [tail, indicator_of_notMem h]
  rw [h, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_right.mpr zero_le_one]

lemma integrableOn_mul_cpow {g : ℝ → ℝ} {B : ℝ} (hm : Measurable g) (hg : ∀ t, |g t| ≤ B)
    {a : ℂ} (ha : a.re < -1) :
    IntegrableOn (fun t : ℝ => ((g t : ℝ) : ℂ) * (t : ℂ) ^ a) (Ioi 1) := by
  have hint : IntegrableOn (fun t : ℝ => (t : ℂ) ^ a) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt ha zero_lt_one
  refine Integrable.mono' (hint.norm.const_mul B) ?_ ?_
  · exact (Complex.measurable_ofReal.comp hm).aestronglyMeasurable.mul hint.aestronglyMeasurable
  · refine Eventually.of_forall fun t => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hg t) (norm_nonneg _)

lemma abs_fract_le (t : ℝ) : |Int.fract t| ≤ 1 := by
  rw [abs_of_nonneg (Int.fract_nonneg t)]; exact (Int.fract_lt_one t).le

/-- Integration by parts: for `re s > 0`,
`∫_1^∞ {x} x^(-s-1) dx - (s+1) ∫_1^∞ P₂(x) x^(-s-2) dx = 1/(2s)`. -/
lemma mellin_fract_sub {s : ℂ} (hs : 0 < s.re) :
    mellin Crossley.fractTail (-s) - (s + 1) * mellin (tail p2) (-s - 1) = 1 / (2 * s) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hs1 : -s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hsn : -s ≠ 0 := neg_ne_zero.mpr hs0
  let f' : ℝ → ℂ := fun x => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) -
    (s + 1) * (((p2 x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1 - 1))
  let F : ℝ → ℂ := fun x => ((p2 x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) - 1 / (2 * s) * (x : ℂ) ^ (-s)
  have hint1 : IntegrableOn (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) (Ioi 1) :=
    integrableOn_mul_cpow measurable_fract abs_fract_le (by simp; linarith)
  have hint2 : IntegrableOn (fun t : ℝ => ((p2 t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1 - 1)) (Ioi 1) :=
    integrableOn_mul_cpow continuous_p2.measurable abs_p2_le (by simp; linarith)
  have hint : IntegrableOn f' (Ioi 1) := hint1.sub (hint2.const_mul (s + 1))
  have hI : ∫ t in Ioi (1 : ℝ), f' t =
      mellin Crossley.fractTail (-s) - (s + 1) * mellin (tail p2) (-s - 1) := by
    rw [Crossley.mellin_fractTail, mellin_tail]
    simp only [f']
    rw [integral_sub hint1 (hint2.const_mul (s + 1)), integral_const_mul]
  have hFTC : ∀ n : ℕ, 1 ≤ n → ∫ x in (1 : ℝ)..n, f' x = F n - F 1 := by
    intro n hn
    have hle : (1 : ℝ) ≤ n := by exact_mod_cast hn
    refine integral_eq_of_hasDerivAt_off_countable_of_le F f' hle
      (s := range (Int.cast : ℤ → ℝ)) (countable_range _) ?_ ?_ ?_
    · intro x hx
      have hx0 : x ≠ 0 := (zero_lt_one.trans_le hx.1).ne'
      have hc1 : ContinuousAt (fun x : ℝ => ((p2 x : ℝ) : ℂ)) x :=
        (Complex.continuous_ofReal.comp continuous_p2).continuousAt
      have hc2 : ContinuousAt (fun x : ℝ => (x : ℂ) ^ (-s - 1)) x :=
        Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hx0)
      have hc3 : ContinuousAt (fun x : ℝ => (x : ℂ) ^ (-s)) x :=
        Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hx0)
      exact ((hc1.mul hc2).sub (continuousAt_const.mul hc3)).continuousWithinAt
    · intro x hx
      have hx0 : x ≠ 0 := (zero_lt_one.trans hx.1.1).ne'
      have h1 := (hasDerivAt_p2 hx.2).ofReal_comp
      have h2 := hasDerivAt_ofReal_cpow_const hx0 hs1
      have h3 := hasDerivAt_ofReal_cpow_const hx0 hsn
      have h4 := (h1.mul h2).sub (h3.const_mul (1 / (2 * s)))
      have h5 : HasDerivAt F _ x := h4
      refine h5.congr_deriv ?_
      simp only [f']
      push_cast
      field_simp
      ring
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mpr
        (hint.mono_set Ioc_subset_Ioi_self)
  have hlim1 : Tendsto (fun n : ℕ => ∫ x in (1 : ℝ)..n, f' x) atTop
      (𝓝 (∫ t in Ioi (1 : ℝ), f' t)) :=
    intervalIntegral_tendsto_integral_Ioi 1 hint tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ => ((n : ℝ) : ℂ) ^ (-s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := (tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    show (n : ℝ) ^ (-s.re) = ‖((n : ℝ) : ℂ) ^ (-s)‖
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0]; simp
  have hlim2 : Tendsto (fun n : ℕ => ∫ x in (1 : ℝ)..n, f' x) atTop (𝓝 (1 / (2 * s))) := by
    have h : Tendsto (fun n : ℕ => 1 / (2 * s) - 1 / (2 * s) * ((n : ℝ) : ℂ) ^ (-s)) atTop
        (𝓝 (1 / (2 * s) - 1 / (2 * s) * 0)) := tendsto_const_nhds.sub (hpow.const_mul _)
    rw [mul_zero, sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [hFTC n hn]
    simp only [F, p2_natCast, p2_one, Complex.ofReal_zero, zero_mul, zero_sub, Complex.ofReal_one,
      Complex.one_cpow, mul_one, Complex.ofReal_natCast]
    ring
  rw [← hI]
  exact tendsto_nhds_unique hlim1 hlim2

/-- `∫_1^∞ P₂(x) x^(-s-2) dx`, holomorphic on `re s > -1`. -/
def kernel (s : ℂ) : ℂ := mellin (tail p2) (-s - 1)

lemma differentiableAt_kernel {s : ℂ} (hs : -1 < s.re) : DifferentiableAt ℂ kernel s := by
  have hw : (-s - 1).re < 0 := by simp; linarith
  exact (differentiableAt_mellin_tail continuous_p2.measurable abs_p2_le hw).comp s
    (differentiableAt_id.neg.sub_const 1)

lemma norm_kernel_le {s : ℂ} (hs : -1 < s.re) : ‖kernel s‖ ≤ 1 / 8 / (s.re + 1) := by
  unfold kernel
  rw [mellin_tail]
  have hint : IntegrableOn (fun t : ℝ => (1 / 8 : ℝ) * t ^ (-s.re - 2)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (1 : ℝ))) hint
    (f := fun t : ℝ => ((p2 t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1 - 1)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      have e : (-s - 1 - 1).re = -s.re - 2 := by simp; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right (abs_p2_le t) (Real.rpow_nonneg ht0.le _))
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one] at h
  have e : (1 / 8 : ℝ) * (-(1 : ℝ) ^ (-s.re - 2 + 1) / (-s.re - 2 + 1)) = 1 / 8 / (s.re + 1) := by
    rw [Real.one_rpow, show (-s.re - 2 + 1) = -(s.re + 1) by ring, neg_div_neg_eq]; ring
  rwa [e] at h

/-- The second-order Euler–Maclaurin formula on `re s > -1`. -/
theorem zeta₁_eq_kernel {s : ℂ} (hs : -1 < s.re) :
    riemannZeta₁ s = (s + 1) / 2 - s * (s - 1) * (s + 1) * kernel s := by
  let D : ℂ → ℂ := fun s => riemannZeta₁ s - ((s + 1) / 2 - s * (s - 1) * (s + 1) * kernel s)
  have hU : IsOpen {s : ℂ | -1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hD : DifferentiableOn ℂ D {s : ℂ | -1 < s.re} := by
    intro z hz
    have hk : DifferentiableAt ℂ kernel z := differentiableAt_kernel hz
    exact ((differentiable_riemannZeta₁ z).sub (((differentiableAt_id.add_const 1).div_const 2).sub
      (((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
        (differentiableAt_id.add_const 1)).mul hk))).differentiableWithinAt
  have h0 : D =ᶠ[𝓝 2] 0 := by
    have h : ∀ᶠ z : ℂ in 𝓝 2, 0 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [h] with z hz
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz
    have e1 := Crossley.zeta₁_eq_fract hz
    have e2 := mellin_fract_sub hz
    have e3 : mellin Crossley.fractTail (-z) = 1 / (2 * z) + (z + 1) * kernel z := by
      unfold kernel; rw [← e2]; ring
    simp only [D, Pi.zero_apply]
    rw [e1, e3]; field_simp; ring
  have h := (hD.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_re_gt (-1)).isPreconnected (show (-1 : ℝ) < (2 : ℂ).re by norm_num) h0 hs
  simpa [D, sub_eq_zero] using h

/-- Polynomial growth of `(s - 1) ζ(s)` on `re s ≥ -4/5`. -/
theorem norm_zeta₁_le_left {s : ℂ} (hs : -4 / 5 ≤ s.re) :
    ‖riemannZeta₁ s‖ ≤ ‖s + 1‖ / 2 + 5 / 8 * ‖s‖ * ‖s - 1‖ * ‖s + 1‖ := by
  have hs1 : -1 < s.re := by linarith
  rw [zeta₁_eq_kernel hs1]
  have hk : ‖kernel s‖ ≤ 5 / 8 := by
    refine (norm_kernel_le hs1).trans ?_
    rw [div_le_iff₀ (by linarith)]; linarith
  calc ‖(s + 1) / 2 - s * (s - 1) * (s + 1) * kernel s‖
      ≤ ‖(s + 1) / 2‖ + ‖s * (s - 1) * (s + 1) * kernel s‖ := norm_sub_le _ _
    _ = ‖s + 1‖ / 2 + ‖s‖ * ‖s - 1‖ * ‖s + 1‖ * ‖kernel s‖ := by
        rw [norm_div, norm_mul, norm_mul, norm_mul]; simp
    _ ≤ ‖s + 1‖ / 2 + ‖s‖ * ‖s - 1‖ * ‖s + 1‖ * (5 / 8) := by gcongr
    _ = ‖s + 1‖ / 2 + 5 / 8 * ‖s‖ * ‖s - 1‖ * ‖s + 1‖ := by ring

end ZetaStrip
