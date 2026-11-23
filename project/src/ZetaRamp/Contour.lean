import Mathlib
import ZetaRamp.Inversion

/-! The contour shift. On the line `re s = 1 + 1/u` the part `|t| ≤ T` is moved to
`re s = 1 - c / log (T + 2)` by Cauchy's theorem for a rectangle; the part `|t| > T` stays. -/

open Complex MeasureTheory Set Filter Topology
open scoped Interval

noncomputable section

namespace ZetaRamp

open IndependentLandau ZetaShared

/-- `∫ (1 + |t|)^(-r) dt` over the real line. -/
def J (r : ℝ) : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-r)

lemma J_nonneg (r : ℝ) : 0 ≤ J r :=
  integral_nonneg fun t => Real.rpow_nonneg (by positivity) _

lemma integrable_J {r : ℝ} (hr : 1 < r) : Integrable (fun t : ℝ => (1 + |t|) ^ (-r)) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := r)
    (by rw [Module.finrank_self]; simpa using hr)
  simpa only [Real.norm_eq_abs] using h

lemma norm_setIntegral_le_of_bound {g : ℝ → ℂ} {bd : ℝ → ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    (hbd : Integrable bd) (hbd0 : ∀ t, 0 ≤ bd t) (hg : ∀ t ∈ S, ‖g t‖ ≤ bd t) :
    ‖∫ t in S, g t‖ ≤ ∫ t, bd t :=
  (norm_integral_le_of_norm_le hbd.restrict ((ae_restrict_iff' hS).mpr (ae_of_all _ hg))).trans
    (setIntegral_le_integral hbd (ae_of_all _ hbd0))

lemma norm_integrand_le {c B : ℝ}
    (hB : ∀ s ∈ region c, s.re ≤ 2 → ‖psi s‖ ≤ B * (1 + |s.im|) ^ (-(3 / 2) : ℝ))
    {x y : ℝ} (hmem : (x : ℂ) + (y : ℂ) * I ∈ region c) (hx : x ≤ 2) (u : ℝ) :
    ‖psi ((x : ℂ) + (y : ℂ) * I) * cexp (((x : ℂ) + (y : ℂ) * I) * u)‖
      ≤ B * (1 + |y|) ^ (-(3 / 2) : ℝ) * Real.exp (x * u) := by
  rw [norm_mul, Complex.norm_exp]
  have hre : (((x : ℂ) + (y : ℂ) * I) * u).re = x * u := by simp
  rw [hre]
  exact mul_le_mul_of_nonneg_right (norm_psi_line_le hB hmem hx) (Real.exp_pos _).le

/-- The bound for `rampH u` obtained from the contour shift at height `T`. -/
theorem rampH_bound {c C B : ℝ} (h : RegionData c C) (hc : c ≤ 1 / 4) (hB0 : 0 ≤ B)
    (hB : ∀ s ∈ region c, s.re ≤ 2 → ‖psi s‖ ≤ B * (1 + |s.im|) ^ (-(3 / 2) : ℝ))
    {u T : ℝ} (hu : 1 ≤ u) (hT : 0 ≤ T) :
    |rampH u| ≤ B * Real.exp u * ((J (5 / 4) + 4) * Real.exp 1 * (1 + T) ^ (-(1 / 4) : ℝ)
      + J (3 / 2) * Real.exp (-(c / Real.log (T + 2)) * u)) := by
  have hc0 := h.c_pos
  have hu0 : 0 < u := by linarith
  set b : ℝ := 1 + 1 / u with hbdef
  have hb1 : 1 < b := by
    have : 0 < 1 / u := by positivity
    rw [hbdef]; linarith
  have hb2 : b ≤ 2 := by
    have : 1 / u ≤ 1 := by rw [div_le_one hu0]; exact hu
    rw [hbdef]; linarith
  have hbu : b * u = u + 1 := by rw [hbdef]; field_simp
  have hLT : 1 / 2 < Real.log (T + 2) := by
    have := half_lt_log_abs_add_two T
    rwa [abs_of_nonneg hT] at this
  set η : ℝ := c / Real.log (T + 2) with hηdef
  have hη0 : 0 ≤ η := div_nonneg hc0.le (by linarith)
  have hη1 : η ≤ 1 / 2 := by
    rw [hηdef, div_le_iff₀ (by linarith)]; nlinarith
  have hle1 : 1 - η ≤ b := by linarith
  have hTT : -T ≤ T := by linarith
  have hT1 : 0 < 1 + T := by linarith
  set f : ℂ → ℂ := fun s => psi s * cexp (s * u) with hfdef
  have hinv := inversion h hc hB0 hB hb1 hb2 hu0
  -- pointwise bounds
  have hbd_line : ∀ t : ℝ, ‖f ((b : ℂ) + (t : ℂ) * I)‖
      ≤ B * (1 + |t|) ^ (-(3 / 2) : ℝ) * Real.exp (b * u) :=
    fun t => norm_integrand_le hB (line_mem_region hc0 hb1.le t) hb2 u
  have hbd_rect : ∀ x y : ℝ, 1 - η ≤ x → x ≤ b → |y| ≤ T →
      ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ B * (1 + |y|) ^ (-(3 / 2) : ℝ) * Real.exp (x * u) :=
    fun x y hx1 hx2 hy =>
      norm_integrand_le hB (mem_region_of_le hc0 hy hx1) (hx2.trans hb2) u
  -- integrability on the line
  have hfcont : Continuous fun t : ℝ => f ((b : ℂ) + (t : ℂ) * I) :=
    (continuous_psi_line h hc hb1.le).mul (by fun_prop)
  have hI32 := integrable_J (r := 3 / 2) (by norm_num)
  have hI54 := integrable_J (r := 5 / 4) (by norm_num)
  have hfi : Integrable fun t : ℝ => f ((b : ℂ) + (t : ℂ) * I) :=
    Integrable.mono' ((hI32.const_mul B).mul_const (Real.exp (b * u)))
      hfcont.aestronglyMeasurable (ae_of_all _ hbd_line)
  have hsplit : (∫ t in Ioc (-T) T, f ((b : ℂ) + (t : ℂ) * I))
      + ∫ t in (Ioc (-T) T)ᶜ, f ((b : ℂ) + (t : ℂ) * I)
      = ∫ t : ℝ, f ((b : ℂ) + (t : ℂ) * I) := integral_add_compl measurableSet_Ioc hfi
  -- the tails
  have htail : ‖∫ t in (Ioc (-T) T)ᶜ, f ((b : ℂ) + (t : ℂ) * I)‖
      ≤ B * Real.exp (b * u) * (1 + T) ^ (-(1 / 4) : ℝ) * J (5 / 4) := by
    have hbd : Integrable fun t : ℝ =>
        B * Real.exp (b * u) * (1 + T) ^ (-(1 / 4) : ℝ) * (1 + |t|) ^ (-(5 / 4) : ℝ) :=
      hI54.const_mul _
    refine (norm_setIntegral_le_of_bound measurableSet_Ioc.compl hbd
      (fun t => by positivity) fun t ht => ?_).trans (le_of_eq ?_)
    · have htT : T ≤ |t| := by
        rw [mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at ht
        rcases ht with ht | ht
        · exact (by linarith : T ≤ -t).trans (neg_le_abs t)
        · exact ht.le.trans (le_abs_self t)
      have hpow : (1 + |t|) ^ (-(3 / 2) : ℝ)
          ≤ (1 + T) ^ (-(1 / 4) : ℝ) * (1 + |t|) ^ (-(5 / 4) : ℝ) := by
        have h1 : (1 + |t|) ^ (-(3 / 2) : ℝ)
            = (1 + |t|) ^ (-(1 / 4) : ℝ) * (1 + |t|) ^ (-(5 / 4) : ℝ) := by
          rw [← Real.rpow_add (by positivity)]
          congr 1
          norm_num
        rw [h1]
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos hT1 (by linarith) (by norm_num))
          (Real.rpow_nonneg (by positivity) _)
      calc ‖f ((b : ℂ) + (t : ℂ) * I)‖
          ≤ B * (1 + |t|) ^ (-(3 / 2) : ℝ) * Real.exp (b * u) := hbd_line t
        _ ≤ B * ((1 + T) ^ (-(1 / 4) : ℝ) * (1 + |t|) ^ (-(5 / 4) : ℝ)) * Real.exp (b * u) := by
            gcongr
        _ = B * Real.exp (b * u) * (1 + T) ^ (-(1 / 4) : ℝ) * (1 + |t|) ^ (-(5 / 4) : ℝ) := by
            ring
    · rw [integral_const_mul]; rfl
  -- Cauchy's theorem on the rectangle
  have Hdiff : DifferentiableOn ℂ f ([[1 - η, b]] ×ℂ [[-T, T]]) := by
    intro s hs
    rw [mem_reProdIm, uIcc_of_le hle1, uIcc_of_le hTT] at hs
    have hmem : s ∈ region c := by
      have := mem_region_of_le hc0 (x := s.re) (y := s.im) (T := T) (abs_le.mpr hs.2) hs.1.1
      rwa [Complex.re_add_im] at this
    exact ((analyticAt_psi h hc hmem).differentiableAt.mul
      (by fun_prop)).differentiableWithinAt
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ⟨1 - η, -T⟩ ⟨b, T⟩ Hdiff
  dsimp only at hrect
  have hbot : ‖∫ x in (1 - η)..b, f ((x : ℂ) + ((-T : ℝ) : ℂ) * I)‖
      ≤ B * (1 + T) ^ (-(3 / 2) : ℝ) * Real.exp (b * u) * |b - (1 - η)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [uIoc_of_le hle1] at hx
    have h1 := hbd_rect x (-T) hx.1.le hx.2 (by rw [abs_neg, abs_of_nonneg hT])
    rw [abs_neg, abs_of_nonneg hT] at h1
    refine h1.trans ?_
    gcongr
    exact hx.2
  have htop : ‖∫ x in (1 - η)..b, f ((x : ℂ) + (T : ℂ) * I)‖
      ≤ B * (1 + T) ^ (-(3 / 2) : ℝ) * Real.exp (b * u) * |b - (1 - η)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [uIoc_of_le hle1] at hx
    have h1 := hbd_rect x T hx.1.le hx.2 (by rw [abs_of_nonneg hT])
    rw [abs_of_nonneg hT] at h1
    refine h1.trans ?_
    gcongr
    exact hx.2
  have hleft : ‖∫ y in (-T)..T, f (((1 - η : ℝ) : ℂ) + (y : ℂ) * I)‖
      ≤ B * Real.exp ((1 - η) * u) * J (3 / 2) := by
    rw [intervalIntegral.integral_of_le hTT]
    have hbd : Integrable fun t : ℝ =>
        B * Real.exp ((1 - η) * u) * (1 + |t|) ^ (-(3 / 2) : ℝ) := hI32.const_mul _
    refine (norm_setIntegral_le_of_bound measurableSet_Ioc hbd
      (fun t => by positivity) fun t ht => ?_).trans (le_of_eq ?_)
    · refine (hbd_rect (1 - η) t le_rfl hle1 (abs_le.mpr ⟨ht.1.le, ht.2⟩)).trans (le_of_eq ?_)
      ring
    · rw [integral_const_mul]; rfl
  have hmid : ‖∫ t in Ioc (-T) T, f ((b : ℂ) + (t : ℂ) * I)‖
      ≤ ‖∫ y in (-T)..T, f (((1 - η : ℝ) : ℂ) + (y : ℂ) * I)‖
        + ‖∫ x in (1 - η)..b, f ((x : ℂ) + ((-T : ℝ) : ℂ) * I)‖
        + ‖∫ x in (1 - η)..b, f ((x : ℂ) + (T : ℂ) * I)‖ := by
    rw [← intervalIntegral.integral_of_le hTT]
    simp only [smul_eq_mul] at hrect
    have e : I * (∫ y in (-T)..T, f ((b : ℂ) + (y : ℂ) * I))
        = I * (∫ y in (-T)..T, f (((1 - η : ℝ) : ℂ) + (y : ℂ) * I))
          - (∫ x in (1 - η)..b, f ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
          + ∫ x in (1 - η)..b, f ((x : ℂ) + (T : ℂ) * I) := by
      linear_combination hrect
    calc ‖∫ y in (-T)..T, f ((b : ℂ) + (y : ℂ) * I)‖
        = ‖I * (∫ y in (-T)..T, f ((b : ℂ) + (y : ℂ) * I))‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ ‖I * (∫ y in (-T)..T, f (((1 - η : ℝ) : ℂ) + (y : ℂ) * I))‖
          + ‖∫ x in (1 - η)..b, f ((x : ℂ) + ((-T : ℝ) : ℂ) * I)‖
          + ‖∫ x in (1 - η)..b, f ((x : ℂ) + (T : ℂ) * I)‖ := by
          rw [e]
          exact (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
      _ = _ := by rw [norm_mul, Complex.norm_I, one_mul]
  -- assembly
  have habs : |rampH u| = ‖((rampH u : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hpi : (2 * Real.pi)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    linarith [Real.pi_gt_three]
  have hnorm : ‖((rampH u : ℝ) : ℂ)‖ ≤ ‖∫ t : ℝ, f ((b : ℂ) + (t : ℂ) * I)‖ := by
    rw [hinv, norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_left (norm_nonneg _) hpi
  have htotal : ‖∫ t : ℝ, f ((b : ℂ) + (t : ℂ) * I)‖
      ≤ B * Real.exp ((1 - η) * u) * J (3 / 2)
        + B * (1 + T) ^ (-(3 / 2) : ℝ) * Real.exp (b * u) * |b - (1 - η)|
        + B * (1 + T) ^ (-(3 / 2) : ℝ) * Real.exp (b * u) * |b - (1 - η)|
        + B * Real.exp (b * u) * (1 + T) ^ (-(1 / 4) : ℝ) * J (5 / 4) := by
    rw [← hsplit]
    refine (norm_add_le _ _).trans ?_
    linarith
  rw [habs]
  refine hnorm.trans (htotal.trans ?_)
  have ha : |b - (1 - η)| ≤ 2 := by
    rw [abs_of_nonneg (by linarith)]; linarith
  have hP : (1 + T) ^ (-(3 / 2) : ℝ) ≤ (1 + T) ^ (-(1 / 4) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hJ32 := J_nonneg (3 / 2)
  have hJ54 := J_nonneg (5 / 4)
  have e1 : Real.exp (b * u) = Real.exp u * Real.exp 1 := by rw [hbu, Real.exp_add]
  have e2 : Real.exp ((1 - η) * u) = Real.exp u * Real.exp (-η * u) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e1, e2]
  have hstep : B * (1 + T) ^ (-(3 / 2) : ℝ) * (Real.exp u * Real.exp 1) * |b - (1 - η)|
      ≤ B * (1 + T) ^ (-(1 / 4) : ℝ) * (Real.exp u * Real.exp 1) * 2 := by
    gcongr
  calc B * (Real.exp u * Real.exp (-η * u)) * J (3 / 2)
        + B * (1 + T) ^ (-(3 / 2) : ℝ) * (Real.exp u * Real.exp 1) * |b - (1 - η)|
        + B * (1 + T) ^ (-(3 / 2) : ℝ) * (Real.exp u * Real.exp 1) * |b - (1 - η)|
        + B * (Real.exp u * Real.exp 1) * (1 + T) ^ (-(1 / 4) : ℝ) * J (5 / 4)
      ≤ B * (Real.exp u * Real.exp (-η * u)) * J (3 / 2)
        + B * (1 + T) ^ (-(1 / 4) : ℝ) * (Real.exp u * Real.exp 1) * 2
        + B * (1 + T) ^ (-(1 / 4) : ℝ) * (Real.exp u * Real.exp 1) * 2
        + B * (Real.exp u * Real.exp 1) * (1 + T) ^ (-(1 / 4) : ℝ) * J (5 / 4) := by
        linarith
    _ = B * Real.exp u * ((J (5 / 4) + 4) * Real.exp 1 * (1 + T) ^ (-(1 / 4) : ℝ)
        + J (3 / 2) * Real.exp (-η * u)) := by ring

end ZetaRamp
