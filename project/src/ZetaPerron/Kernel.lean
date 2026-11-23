import Mathlib

/-! The truncated Perron kernel `∫_{-T}^{T} e^{(c+it)L} / (c+it) dt`, estimated by Cauchy's
theorem on rectangles. Mathlib only. -/

open Complex MeasureTheory Set
open scoped Real Interval

noncomputable section

namespace ZetaPerron

/-- The kernel function `exp (s L) / s`. -/
def kf (L : ℝ) (s : ℂ) : ℂ := Complex.exp (s * (L : ℂ)) / s

/-- The truncated kernel integral over the vertical segment `re s = c`, `|im s| ≤ T`. -/
def kint (L c T : ℝ) : ℂ := ∫ t in (-T)..T, kf L ((c : ℂ) + (t : ℂ) * I)

lemma norm_kf (L : ℝ) (s : ℂ) : ‖kf L s‖ = Real.exp (s.re * L) / ‖s‖ := by
  simp [kf, Complex.norm_exp]

lemma horiz_ne (σ h : ℝ) (hh : h ≠ 0) : (σ : ℂ) + (h : ℂ) * I ≠ 0 := by
  intro H
  have := congrArg Complex.im H
  simp at this
  exact hh this

lemma vert_ne (x t : ℝ) (hx : x ≠ 0) : (x : ℂ) + (t : ℂ) * I ≠ 0 := by
  intro H
  have := congrArg Complex.re H
  simp at this
  exact hx this

lemma cont_kf_horiz (L h : ℝ) (hh : h ≠ 0) :
    Continuous fun σ : ℝ => kf L ((σ : ℂ) + (h : ℂ) * I) := by
  unfold kf
  exact Continuous.div (by fun_prop) (by fun_prop) (fun σ => horiz_ne σ h hh)

lemma cont_kf_vert (L x : ℝ) (hx : x ≠ 0) :
    Continuous fun t : ℝ => kf L ((x : ℂ) + (t : ℂ) * I) := by
  unfold kf
  exact Continuous.div (by fun_prop) (by fun_prop) (fun t => vert_ne x t hx)

lemma cont_inv_horiz (h : ℝ) (hh : h ≠ 0) :
    Continuous fun σ : ℝ => ((σ : ℂ) + (h : ℂ) * I)⁻¹ :=
  Continuous.inv₀ (by fun_prop) (fun σ => horiz_ne σ h hh)

lemma cont_inv_vert (x : ℝ) (hx : x ≠ 0) :
    Continuous fun t : ℝ => ((x : ℂ) + (t : ℂ) * I)⁻¹ :=
  Continuous.inv₀ (by fun_prop) (fun t => vert_ne x t hx)

/-! ### Edge bounds -/

lemma norm_vert_le (L x T : ℝ) (hx : x ≠ 0) (hT : 0 ≤ T) :
    ‖∫ t in (-T)..T, kf L ((x : ℂ) + (t : ℂ) * I)‖ ≤ 2 * T * (Real.exp (x * L) / |x|) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T)
    (C := Real.exp (x * L) / |x|) (f := fun t : ℝ => kf L ((x : ℂ) + (t : ℂ) * I)) ?_
  · have habs : |T - -T| = 2 * T := by
      rw [abs_of_nonneg (by linarith)]; ring
    rw [habs] at h
    linarith [h]
  · intro t _
    rw [norm_kf]
    have hre : ((x : ℂ) + (t : ℂ) * I).re = x := by simp
    rw [hre]
    have hpos : 0 < |x| := abs_pos.mpr hx
    have hle : |x| ≤ ‖(x : ℂ) + (t : ℂ) * I‖ := by
      have := Complex.abs_re_le_norm ((x : ℂ) + (t : ℂ) * I)
      rwa [hre] at this
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hpos hle

lemma norm_horiz_le (L p q h : ℝ) (hpq : p ≤ q) (hh : h ≠ 0) :
    ‖∫ σ in p..q, kf L ((σ : ℂ) + (h : ℂ) * I)‖ ≤ (∫ σ in p..q, Real.exp (σ * L)) / |h| := by
  have hpos : 0 < |h| := abs_pos.mpr hh
  have key : ∀ σ : ℝ, ‖kf L ((σ : ℂ) + (h : ℂ) * I)‖ ≤ Real.exp (σ * L) / |h| := by
    intro σ
    rw [norm_kf]
    have hre : ((σ : ℂ) + (h : ℂ) * I).re = σ := by simp
    have him : ((σ : ℂ) + (h : ℂ) * I).im = h := by simp
    rw [hre]
    have hle : |h| ≤ ‖(σ : ℂ) + (h : ℂ) * I‖ := by
      have := Complex.abs_im_le_norm ((σ : ℂ) + (h : ℂ) * I)
      rwa [him] at this
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hpos hle
  have := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hpq
    (Filter.Eventually.of_forall fun σ _ => key σ)
    (Continuous.intervalIntegrable (by fun_prop) p q)
  rwa [intervalIntegral.integral_div] at this

lemma integral_exp_mul_le_pos {L p q : ℝ} (hL : 0 < L) :
    ∫ σ in p..q, Real.exp (σ * L) ≤ Real.exp (q * L) / L := by
  rw [intervalIntegral.integral_comp_mul_right (fun x => Real.exp x) hL.ne', integral_exp,
    smul_eq_mul, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (p * L)]) hL.le

lemma integral_exp_mul_le_neg {L p q : ℝ} (hL : L < 0) :
    ∫ σ in p..q, Real.exp (σ * L) ≤ Real.exp (p * L) / (-L) := by
  rw [intervalIntegral.integral_comp_mul_right (fun x => Real.exp x) hL.ne, integral_exp,
    smul_eq_mul, inv_mul_eq_div]
  have hL' : 0 < -L := by linarith
  have : (Real.exp (q * L) - Real.exp (p * L)) / L
      = (Real.exp (p * L) - Real.exp (q * L)) / (-L) := by
    rw [div_neg, ← neg_div]; ring
  rw [this]
  exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (q * L)]) hL'.le

lemma integral_exp_mul_le_const {L p q M : ℝ} (hpq : p ≤ q)
    (h : ∀ σ ∈ Icc p q, Real.exp (σ * L) ≤ M) :
    ∫ σ in p..q, Real.exp (σ * L) ≤ (q - p) * M := by
  have := intervalIntegral.integral_mono_on (μ := volume) hpq
    (Continuous.intervalIntegrable (by fun_prop) p q)
    (intervalIntegrable_const (c := M)) h
  simpa using this

/-! ### Cauchy's theorem on a rectangle to the right of the pole -/

lemma differentiableAt_kf (L : ℝ) {s : ℂ} (hs : s ≠ 0) : DifferentiableAt ℂ (kf L) s := by
  unfold kf
  exact ((differentiableAt_id.mul_const _).cexp).div differentiableAt_id hs

lemma rect_kf_right (L p q T : ℝ) (hp : 0 < p) (hpq : p ≤ q) :
    (∫ σ in p..q, kf L ((σ : ℂ) + ((-T : ℝ) : ℂ) * I))
      - (∫ σ in p..q, kf L ((σ : ℂ) + ((T : ℝ) : ℂ) * I))
      + I • (∫ t in (-T)..T, kf L ((q : ℂ) + (t : ℂ) * I))
      - I • (∫ t in (-T)..T, kf L ((p : ℂ) + (t : ℂ) * I)) = 0 := by
  have H : DifferentiableOn ℂ (kf L) ([[p, q]] ×ℂ [[-T, T]]) := by
    intro s hs
    have h1 : s.re ∈ [[p, q]] := hs.1
    rw [Set.uIcc_of_le hpq] at h1
    have hs0 : s ≠ 0 := by
      intro h
      rw [h] at h1
      simp at h1
      linarith [h1.1]
    exact (differentiableAt_kf L hs0).differentiableWithinAt
  exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn (kf L) ⟨p, -T⟩ ⟨q, T⟩ H

/-- Consequence of Cauchy's theorem for a rectangle `[c, R] × [-T, T]`, `0 < c ≤ R`. -/
lemma norm_kint_le_right (L c R T : ℝ) (hc : 0 < c) (hcR : c ≤ R) (hT : 0 < T) :
    ‖kint L c T‖ ≤ 2 * T * (Real.exp (R * L) / R) + 2 * ((∫ σ in c..R, Real.exp (σ * L)) / T) := by
  have H := rect_kf_right L c R T hc hcR
  have hR : 0 < R := lt_of_lt_of_le hc hcR
  have hV := norm_vert_le L R T hR.ne' hT.le
  rw [abs_of_pos hR] at hV
  have hTop := norm_horiz_le L c R T hcR hT.ne'
  have hBot := norm_horiz_le L c R (-T) hcR (neg_ne_zero.mpr hT.ne')
  rw [abs_of_pos hT] at hTop
  rw [abs_neg, abs_of_pos hT] at hBot
  have hEq : I • kint L c T = (∫ σ in c..R, kf L ((σ : ℂ) + ((-T : ℝ) : ℂ) * I))
      - (∫ σ in c..R, kf L ((σ : ℂ) + ((T : ℝ) : ℂ) * I))
      + I • (∫ t in (-T)..T, kf L ((R : ℂ) + (t : ℂ) * I)) := by
    unfold kint
    linear_combination -H
  have hn : ‖kint L c T‖ = ‖I • kint L c T‖ := by
    rw [norm_smul, Complex.norm_I, one_mul]
  rw [hn, hEq]
  have hI : ‖I • (∫ t in (-T)..T, kf L ((R : ℂ) + (t : ℂ) * I))‖
      = ‖∫ t in (-T)..T, kf L ((R : ℂ) + (t : ℂ) * I)‖ := by
    rw [norm_smul, Complex.norm_I, one_mul]
  have h1 := norm_add_le
    ((∫ σ in c..R, kf L ((σ : ℂ) + ((-T : ℝ) : ℂ) * I))
      - (∫ σ in c..R, kf L ((σ : ℂ) + ((T : ℝ) : ℂ) * I)))
    (I • (∫ t in (-T)..T, kf L ((R : ℂ) + (t : ℂ) * I)))
  have h2 := norm_sub_le
    (∫ σ in c..R, kf L ((σ : ℂ) + ((-T : ℝ) : ℂ) * I))
    (∫ σ in c..R, kf L ((σ : ℂ) + ((T : ℝ) : ℂ) * I))
  rw [hI] at h1
  linarith

/-! ### The integral of `1/s` around a rectangle containing the origin -/

lemma log_neg_of_im_neg {z : ℂ} (h : z.im < 0) :
    Complex.log (-z) = Complex.log z + π * I := by
  rw [Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_add_pi_of_im_neg h]
  push_cast; ring

lemma log_neg_of_im_pos {z : ℂ} (h : 0 < z.im) :
    Complex.log (-z) = Complex.log z - π * I := by
  rw [Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_sub_pi_of_im_pos h]
  push_cast; ring

lemma integral_inv_horiz (p q h : ℝ) (hh : h ≠ 0) :
    ∫ σ in p..q, ((σ : ℂ) + (h : ℂ) * I)⁻¹
      = Complex.log ((q : ℂ) + (h : ℂ) * I) - Complex.log ((p : ℂ) + (h : ℂ) * I) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun σ : ℝ => Complex.log ((σ : ℂ) + (h : ℂ) * I)) ?_ ?_
  · intro σ _
    have h1 : HasDerivAt (fun σ : ℝ => (σ : ℂ) + (h : ℂ) * I) 1 σ := by
      simpa using ((hasDerivAt_id σ).ofReal_comp).add_const ((h : ℂ) * I)
    have h2 : (σ : ℂ) + (h : ℂ) * I ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; right; simpa using hh
    simpa using h1.clog_real h2
  · exact (cont_inv_horiz h hh).intervalIntegrable _ _

lemma integral_inv_vert_pos (x T : ℝ) (hx : 0 < x) :
    I * ∫ t in (-T)..T, ((x : ℂ) + (t : ℂ) * I)⁻¹
      = Complex.log ((x : ℂ) + ((T : ℝ) : ℂ) * I) - Complex.log ((x : ℂ) + ((-T : ℝ) : ℂ) * I) := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => Complex.log ((x : ℂ) + (t : ℂ) * I)) ?_ ?_
  · intro t _
    have h1 : HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * I) I t := by
      simpa using (((hasDerivAt_id t).ofReal_comp).mul_const I).const_add (x : ℂ)
    have h2 : (x : ℂ) + (t : ℂ) * I ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left; simpa using hx
    have := h1.clog_real h2
    simpa [div_eq_mul_inv] using this
  · exact (continuous_const.mul (cont_inv_vert x hx.ne')).intervalIntegrable _ _

lemma integral_inv_vert_neg (x T : ℝ) (hx : x < 0) (hT : 0 < T) :
    I * ∫ t in (-T)..T, ((x : ℂ) + (t : ℂ) * I)⁻¹
      = Complex.log ((x : ℂ) + ((T : ℝ) : ℂ) * I) - Complex.log ((x : ℂ) + ((-T : ℝ) : ℂ) * I)
        - 2 * π * I := by
  have hmain : I * ∫ t in (-T)..T, ((x : ℂ) + (t : ℂ) * I)⁻¹
      = Complex.log (-((x : ℂ) + ((T : ℝ) : ℂ) * I))
        - Complex.log (-((x : ℂ) + ((-T : ℝ) : ℂ) * I)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => Complex.log (-((x : ℂ) + (t : ℂ) * I))) ?_ ?_
    · intro t _
      have h0 : HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * I) I t := by
        simpa using (((hasDerivAt_id t).ofReal_comp).mul_const I).const_add (x : ℂ)
      have h1 : HasDerivAt (fun t : ℝ => -((x : ℂ) + (t : ℂ) * I)) (-I) t := h0.neg
      have h2 : -((x : ℂ) + (t : ℂ) * I) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]; left; simpa using hx
      have := h1.clog_real h2
      rw [neg_div_neg_eq, div_eq_mul_inv] at this
      exact this
    · exact (continuous_const.mul (cont_inv_vert x hx.ne)).intervalIntegrable _ _
  rw [hmain, log_neg_of_im_pos (by simpa using hT), log_neg_of_im_neg (by simpa using hT)]
  ring

/-- Cauchy's theorem for `exp (s L) / s` on a rectangle around the origin: the boundary integral
is `2πi`. Proved by removing the singularity and integrating `1/s` explicitly. -/
lemma rect_kf_pole (L a c T : ℝ) (ha : 0 < a) (hc : 0 < c) (hT : 0 < T) :
    (∫ σ in (-a)..c, kf L ((σ : ℂ) + ((-T : ℝ) : ℂ) * I))
      - (∫ σ in (-a)..c, kf L ((σ : ℂ) + ((T : ℝ) : ℂ) * I))
      + I • (∫ t in (-T)..T, kf L ((c : ℂ) + (t : ℂ) * I))
      - I • (∫ t in (-T)..T, kf L (((-a : ℝ) : ℂ) + (t : ℂ) * I)) = 2 * π * I := by
  set g : ℂ → ℂ := dslope (fun s : ℂ => Complex.exp (s * (L : ℂ))) 0 with hg
  have hdiff : Differentiable ℂ (fun s : ℂ => Complex.exp (s * (L : ℂ))) := by fun_prop
  have hgd : DifferentiableOn ℂ g univ :=
    (Complex.differentiableOn_dslope (s := univ) (c := (0 : ℂ)) Filter.univ_mem).mpr
      hdiff.differentiableOn
  have hgs : ∀ s : ℂ, s ≠ 0 → g s = kf L s - s⁻¹ := by
    intro s hs
    rw [hg, dslope_of_ne _ hs, slope_def_field]
    simp only [kf, zero_mul, Complex.exp_zero, sub_zero]
    field_simp
  have Hg := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g ⟨-a, -T⟩ ⟨c, T⟩
    (hgd.mono (subset_univ _))
  have hTn : (-T : ℝ) ≠ 0 := neg_ne_zero.mpr hT.ne'
  have han : (-a : ℝ) ≠ 0 := neg_ne_zero.mpr ha.ne'
  have e1 : (∫ σ in (-a)..c, g ((σ : ℂ) + ((-T : ℝ) : ℂ) * I))
      = (∫ σ in (-a)..c, kf L ((σ : ℂ) + ((-T : ℝ) : ℂ) * I))
        - ∫ σ in (-a)..c, ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)⁻¹ := by
    rw [← intervalIntegral.integral_sub ((cont_kf_horiz L (-T) hTn).intervalIntegrable _ _)
      ((cont_inv_horiz (-T) hTn).intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr (fun σ _ => hgs _ (horiz_ne σ (-T) hTn))
  have e2 : (∫ σ in (-a)..c, g ((σ : ℂ) + ((T : ℝ) : ℂ) * I))
      = (∫ σ in (-a)..c, kf L ((σ : ℂ) + ((T : ℝ) : ℂ) * I))
        - ∫ σ in (-a)..c, ((σ : ℂ) + ((T : ℝ) : ℂ) * I)⁻¹ := by
    rw [← intervalIntegral.integral_sub ((cont_kf_horiz L T hT.ne').intervalIntegrable _ _)
      ((cont_inv_horiz T hT.ne').intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr (fun σ _ => hgs _ (horiz_ne σ T hT.ne'))
  have e3 : (∫ t in (-T)..T, g ((c : ℂ) + (t : ℂ) * I))
      = (∫ t in (-T)..T, kf L ((c : ℂ) + (t : ℂ) * I))
        - ∫ t in (-T)..T, ((c : ℂ) + (t : ℂ) * I)⁻¹ := by
    rw [← intervalIntegral.integral_sub ((cont_kf_vert L c hc.ne').intervalIntegrable _ _)
      ((cont_inv_vert c hc.ne').intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr (fun t _ => hgs _ (vert_ne c t hc.ne'))
  have e4 : (∫ t in (-T)..T, g (((-a : ℝ) : ℂ) + (t : ℂ) * I))
      = (∫ t in (-T)..T, kf L (((-a : ℝ) : ℂ) + (t : ℂ) * I))
        - ∫ t in (-T)..T, (((-a : ℝ) : ℂ) + (t : ℂ) * I)⁻¹ := by
    rw [← intervalIntegral.integral_sub ((cont_kf_vert L (-a) han).intervalIntegrable _ _)
      ((cont_inv_vert (-a) han).intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr (fun t _ => hgs _ (vert_ne (-a) t han))
  have i1 := integral_inv_horiz (-a) c (-T) hTn
  have i2 := integral_inv_horiz (-a) c T hT.ne'
  have i3 := integral_inv_vert_pos c T hc
  have i4 := integral_inv_vert_neg (-a) T (by linarith) hT
  have Hg' : (∫ σ in (-a)..c, g ((σ : ℂ) + ((-T : ℝ) : ℂ) * I))
      - (∫ σ in (-a)..c, g ((σ : ℂ) + ((T : ℝ) : ℂ) * I))
      + I • (∫ t in (-T)..T, g ((c : ℂ) + (t : ℂ) * I))
      - I • (∫ t in (-T)..T, g (((-a : ℝ) : ℂ) + (t : ℂ) * I)) = 0 := Hg
  rw [e1, e2, e3, e4] at Hg'
  simp only [smul_eq_mul] at Hg' ⊢
  linear_combination Hg' + i1 - i2 + i3 - i4

/-- Consequence for a rectangle `[-a, c] × [-T, T]` around the pole. -/
lemma norm_kint_sub_le_left (L a c T : ℝ) (ha : 0 < a) (hc : 0 < c) (hT : 0 < T) :
    ‖kint L c T - 2 * π‖
      ≤ 2 * T * (Real.exp (-a * L) / a) + 2 * ((∫ σ in (-a)..c, Real.exp (σ * L)) / T) := by
  have H := rect_kf_pole L a c T ha hc hT
  have hac : -a ≤ c := by linarith
  have hV := norm_vert_le L (-a) T (neg_ne_zero.mpr ha.ne') hT.le
  rw [abs_neg, abs_of_pos ha] at hV
  have hTop := norm_horiz_le L (-a) c T hac hT.ne'
  have hBot := norm_horiz_le L (-a) c (-T) hac (neg_ne_zero.mpr hT.ne')
  rw [abs_of_pos hT] at hTop
  rw [abs_neg, abs_of_pos hT] at hBot
  have hEq : I • (kint L c T - 2 * π) = (∫ σ in (-a)..c, kf L ((σ : ℂ) + ((T : ℝ) : ℂ) * I))
      - (∫ σ in (-a)..c, kf L ((σ : ℂ) + ((-T : ℝ) : ℂ) * I))
      + I • (∫ t in (-T)..T, kf L (((-a : ℝ) : ℂ) + (t : ℂ) * I)) := by
    unfold kint
    simp only [smul_eq_mul] at H ⊢
    linear_combination H
  have hn : ‖kint L c T - 2 * π‖ = ‖I • (kint L c T - 2 * π)‖ := by
    rw [norm_smul, Complex.norm_I, one_mul]
  rw [hn, hEq]
  have hI : ‖I • (∫ t in (-T)..T, kf L (((-a : ℝ) : ℂ) + (t : ℂ) * I))‖
      = ‖∫ t in (-T)..T, kf L (((-a : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
    rw [norm_smul, Complex.norm_I, one_mul]
  have h1 := norm_add_le
    ((∫ σ in (-a)..c, kf L ((σ : ℂ) + ((T : ℝ) : ℂ) * I))
      - (∫ σ in (-a)..c, kf L ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)))
    (I • (∫ t in (-T)..T, kf L (((-a : ℝ) : ℂ) + (t : ℂ) * I)))
  have h2 := norm_sub_le
    (∫ σ in (-a)..c, kf L ((σ : ℂ) + ((T : ℝ) : ℂ) * I))
    (∫ σ in (-a)..c, kf L ((σ : ℂ) + ((-T : ℝ) : ℂ) * I))
  rw [hI] at h1
  linarith

/-! ### The four kernel bounds -/

/-- `y < 1`: decay bound. -/
theorem kint_bound_neg {L c T : ℝ} (hL : L < 0) (hc : 0 < c) (hT : 0 < T) :
    ‖kint L c T‖ ≤ 2 * Real.exp (c * L) / (T * (-L)) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hq : 0 < 2 * T / ε := by positivity
  set R := c + 2 * T / ε with hR
  have hcR : c ≤ R := by linarith
  have hRpos : 0 < R := by linarith
  have H := norm_kint_le_right L c R T hc hcR hT
  have hint := integral_exp_mul_le_neg (p := c) (q := R) hL
  have hL' : 0 < -L := by linarith
  have h1 : 2 * T * (Real.exp (R * L) / R) ≤ ε := by
    have he : Real.exp (R * L) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hR2 : 2 * T / ε ≤ R := by linarith
    have : Real.exp (R * L) / R ≤ 1 / (2 * T / ε) :=
      div_le_div₀ zero_le_one he hq hR2
    calc 2 * T * (Real.exp (R * L) / R) ≤ 2 * T * (1 / (2 * T / ε)) := by gcongr
      _ = ε := by field_simp
  have h2 : (∫ σ in c..R, Real.exp (σ * L)) / T ≤ Real.exp (c * L) / (-L) / T :=
    div_le_div_of_nonneg_right hint hT.le
  have h3 : 2 * (Real.exp (c * L) / (-L) / T) = 2 * Real.exp (c * L) / (T * (-L)) := by
    field_simp
  linarith

/-- `y ≤ 1`: uniform bound. -/
theorem kint_bound_nonpos {L c T : ℝ} (hL : L ≤ 0) (hc : 0 < c) (hT : 0 < T) :
    ‖kint L c T‖ ≤ 4 * Real.exp (c * L) := by
  have hcR : c ≤ c + T := by linarith
  have H := norm_kint_le_right L c (c + T) T hc hcR hT
  have hint := integral_exp_mul_le_const (L := L) (p := c) (q := c + T) (M := Real.exp (c * L)) hcR
    (fun σ hσ => Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hσ.1 hL))
  have hE : 0 < Real.exp (c * L) := Real.exp_pos _
  have h1 : 2 * T * (Real.exp ((c + T) * L) / (c + T)) ≤ 2 * Real.exp (c * L) := by
    have he : Real.exp ((c + T) * L) ≤ Real.exp (c * L) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hcR hL)
    have hcT : 0 < c + T := by linarith
    rw [← mul_div_assoc, div_le_iff₀ hcT]
    nlinarith [Real.exp_pos ((c + T) * L)]
  have h2 : (∫ σ in c..(c + T), Real.exp (σ * L)) / T ≤ Real.exp (c * L) := by
    rw [div_le_iff₀ hT]
    linarith
  linarith

/-- `y > 1`: decay bound. -/
theorem kint_bound_pos {L c T : ℝ} (hL : 0 < L) (hc : 0 < c) (hT : 0 < T) :
    ‖kint L c T - 2 * π‖ ≤ 2 * Real.exp (c * L) / (T * L) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have ha : 0 < 2 * T / ε := by positivity
  set a := 2 * T / ε with ha_def
  have H := norm_kint_sub_le_left L a c T ha hc hT
  have hint := integral_exp_mul_le_pos (p := -a) (q := c) hL
  have h1 : 2 * T * (Real.exp (-a * L) / a) ≤ ε := by
    have he : Real.exp (-a * L) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have : Real.exp (-a * L) / a ≤ 1 / a := div_le_div_of_nonneg_right he ha.le
    calc 2 * T * (Real.exp (-a * L) / a) ≤ 2 * T * (1 / a) := by gcongr
      _ = ε := by rw [ha_def]; field_simp
  have h2 : (∫ σ in (-a)..c, Real.exp (σ * L)) / T ≤ Real.exp (c * L) / L / T :=
    div_le_div_of_nonneg_right hint hT.le
  have h3 : 2 * (Real.exp (c * L) / L / T) = 2 * Real.exp (c * L) / (T * L) := by
    field_simp
  linarith

/-- `y ≥ 1`: uniform bound. -/
theorem kint_bound_nonneg {L c T : ℝ} (hL : 0 ≤ L) (hc : 0 < c) (hT : 0 < T) :
    ‖kint L c T - 2 * π‖ ≤ (4 + 2 * c / T) * Real.exp (c * L) := by
  have H := norm_kint_sub_le_left L T c T hT hc hT
  have hac : -T ≤ c := by linarith
  have hint := integral_exp_mul_le_const (L := L) (p := -T) (q := c) (M := Real.exp (c * L)) hac
    (fun σ hσ => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hσ.2 hL))
  have hE : 1 ≤ Real.exp (c * L) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have h1 : 2 * T * (Real.exp (-T * L) / T) ≤ 2 * Real.exp (c * L) := by
    have he : Real.exp (-T * L) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have : 2 * T * (Real.exp (-T * L) / T) = 2 * Real.exp (-T * L) := by field_simp
    rw [this]; linarith
  have h2 : (∫ σ in (-T)..c, Real.exp (σ * L)) / T ≤ (c - -T) * Real.exp (c * L) / T :=
    div_le_div_of_nonneg_right hint hT.le
  have h3 : (4 + 2 * c / T) * Real.exp (c * L)
      = 2 * Real.exp (c * L) + 2 * ((c - -T) * Real.exp (c * L) / T) := by
    field_simp; ring
  linarith

end ZetaPerron
