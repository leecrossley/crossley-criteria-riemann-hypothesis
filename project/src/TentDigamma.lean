import Mathlib

/-!
# Digamma partial fractions for the tent mass identity

Mathlib-only lemmas used by `TentMassIdentity`.

1. The partial-fraction series `Complex.digamma w + γ = ∑_{m ≥ 0} (1/(m+1) - 1/(w+m))` on
   `0 < w.re`. It is proved on `(0, ∞)` from the convexity of `log ∘ Gamma` (Bohr–Mollerup) and
   carried to the half-plane by the identity theorem.
2. Termwise bounds: `‖1/(m+1) - 1/(w+m)‖ ≤ ‖w - 1‖ / δ · 1/(m+1)^2` on `δ ≤ w.re`, and
   `‖1/(m+1) - 1/(w+m)‖ ≤ √|y| / ((m+1)√(m+1))` on the line `w = 1 + i y`. The first gives
   `‖digamma w + γ‖ ≤ C ‖w - 1‖ / δ`.
3. The logarithmic derivative of `Gammaℝ s = π^(-s/2) Γ(s/2)` on `0 < s.re`, namely
   `-(log π)/2 + digamma (s/2) / 2`.
4. The value `∑_{m ≥ 0} (1/(2m+1) - 1/(2m+2)) = log 2`, from `digamma (1/2) = -2 log 2 - γ`.
-/

open Complex Set Filter Topology

noncomputable section

namespace TentDigamma

local notation "γ" => Real.eulerMascheroniConstant

/-! ## 1. The terms of the series -/

/-- The `m`-th partial-fraction term `1/(m+1) - 1/(w+m)` of `digamma w + γ`. -/
def digammaTerm (w : ℂ) (m : ℕ) : ℂ :=
  1 / ((m : ℂ) + 1) - 1 / (w + (m : ℂ))

lemma add_natCast_ne_zero {w : ℂ} (hw : 0 < w.re) (m : ℕ) : w + (m : ℂ) ≠ 0 := by
  intro h
  have h' := congrArg Complex.re h
  simp only [add_re, natCast_re, zero_re] at h'
  linarith [Nat.cast_nonneg (α := ℝ) m]

lemma natCast_add_one_ne_zero (m : ℕ) : (m : ℂ) + 1 ≠ 0 := by
  exact_mod_cast Nat.succ_ne_zero m

lemma digammaTerm_eq {w : ℂ} (m : ℕ) (hw : w + (m : ℂ) ≠ 0) :
    digammaTerm w m = (w - 1) / (((m : ℂ) + 1) * (w + (m : ℂ))) := by
  unfold digammaTerm
  rw [div_sub_div _ _ (natCast_add_one_ne_zero m) hw]
  congr 1
  ring

lemma norm_natCast_add_one (m : ℕ) : ‖(m : ℂ) + 1‖ = (m : ℝ) + 1 := by
  rw [show (m : ℂ) + 1 = (((m : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

/-- Termwise bound on a right half-plane `δ ≤ w.re` with `0 < δ ≤ 1`. -/
lemma norm_digammaTerm_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {w : ℂ} (hw : δ ≤ w.re) (m : ℕ) :
    ‖digammaTerm w m‖ ≤ ‖w - 1‖ / δ * (1 / ((m : ℝ) + 1) ^ 2) := by
  have hw0 : 0 < w.re := hδ.trans_le hw
  rw [digammaTerm_eq m (add_natCast_ne_zero hw0 m), norm_div, norm_mul, norm_natCast_add_one]
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hre : w.re + m ≤ ‖w + (m : ℂ)‖ := by
    have h := Complex.re_le_norm (w + (m : ℂ))
    simpa using h
  have hlow : δ * ((m : ℝ) + 1) ≤ ‖w + (m : ℂ)‖ := by
    nlinarith [mul_nonneg (sub_nonneg.2 hδ1) (Nat.cast_nonneg (α := ℝ) m)]
  calc ‖w - 1‖ / (((m : ℝ) + 1) * ‖w + (m : ℂ)‖)
      ≤ ‖w - 1‖ / (((m : ℝ) + 1) * (δ * ((m : ℝ) + 1))) := by
        apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left hlow hm.le
    _ = ‖w - 1‖ / δ * (1 / ((m : ℝ) + 1) ^ 2) := by
        field_simp

lemma summable_one_div_add_one_sq : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  simpa [Nat.cast_add, Nat.cast_one] using h

lemma summable_digammaTerm {w : ℂ} (hw : 0 < w.re) : Summable (digammaTerm w) :=
  Summable.of_norm_bounded (summable_one_div_add_one_sq.mul_left (‖w - 1‖ / min w.re 1))
    (fun m => norm_digammaTerm_le (lt_min hw one_pos) (min_le_right _ _) (min_le_left _ _) m)

lemma isOpen_re_pos : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re

lemma differentiableOn_tsum_digammaTerm :
    DifferentiableOn ℂ (fun w => ∑' m, digammaTerm w m) {w : ℂ | 0 < w.re} := by
  intro w₀ hw₀
  have hw₀' : 0 < w₀.re := hw₀
  set r : ℝ := w₀.re / 2 with hr_def
  have hr : 0 < r := by positivity
  have hball : ∀ w ∈ Metric.ball w₀ r, r ≤ w.re ∧ ‖w - 1‖ ≤ ‖w₀ - 1‖ + r := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have h1 : |(w - w₀).re| ≤ ‖w - w₀‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re] at h1
    refine ⟨by linarith [(abs_le.mp h1).1], ?_⟩
    calc ‖w - 1‖ = ‖(w - w₀) + (w₀ - 1)‖ := by ring_nf
      _ ≤ ‖w - w₀‖ + ‖w₀ - 1‖ := norm_add_le _ _
      _ ≤ ‖w₀ - 1‖ + r := by linarith
  have hd : DifferentiableOn ℂ (fun w => ∑' m, digammaTerm w m) (Metric.ball w₀ r) := by
    refine differentiableOn_tsum_of_summable_norm
      (summable_one_div_add_one_sq.mul_left ((‖w₀ - 1‖ + r) / min r 1)) (fun m => ?_)
      Metric.isOpen_ball (fun m w hw => ?_)
    · intro w hw
      have hne := add_natCast_ne_zero (hr.trans_le (hball w hw).1) m
      unfold digammaTerm
      refine DifferentiableAt.differentiableWithinAt ?_
      fun_prop (disch := exact hne)
    · obtain ⟨h1, h2⟩ := hball w hw
      refine (norm_digammaTerm_le (lt_min hr one_pos) (min_le_right _ _)
        ((min_le_left _ _).trans h1) m).trans ?_
      gcongr
  exact (hd.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).differentiableWithinAt

/-! ## 2. The series on the positive reals -/

lemma digamma_add_nat {w : ℂ} (hw : 0 < w.re) (N : ℕ) :
    Complex.digamma (w + N) = Complex.digamma w + ∑ m ∈ Finset.range N, (w + m)⁻¹ := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hne : ∀ k : ℕ, w + (N : ℂ) ≠ -(k : ℂ) := by
      intro k h
      have h' := congrArg Complex.re h
      simp only [add_re, natCast_re, neg_re] at h'
      linarith [Nat.cast_nonneg (α := ℝ) N, Nat.cast_nonneg (α := ℝ) k]
    rw [Nat.cast_succ, ← add_assoc, Complex.digamma_apply_add_one _ hne, ih,
      Finset.sum_range_succ, add_assoc]

lemma ne_neg_natCast_of_pos {x : ℝ} (hx : 0 < x) (m : ℕ) : x ≠ -(m : ℝ) :=
  ((neg_nonpos.mpr (Nat.cast_nonneg m)).trans_lt hx).ne'

/-- On `(0, ∞)` the complex digamma function is the derivative of `log ∘ Gamma`. -/
lemma digamma_ofReal {x : ℝ} (hx : 0 < x) :
    Complex.digamma (x : ℂ) = ((deriv (Real.log ∘ Real.Gamma) x : ℝ) : ℂ) := by
  have hR : DifferentiableAt ℝ Real.Gamma x :=
    Real.differentiableAt_Gamma (ne_neg_natCast_of_pos hx)
  have hC : DifferentiableAt ℂ Complex.Gamma (x : ℂ) := by
    refine Complex.differentiableAt_Gamma _ fun m h => ?_
    have h' := congrArg Complex.re h
    simp only [ofReal_re, neg_re, natCast_re] at h'
    exact ne_neg_natCast_of_pos hx m h'
  have h1 : HasDerivAt (fun t : ℝ => Complex.Gamma (t : ℂ)) (deriv Complex.Gamma (x : ℂ)) x :=
    hC.hasDerivAt.comp_ofReal
  have h2 : HasDerivAt (fun t : ℝ => Complex.Gamma (t : ℂ)) ((deriv Real.Gamma x : ℝ) : ℂ) x :=
    hR.hasDerivAt.ofReal_comp.congr_of_eventuallyEq
      (Eventually.of_forall fun t => Complex.Gamma_ofReal t)
  have hderiv : deriv Complex.Gamma (x : ℂ) = ((deriv Real.Gamma x : ℝ) : ℂ) := h1.unique h2
  rw [Complex.digamma_def, logDeriv_apply, hderiv, Complex.Gamma_ofReal, Function.comp_def,
    deriv.log hR (Real.Gamma_pos_of_pos hx).ne']
  push_cast
  rfl

/-- Convexity of `log ∘ Gamma` places its derivative at `y > 1` between `log (y - 1)` and `log y`. -/
lemma deriv_logGamma_bounds {y : ℝ} (hy : 1 < y) :
    Real.log (y - 1) ≤ deriv (Real.log ∘ Real.Gamma) y ∧
      deriv (Real.log ∘ Real.Gamma) y ≤ Real.log y := by
  set f : ℝ → ℝ := Real.log ∘ Real.Gamma with hf
  have hc : ConvexOn ℝ (Ioi 0) f := Real.convexOn_log_Gamma
  have h_rec (z : ℝ) (hz : 0 < z) : f (z + 1) = f z + Real.log z := by
    simp only [f, Function.comp_apply, Real.Gamma_add_one hz.ne',
      Real.log_mul hz.ne' (Real.Gamma_pos_of_pos hz).ne', add_comm]
  have hder {z : ℝ} (hz : 0 < z) : DifferentiableAt ℝ f z :=
    (Real.differentiableAt_Gamma (ne_neg_natCast_of_pos hz)).log (Real.Gamma_pos_of_pos hz).ne'
  have hy0 : 0 < y := by linarith
  have hy1 : 0 < y - 1 := by linarith
  constructor
  · refine (le_of_eq ?_).trans (hc.slope_le_deriv (mem_Ioi.mpr hy1) (mem_Ioi.mpr hy0)
      (by linarith) (hder hy0))
    rw [slope_def_field, show y - (y - 1) = (1 : ℝ) by ring, div_one,
      show y = (y - 1) + 1 by ring, h_rec _ hy1]
    ring_nf
  · refine (hc.deriv_le_slope (mem_Ioi.mpr hy0) (mem_Ioi.mpr (by linarith : (0 : ℝ) < y + 1))
      (by linarith) (hder hy0)).trans (le_of_eq ?_)
    rw [slope_def_field, show y + 1 - y = (1 : ℝ) by ring, div_one, h_rec _ hy0]
    ring

lemma tendsto_deriv_logGamma_sub_log {x : ℝ} (hx : 0 < x) :
    Tendsto (fun N : ℕ => deriv (Real.log ∘ Real.Gamma) (x + N) - Real.log N) atTop (𝓝 0) := by
  have hlo := (Real.tendsto_log_comp_add_sub_log (x - 1)).comp tendsto_natCast_atTop_atTop
  have hhi := (Real.tendsto_log_comp_add_sub_log x).comp tendsto_natCast_atTop_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hb := (deriv_logGamma_bounds (y := x + N) (by linarith)).1
    simp only [Function.comp_apply]
    rw [show (N : ℝ) + (x - 1) = x + N - 1 by ring]
    linarith
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hb := (deriv_logGamma_bounds (y := x + N) (by linarith)).2
    simp only [Function.comp_apply]
    rw [show (N : ℝ) + x = x + N by ring]
    linarith

lemma hasSum_digammaTerm_ofReal {x : ℝ} (hx : 0 < x) :
    HasSum (digammaTerm (x : ℂ)) (Complex.digamma (x : ℂ) + γ) := by
  have hxre : 0 < (x : ℂ).re := by simpa using hx
  refine (hasSum_iff_tendsto_nat_of_summable_norm (summable_digammaTerm hxre).norm).mpr ?_
  set f : ℝ → ℝ := Real.log ∘ Real.Gamma with hf
  have hpart : ∀ N : ℕ, ∑ m ∈ Finset.range N, digammaTerm (x : ℂ) m =
      (((harmonic N : ℝ) - deriv f (x + N) : ℝ) : ℂ) + Complex.digamma x := by
    intro N
    have h1 := digamma_add_nat hxre N
    have h2 : Complex.digamma ((x : ℂ) + N) = ((deriv f (x + N) : ℝ) : ℂ) := by
      rw [show (x : ℂ) + N = ((x + N : ℝ) : ℂ) by push_cast; ring]
      exact digamma_ofReal (by positivity)
    have h3 : ((harmonic N : ℝ) : ℂ) = ∑ m ∈ Finset.range N, 1 / ((m : ℂ) + 1) := by
      simp [harmonic]
    rw [Complex.ofReal_sub, h3, ← h2, h1]
    simp only [digammaTerm, Finset.sum_sub_distrib, one_div]
    ring
  have hreal : Tendsto (fun N : ℕ => (harmonic N : ℝ) - deriv f (x + N)) atTop (𝓝 γ) := by
    have h := Real.tendsto_harmonic_sub_log.sub (tendsto_deriv_logGamma_sub_log hx)
    rw [sub_zero] at h
    exact h.congr fun N => by ring
  rw [funext hpart, add_comm (Complex.digamma _)]
  exact ((Complex.continuous_ofReal.tendsto _).comp hreal).add_const _

/-! ## 3. Continuation to the right half-plane -/

lemma analyticOnNhd_Gamma : AnalyticOnNhd ℂ Complex.Gamma {w : ℂ | 0 < w.re} := by
  refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) isOpen_re_pos
  refine (Complex.differentiableAt_Gamma _ fun m h => ?_).differentiableWithinAt
  have h' := congrArg Complex.re h
  simp only [neg_re, natCast_re] at h'
  have hw' : 0 < w.re := hw
  linarith [Nat.cast_nonneg (α := ℝ) m]

lemma analyticOnNhd_digamma : AnalyticOnNhd ℂ Complex.digamma {w : ℂ | 0 < w.re} := by
  have hfun : Complex.digamma = fun w => deriv Complex.Gamma w / Complex.Gamma w := by
    funext w; rw [Complex.digamma_def, logDeriv_apply]
  rw [hfun]
  intro w hw
  exact (analyticOnNhd_Gamma w hw).deriv.div (analyticOnNhd_Gamma w hw)
    (Complex.Gamma_ne_zero_of_re_pos hw)

/-- **Partial fractions for digamma.** On `0 < w.re`,
`digamma w + γ = ∑_{m ≥ 0} (1/(m+1) - 1/(w+m))`. -/
theorem hasSum_digammaTerm {w : ℂ} (hw : 0 < w.re) :
    HasSum (digammaTerm w) (Complex.digamma w + γ) := by
  have hpre : IsPreconnected {w : ℂ | 0 < w.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hf : AnalyticOnNhd ℂ (fun w => ∑' m, digammaTerm w m) {w : ℂ | 0 < w.re} :=
    differentiableOn_tsum_digammaTerm.analyticOnNhd isOpen_re_pos
  have hg : AnalyticOnNhd ℂ (fun w => Complex.digamma w + γ) {w : ℂ | 0 < w.re} :=
    analyticOnNhd_digamma.add analyticOnNhd_const
  have hone : (1 : ℂ) ∈ {w : ℂ | 0 < w.re} := by simp
  have heq := hf.eqOn_of_preconnected_of_frequently_eq hg hpre hone ?_
  · have h := heq hw
    simp only at h
    rw [← h]
    exact (summable_digammaTerm hw).hasSum
  · have hlim : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 1) := by
      have h := tendsto_const_nhds (x := (1 : ℝ)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa using h
    have ht : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 1) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h := (Complex.continuous_ofReal.tendsto 1).comp hlim
        rw [Complex.ofReal_one] at h
        exact h
      · simp only [mem_compl_iff, mem_singleton_iff]
        intro h
        have h' := congrArg Complex.re h
        simp only [ofReal_re, one_re] at h'
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    refine ht.frequently (Frequently.of_forall fun n => ?_)
    have hpos : (0 : ℝ) < 1 + 1 / ((n : ℝ) + 1) := by positivity
    exact (hasSum_digammaTerm_ofReal hpos).tsum_eq

theorem digamma_eq_tsum {w : ℂ} (hw : 0 < w.re) :
    Complex.digamma w = ∑' m, digammaTerm w m - γ := by
  rw [(hasSum_digammaTerm hw).tsum_eq]
  ring

/-! ## 4. Bounds -/

/-- A linear bound for `digamma` on `δ ≤ w.re`. -/
theorem norm_digamma_add_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {w : ℂ} (hw : δ ≤ w.re) :
    ‖Complex.digamma w + γ‖ ≤ ‖w - 1‖ / δ * ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2 := by
  rw [← (hasSum_digammaTerm (hδ.trans_le hw)).tsum_eq, ← tsum_mul_left]
  refine tsum_of_norm_bounded ((summable_one_div_add_one_sq.mul_left _).hasSum) fun m => ?_
  exact norm_digammaTerm_le hδ hδ1 hw m

/-- Termwise bound on the line `w = 1 + i y`. -/
theorem norm_digammaTerm_one_add_le (y : ℝ) (m : ℕ) :
    ‖digammaTerm (1 + y * I) m‖ ≤ Real.sqrt |y| / (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1)) := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hre : 0 < ((1 : ℂ) + y * I).re := by simp
  rw [digammaTerm_eq m (add_natCast_ne_zero hre m), norm_div, norm_mul, norm_natCast_add_one]
  have hnum : ‖(1 : ℂ) + y * I - 1‖ = |y| := by
    rw [show (1 : ℂ) + y * I - 1 = y * I by ring, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
  have hden : ‖(1 : ℂ) + y * I + m‖ = Real.sqrt (((m : ℝ) + 1) ^ 2 + y ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp only [add_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_zero, natCast_re, add_im, one_im, mul_im, zero_add, natCast_im, add_zero]
    ring
  rw [hnum, hden]
  have hQ : 0 < ((m : ℝ) + 1) ^ 2 + y ^ 2 := by positivity
  have hsQ : 0 < Real.sqrt (((m : ℝ) + 1) ^ 2 + y ^ 2) := Real.sqrt_pos.mpr hQ
  have hsm : 0 < Real.sqrt ((m : ℝ) + 1) := Real.sqrt_pos.mpr hm
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  -- `|y| √(m+1) ≤ √|y| √((m+1)^2 + y^2)`
  have hkey : Real.sqrt |y| * Real.sqrt ((m : ℝ) + 1) ≤
      Real.sqrt (((m : ℝ) + 1) ^ 2 + y ^ 2) := by
    rw [← Real.sqrt_mul (abs_nonneg y)]
    apply Real.sqrt_le_sqrt
    have h1 : |y| ^ 2 = y ^ 2 := sq_abs y
    nlinarith [sq_nonneg ((m : ℝ) + 1 - |y|), abs_nonneg y]
  have hy : |y| = Real.sqrt |y| * Real.sqrt |y| :=
    (Real.mul_self_sqrt (abs_nonneg y)).symm
  calc |y| * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))
      = Real.sqrt |y| * ((m : ℝ) + 1) * (Real.sqrt |y| * Real.sqrt ((m : ℝ) + 1)) := by
        conv_lhs => rw [hy]
        ring
    _ ≤ Real.sqrt |y| * ((m : ℝ) + 1) * Real.sqrt (((m : ℝ) + 1) ^ 2 + y ^ 2) := by
        gcongr
    _ = Real.sqrt |y| * (((m : ℝ) + 1) * Real.sqrt (((m : ℝ) + 1) ^ 2 + y ^ 2)) := by ring

lemma summable_inv_mul_sqrt : Summable (fun m : ℕ => 1 / (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))) := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 3 / 2))
  refine h.congr fun m => ?_
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  push_cast
  rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hm.le (by norm_num)]
  norm_num

/-! ## 5. The logarithmic derivative of `Gammaℝ` -/

lemma differentiableAt_Gamma_half {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s := by
  have hre : 0 < (s / 2).re := by simp [hs]
  have hG : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
    (analyticOnNhd_Gamma (s / 2) hre).differentiableAt
  exact hG.comp s (by fun_prop)

theorem logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    logDeriv Gammaℝ s = -(Real.log Real.pi : ℂ) / 2 + Complex.digamma (s / 2) / 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hre : 0 < (s / 2).re := by simp [hs]
  have hA : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log Real.pi * (-1 / 2)) s := by
    have h : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2) s := by
      simpa using ((hasDerivAt_id s).neg.div_const 2)
    exact h.const_cpow (Or.inl hpi)
  have hA0 : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hpi]; exact Complex.exp_ne_zero _
  have hG0 : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hre
  have hGd : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
    (analyticOnNhd_Gamma (s / 2) hre).differentiableAt
  have hhalf : HasDerivAt (fun z : ℂ => z / 2) (1 / 2) s := by
    simpa using ((hasDerivAt_id s).div_const 2)
  have hfun : Gammaℝ = fun z => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) := by
    funext z; rw [Gammaℝ_def]
  rw [hfun, logDeriv_mul (f := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
    (g := fun z : ℂ => Complex.Gamma (z / 2)) s hA0 hG0 hA.differentiableAt
    (hGd.comp s hhalf.differentiableAt)]
  have h1 : logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s = -(Real.log Real.pi : ℂ) / 2 := by
    rw [logDeriv_apply, hA.deriv, Complex.ofReal_log Real.pi_pos.le]
    field_simp
  have h2 : logDeriv (fun z : ℂ => Complex.Gamma (z / 2)) s = Complex.digamma (s / 2) / 2 := by
    have h := logDeriv_comp (f := Complex.Gamma) (g := fun z : ℂ => z / 2) (x := s) hGd
      hhalf.differentiableAt
    rw [show (fun z : ℂ => Complex.Gamma (z / 2)) = Complex.Gamma ∘ (fun z : ℂ => z / 2) from rfl,
      h, hhalf.deriv, Complex.digamma_def]
    ring
  rw [h1, h2]

/-! ## 6. The alternating series for `log 2` -/

/-- `∑_{m ≥ 0} (1/(2m+1) - 1/(2m+2)) = log 2`, from `digamma (1/2) = -2 log 2 - γ`. -/
theorem hasSum_log_two :
    HasSum (fun m : ℕ => 1 / (2 * (m : ℝ) + 1) - 1 / (2 * (m : ℝ) + 2)) (Real.log 2) := by
  have h := hasSum_digammaTerm (w := 1 / 2) (by norm_num)
  rw [Complex.digamma_one_half] at h
  have h2 := h.mul_left (-1 / 2 : ℂ)
  have e1 : (fun m : ℕ => (-1 / 2 : ℂ) * digammaTerm (1 / 2) m) =
      fun m : ℕ => (((1 / (2 * (m : ℝ) + 1) - 1 / (2 * (m : ℝ) + 2) : ℝ)) : ℂ) := by
    funext m
    have hc : ∀ x : ℝ, 0 < x → (x : ℂ) ≠ 0 := fun x hx => Complex.ofReal_ne_zero.mpr hx.ne'
    have h1 : (2 : ℂ) * m + 1 ≠ 0 := by
      rw [show (2 : ℂ) * m + 1 = ((2 * m + 1 : ℝ) : ℂ) by push_cast; ring]; exact hc _ (by positivity)
    have h2 : (2 : ℂ) * m + 2 ≠ 0 := by
      rw [show (2 : ℂ) * m + 2 = ((2 * m + 2 : ℝ) : ℂ) by push_cast; ring]; exact hc _ (by positivity)
    have h3 : (1 / 2 : ℂ) + m ≠ 0 := by
      rw [show (1 / 2 : ℂ) + m = ((1 / 2 + m : ℝ) : ℂ) by push_cast; ring]; exact hc _ (by positivity)
    have h4 := natCast_add_one_ne_zero m
    have e3 : (1 : ℂ) / (1 / 2 + m) = 2 / (2 * m + 1) := by
      rw [div_eq_div_iff h3 h1]; ring
    have e4 : (1 : ℂ) / (m + 1) = 2 / (2 * m + 2) := by
      rw [div_eq_div_iff h4 h2]; ring
    unfold digammaTerm
    rw [e3, e4]
    push_cast
    ring
  have e2 : (-1 / 2 : ℂ) * (-2 * Complex.log 2 - (γ : ℂ) + (γ : ℂ)) = ((Real.log 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast
    ring
  rw [e1, e2] at h2
  exact Complex.hasSum_ofReal.mp h2

#print axioms hasSum_digammaTerm
#print axioms norm_digamma_add_le
#print axioms norm_digammaTerm_one_add_le
#print axioms logDeriv_Gammaℝ
#print axioms hasSum_log_two

end TentDigamma
