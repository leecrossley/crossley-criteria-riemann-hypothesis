/-
Copyright (c) 2026 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE-2.0.
-/
import HalvingPowerInput
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.NumberTheory.ZetaValues

/-!
# Zero-Free Half-Plane to Mertens Prefix Bound from Mathlib

Proof of Littlewood's classical zero-free half-plane to Mertens summatory Möbius theorem
(Titchmarsh, *The Theory of the Riemann Zeta-Function*, §14.25) from Mathlib (`0df444a360ea`)
and `HalvingPowerInput` alone, without third-party `GaloisForLFunctions` imports.

## Main Results

* `HalvingMertens.prefixExponent_of_zeroFree`:
  If `1 / 2 ≤ θ ≤ 1` and `∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0`, then `PrefixExponent θ`.
* `HalvingMertens.rh_implies_prefixExponent_half`:
  `RiemannHypothesis → PrefixExponent (1 / 2)`.
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Interval

noncomputable section

namespace ZetaMertens

/-! ### 1. Polynomial Growth of `riemannZeta` on `Re s ≥ 1/4` and Lower Bound on `Re s = 2` -/

private def zetaIntBlock (k : ℕ) (w : ℂ) : ℂ :=
  cexp (w * (Real.log ((k : ℝ) + 2) : ℂ)) - cexp (w * (Real.log ((k : ℝ) + 1) : ℂ))

private def zetaDiffTerm (k : ℕ) (s : ℂ) : ℂ :=
  cexp (-s * (Real.log ((k : ℝ) + 1) : ℂ)) - dslope (zetaIntBlock k) 0 (1 - s)

private theorem differentiable_zetaDiffTerm (k : ℕ) : Differentiable ℂ (zetaDiffTerm k) := by
  have hb : Differentiable ℂ (zetaIntBlock k) := by unfold zetaIntBlock; fun_prop
  have hd : Differentiable ℂ (dslope (zetaIntBlock k) 0) :=
    differentiableOn_univ.mp
      ((Complex.differentiableOn_dslope (s := univ) (c := (0 : ℂ)) Filter.univ_mem).mpr
        hb.differentiableOn)
  unfold zetaDiffTerm
  exact (by fun_prop : Differentiable ℂ fun s : ℂ =>
    cexp (-s * (Real.log ((k : ℝ) + 1) : ℂ))).sub
    (hd.comp (differentiable_const (1 : ℂ) |>.sub differentiable_id))

private theorem dslope_zetaIntBlock_eq_integral (k : ℕ) {s : ℂ} (hs1 : s ≠ 1) :
    dslope (zetaIntBlock k) 0 (1 - s) =
      ∫ x in ((k : ℝ) + 1)..((k : ℝ) + 2), cexp (-s * (Real.log x : ℂ)) := by
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  set a : ℝ := (k : ℝ) + 1
  set b : ℝ := (k : ℝ) + 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hderiv : ∀ x ∈ uIcc a b,
      HasDerivAt (fun t : ℝ => cexp ((1 - s) * (Real.log t : ℂ)) / (1 - s))
        (cexp (-s * (Real.log x : ℂ))) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hx0 : 0 < x := ha.trans_le hx.1
    have h1 : HasDerivAt (fun t : ℝ => (Real.log t : ℂ)) ((x⁻¹ : ℝ) : ℂ) x :=
      (Real.hasDerivAt_log hx0.ne').ofReal_comp
    have h2 := ((h1.const_mul (1 - s)).cexp).div_const (1 - s)
    refine h2.congr_deriv ?_
    have hexp_split : cexp ((1 - s) * (Real.log x : ℂ)) =
        (x : ℂ) * cexp (-s * (Real.log x : ℂ)) := by
      have hxl : cexp (Real.log x : ℂ) = (x : ℂ) := by
        rw [← Complex.ofReal_exp, Real.exp_log hx0]
      rw [show (1 - s) * (Real.log x : ℂ) = (Real.log x : ℂ) + -s * (Real.log x : ℂ) by ring,
        Complex.exp_add, hxl]
    rw [hexp_split]
    have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
    push_cast
    field_simp [h1s, hxc]
  have hint : IntervalIntegrable (fun x : ℝ => cexp (-s * (Real.log x : ℂ))) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]
    have hne : ∀ x ∈ Icc a b, x ≠ 0 := fun x hx => (ha.trans_le hx.1).ne'
    fun_prop (disch := assumption)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint,
    dslope_of_ne _ h1s, slope_def_field]
  unfold zetaIntBlock
  simp only [zero_mul, Complex.exp_zero, sub_self, sub_zero]
  dsimp [a, b]
  ring

private theorem norm_zetaDiffTerm_le_of_ne_one {k : ℕ} {s : ℂ} {δ₀ : ℝ}
    (hs1 : s ≠ 1) (hδ₀ : 0 < δ₀) (hre : δ₀ ≤ s.re) :
    ‖zetaDiffTerm k s‖ ≤ ‖s‖ * ((k + 1 : ℕ) : ℝ) ^ (-(1 + δ₀)) := by
  set a : ℝ := (k : ℝ) + 1
  set b : ℝ := (k : ℝ) + 2
  have ha_eq : a = ((k + 1 : ℕ) : ℝ) := by dsimp [a]; push_cast; ring
  have ha1 : 1 ≤ a := by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have ha0 : 0 < a := zero_lt_one.trans_le ha1
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hconst_int : (∫ _x in a..b, cexp (-s * (Real.log a : ℂ))) =
      cexp (-s * (Real.log a : ℂ)) := by
    rw [intervalIntegral.integral_const]
    have hba : b - a = 1 := by dsimp [a, b]; ring
    rw [hba, one_smul]
  have hdiff_eq : zetaDiffTerm k s =
      ∫ x in a..b, (cexp (-s * (Real.log a : ℂ)) - cexp (-s * (Real.log x : ℂ))) := by
    have hc1 : IntervalIntegrable (fun _ : ℝ => cexp (-s * (Real.log a : ℂ))) volume a b :=
      intervalIntegrable_const
    have hc2 : IntervalIntegrable (fun x : ℝ => cexp (-s * (Real.log x : ℂ))) volume a b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hab]
      have hne : ∀ x ∈ Icc a b, x ≠ 0 := fun x hx => (ha0.trans_le hx.1).ne'
      fun_prop (disch := assumption)
    calc zetaDiffTerm k s
        = cexp (-s * (Real.log a : ℂ)) -
            ∫ x in a..b, cexp (-s * (Real.log x : ℂ)) := by
              unfold zetaDiffTerm
              rw [dslope_zetaIntBlock_eq_integral k hs1]
      _ = (∫ _x in a..b, cexp (-s * (Real.log a : ℂ))) -
            ∫ x in a..b, cexp (-s * (Real.log x : ℂ)) := by rw [hconst_int]
      _ = ∫ x in a..b, (cexp (-s * (Real.log a : ℂ)) - cexp (-s * (Real.log x : ℂ))) :=
            (intervalIntegral.integral_sub hc1 hc2).symm
  rw [hdiff_eq]
  have hinner : ∀ x ∈ uIoc a b,
      ‖cexp (-s * (Real.log a : ℂ)) - cexp (-s * (Real.log x : ℂ))‖ ≤
        ‖s‖ * ((k + 1 : ℕ) : ℝ) ^ (-(1 + δ₀)) := by
    intro x hx
    rw [uIoc_of_le hab] at hx
    have hax : a ≤ x := hx.1.le
    have hxb : x ≤ b := hx.2
    have hftc_ax : cexp (-s * (Real.log a : ℂ)) - cexp (-s * (Real.log x : ℂ)) =
        s * ∫ t in a..x, cexp (-s * (Real.log t : ℂ)) / (t : ℂ) := by
      have hder : ∀ t ∈ uIcc a x,
          HasDerivAt (fun u : ℝ => -cexp (-s * (Real.log u : ℂ)))
            (s * (cexp (-s * (Real.log t : ℂ)) / (t : ℂ))) t := by
        intro t ht
        rw [uIcc_of_le hax] at ht
        have ht0 : 0 < t := ha0.trans_le ht.1
        have h1 : HasDerivAt (fun u : ℝ => (Real.log u : ℂ)) ((t⁻¹ : ℝ) : ℂ) t :=
          (Real.hasDerivAt_log ht0.ne').ofReal_comp
        have h2 := ((h1.const_mul (-s)).cexp).neg
        refine h2.congr_deriv ?_
        push_cast; field_simp [ht0.ne']
      have hint_ax : IntervalIntegrable
          (fun t : ℝ => s * (cexp (-s * (Real.log t : ℂ)) / (t : ℂ))) volume a x := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hax]
        have hneC : ∀ t ∈ Icc a x, (t : ℂ) ≠ 0 :=
          fun t ht => Complex.ofReal_ne_zero.mpr (ha0.trans_le ht.1).ne'
        have hneR : ∀ t ∈ Icc a x, t ≠ 0 := fun t ht => (ha0.trans_le ht.1).ne'
        fun_prop (disch := assumption)
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint_ax
      rw [intervalIntegral.integral_const_mul] at h
      linear_combination -h
    rw [hftc_ax, norm_mul]
    have hint_bd : ‖∫ t in a..x, cexp (-s * (Real.log t : ℂ)) / (t : ℂ)‖ ≤
        ((k + 1 : ℕ) : ℝ) ^ (-(1 + δ₀)) * |x - a| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
      rw [uIoc_of_le hax] at ht
      have hat : a ≤ t := ht.1.le
      have ht0 : 0 < t := ha0.trans_le hat
      have hlog0 : 0 ≤ Real.log t := Real.log_nonneg (ha1.trans hat)
      rw [norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg ht0.le]
      have hre_exp : (-s * (Real.log t : ℂ)).re = -s.re * Real.log t := by
        simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      rw [hre_exp]
      have hexp_le : Real.exp (-s.re * Real.log t) ≤ Real.exp (-δ₀ * Real.log t) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hre) hlog0)
      have hrpow_t : Real.exp (-δ₀ * Real.log t) / t = t ^ (-(1 + δ₀)) := by
        calc Real.exp (-δ₀ * Real.log t) / t
            = Real.exp (-δ₀ * Real.log t) / Real.exp (Real.log t) := by rw [Real.exp_log ht0]
          _ = Real.exp (-δ₀ * Real.log t - Real.log t) := (Real.exp_sub _ _).symm
          _ = Real.exp (Real.log t * -(1 + δ₀)) := by congr 1; ring
          _ = t ^ (-(1 + δ₀)) := (Real.rpow_def_of_pos ht0 _).symm
      calc Real.exp (-s.re * Real.log t) / t
          ≤ Real.exp (-δ₀ * Real.log t) / t := div_le_div_of_nonneg_right hexp_le ht0.le
        _ = t ^ (-(1 + δ₀)) := hrpow_t
        _ ≤ a ^ (-(1 + δ₀)) := Real.rpow_le_rpow_of_nonpos ha0 hat (by linarith)
        _ = ((k + 1 : ℕ) : ℝ) ^ (-(1 + δ₀)) := by rw [ha_eq]
    have hxa_le : |x - a| ≤ 1 := by
      rw [abs_of_nonneg (by linarith)]
      dsimp [a, b] at hxb ⊢
      linarith
    calc ‖s‖ * ‖∫ t in a..x, cexp (-s * (Real.log t : ℂ)) / (t : ℂ)‖
        ≤ ‖s‖ * (((k + 1 : ℕ) : ℝ) ^ (-(1 + δ₀)) * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg s)
          exact hint_bd.trans (mul_le_mul_of_nonneg_left hxa_le (by positivity))
      _ = ‖s‖ * ((k + 1 : ℕ) : ℝ) ^ (-(1 + δ₀)) := by ring
  have houter := intervalIntegral.norm_integral_le_of_norm_le_const hinner
  have hba1 : |b - a| = 1 := by
    have : b - a = 1 := by dsimp [a, b]; ring
    rw [this, abs_one]
  rwa [hba1, mul_one] at houter

private theorem norm_zetaDiffTerm_le {k : ℕ} {s : ℂ} {δ₀ M : ℝ}
    (hδ₀ : 0 < δ₀) (hre : δ₀ ≤ s.re) (hM : ‖s‖ ≤ M) :
    ‖zetaDiffTerm k s‖ ≤ M * ((k + 1 : ℕ) : ℝ) ^ (-(1 + δ₀)) := by
  have h_self : ‖zetaDiffTerm k s‖ ≤ ‖s‖ * ((k + 1 : ℕ) : ℝ) ^ (-(1 + δ₀)) := by
    rcases ne_or_eq s 1 with hs1 | rfl
    · exact norm_zetaDiffTerm_le_of_ne_one hs1 hδ₀ hre
    · -- Continuity limit along `s_n = 1 + 1 / (n + 1)`
      let seq : ℕ → ℂ := fun n => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)
      have hlim : Tendsto seq atTop (𝓝 (1 : ℂ)) := by
        have h1 : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
        rw [add_zero] at h1
        exact (Complex.continuous_ofReal.tendsto 1).comp h1
      have h_lhs : Tendsto (fun n => ‖zetaDiffTerm k (seq n)‖) atTop (𝓝 ‖zetaDiffTerm k 1‖) :=
        ((differentiable_zetaDiffTerm k).continuous.norm.tendsto 1).comp hlim
      have h_rhs : Tendsto (fun n => ‖seq n‖ * ((k + 1 : ℕ) : ℝ) ^ (-(1 + δ₀)))
          atTop (𝓝 (‖(1 : ℂ)‖ * ((k + 1 : ℕ) : ℝ) ^ (-(1 + δ₀)))) :=
        (continuous_norm.tendsto 1 |>.comp hlim).mul_const _
      refine le_of_tendsto_of_tendsto h_lhs h_rhs (Eventually.of_forall fun n => ?_)
      have hne : seq n ≠ 1 := by
        intro hc
        have := congrArg Complex.re hc
        simp only [seq, ofReal_re, one_re] at this
        have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      have hre_n : δ₀ ≤ (seq n).re := by
        have h1 : δ₀ ≤ (1 : ℂ).re := hre
        simp only [one_re] at h1
        simp only [seq, ofReal_re]
        have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      exact norm_zetaDiffTerm_le_of_ne_one hne hδ₀ hre_n
  exact h_self.trans (mul_le_mul_of_nonneg_right hM (by positivity))

private theorem summable_zetaDiff_majorant (M : ℝ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    Summable fun k : ℕ => M * ((k + 1 : ℕ) : ℝ) ^ (-(1 + δ₀)) := by
  have h1 : Summable fun n : ℕ => (n : ℝ) ^ (-(1 + δ₀)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact ((summable_nat_add_iff 1).mpr h1).mul_left M

private theorem differentiableOn_tsum_zetaDiffTerm :
    DifferentiableOn ℂ (fun s => ∑' k : ℕ, zetaDiffTerm k s) {s : ℂ | 0 < s.re} := by
  intro s₀ hs₀
  have hs₀' : 0 < s₀.re := hs₀
  set δ₀ : ℝ := s₀.re / 2
  have hδ₀ : 0 < δ₀ := half_pos hs₀'
  have hunif : TendstoUniformlyOn
      (fun (N : ℕ) (s : ℂ) => ∑ k ∈ Finset.range N, zetaDiffTerm k s)
      (fun s => ∑' k : ℕ, zetaDiffTerm k s) atTop (ball s₀ δ₀) := by
    refine tendstoUniformlyOn_tsum_nat (summable_zetaDiff_majorant (‖s₀‖ + δ₀) hδ₀) fun k s hs => ?_
    have hdist : ‖s - s₀‖ < δ₀ := mem_ball_iff_norm.mp hs
    have hre : δ₀ ≤ s.re := by
      have h2 := (abs_lt.mp ((Complex.abs_re_le_norm (s - s₀)).trans_lt hdist)).1
      rw [Complex.sub_re] at h2
      dsimp [δ₀] at h2 ⊢
      linarith
    have hnorm : ‖s‖ ≤ ‖s₀‖ + δ₀ := by
      have htri := norm_add_le (s - s₀) s₀
      rw [sub_add_cancel] at htri
      linarith
    exact norm_zetaDiffTerm_le hδ₀ hre hnorm
  have hdiff_ball : DifferentiableOn ℂ (fun s => ∑' k : ℕ, zetaDiffTerm k s) (ball s₀ δ₀) := by
    refine hunif.tendstoLocallyUniformlyOn.differentiableOn ?_ isOpen_ball
    exact Eventually.of_forall fun N => DifferentiableOn.fun_sum fun k _ =>
      (differentiable_zetaDiffTerm k).differentiableOn
  exact (hdiff_ball.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hδ₀))).differentiableWithinAt

private theorem tsum_zetaDiffTerm_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    (∑' k : ℕ, zetaDiffTerm k s) = riemannZeta₀ s := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  -- First, `∑_{k ≥ 0} cexp (-s * log(k + 1)) = riemannZeta s`
  have hterm_zeta : ∀ k : ℕ,
      cexp (-s * (Real.log ((k : ℝ) + 1) : ℂ)) = 1 / ((k : ℂ) + 1) ^ s := by
    intro k
    have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hk1_ne : ((k : ℂ) + 1) ≠ 0 := by
      have : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [this]
      exact Complex.ofReal_ne_zero.mpr hk1_pos.ne'
    have hcast : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [one_div, ← Complex.cpow_neg, hcast,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hk1_pos.ne'),
      ← Complex.ofReal_log hk1_pos.le]
    congr 1; ring
  have hsum_zeta : HasSum (fun k : ℕ => cexp (-s * (Real.log ((k : ℝ) + 1) : ℂ)))
      (riemannZeta s) := by
    have hsn : Summable fun k : ℕ => ‖1 / ((k : ℂ) + 1) ^ s‖ := by
      have h1 : Summable fun n : ℕ => (n : ℝ) ^ (-s.re) :=
        Real.summable_nat_rpow.mpr (by linarith)
      refine ((summable_nat_add_iff 1).mpr h1).congr fun k => ?_
      have he : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [he, norm_div, norm_one, Complex.norm_natCast_cpow_of_pos (Nat.succ_pos k),
        one_div, ← Real.rpow_neg (Nat.cast_nonneg _)]
    have hhs := hsn.of_norm.hasSum
    rw [← zeta_eq_tsum_one_div_nat_add_one_cpow hs] at hhs
    exact hhs.congr_fun fun k => hterm_zeta k
  -- Second, partial sums of `dslope (zetaIntBlock k) 0 (1 - s)` telescope to `(s - 1)⁻¹`
  have hdslope_tel : ∀ N : ℕ,
      (∑ k ∈ Finset.range N, dslope (zetaIntBlock k) 0 (1 - s)) =
        (cexp ((1 - s) * (Real.log ((N : ℝ) + 1) : ℂ)) - 1) / (1 - s) := by
    intro N
    have hcongr : ∀ k ∈ Finset.range N, dslope (zetaIntBlock k) 0 (1 - s) =
        cexp ((1 - s) * (Real.log (((k + 1 : ℕ) : ℝ) + 1) : ℂ)) / (1 - s) -
          cexp ((1 - s) * (Real.log ((k : ℝ) + 1) : ℂ)) / (1 - s) := by
      intro k _
      rw [dslope_of_ne _ h1s, slope_def_field]
      unfold zetaIntBlock
      simp only [zero_mul, Complex.exp_zero, sub_self, sub_zero]
      have hk2 : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
      rw [hk2, sub_div]
    rw [Finset.sum_congr rfl hcongr,
      Finset.sum_range_sub (fun k : ℕ => cexp ((1 - s) * (Real.log ((k : ℝ) + 1) : ℂ)) / (1 - s)) N]
    simp only [Nat.cast_zero, zero_add, Real.log_one, ofReal_zero, mul_zero, Complex.exp_zero]
    rw [sub_div]
  have htend_zero : Tendsto (fun N : ℕ => cexp ((1 - s) * (Real.log ((N : ℝ) + 1) : ℂ)))
      atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    have hnorm_eq : (fun N : ℕ => ‖cexp ((1 - s) * (Real.log ((N : ℝ) + 1) : ℂ))‖) =
        fun N : ℕ => ((N : ℝ) + 1) ^ (1 - s.re) := by
      funext N
      have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      rw [Complex.norm_exp]
      have hre : ((1 - s) * (Real.log ((N : ℝ) + 1) : ℂ)).re =
          Real.log ((N : ℝ) + 1) * (1 - s.re) := by
        simp only [sub_re, one_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
        ring
      rw [hre, ← Real.rpow_def_of_pos hN1]
    rw [hnorm_eq]
    have ht1 : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    exact (tendsto_rpow_neg_atTop (by linarith : 0 < -(1 - s.re))).comp ht1 |>.congr fun N => by
      simp [sub_eq_add_neg]
  have htend_dslope : Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range N, dslope (zetaIntBlock k) 0 (1 - s))
      atTop (𝓝 ((s - 1)⁻¹)) := by
    have h1 := (htend_zero.sub (tendsto_const_nhds (x := (1 : ℂ)))).div_const (1 - s)
    have hval : (0 - (1 : ℂ)) / (1 - s) = (s - 1)⁻¹ := by
      have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      field_simp [h1s, hs1']
      ring
    rw [hval] at h1
    exact h1.congr fun N => (hdslope_tel N).symm
  have hsum_diff : Summable fun k : ℕ => zetaDiffTerm k s :=
    Summable.of_norm_bounded (summable_zetaDiff_majorant ‖s‖ (by linarith : 0 < s.re))
      fun k => norm_zetaDiffTerm_le (by linarith) le_rfl le_rfl
  have htend_diff : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, zetaDiffTerm k s)
      atTop (𝓝 (riemannZeta s - (s - 1)⁻¹)) := by
    have h := hsum_zeta.tendsto_sum_nat.sub htend_dslope
    refine h.congr fun N => ?_
    rw [← Finset.sum_sub_distrib]
    rfl
  have htsum := (hsum_diff.hasSum_iff_tendsto_nat.mpr htend_diff).tsum_eq
  rw [htsum, riemannZeta_eq_inv_sub_add hs1]
  ring

private theorem tsum_zetaDiffTerm_eq_riemannZeta₀ {s : ℂ} (hs : 0 < s.re) :
    (∑' k : ℕ, zetaDiffTerm k s) = riemannZeta₀ s := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  let G : ℂ → ℂ := fun z => (∑' k : ℕ, zetaDiffTerm k z) - riemannZeta₀ z
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_conv : Convex ℝ U := by
    intro a ha b hb u v hu hv huv
    show 0 < (u • a + v • b).re
    simp only [add_re, real_smul, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    have ha' : 0 < a.re := ha
    have hb' : 0 < b.re := hb
    rcases eq_or_lt_of_le hu with rfl | hu'
    · simp only [zero_add] at huv; subst huv; linarith
    · nlinarith
  have hG_an : AnalyticOnNhd ℂ G U := by
    have han1 := differentiableOn_tsum_zetaDiffTerm.analyticOnNhd hU_open
    intro z hz
    exact (han1 z hz).sub (differentiable_riemannZeta₀.analyticAt z)
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), G z = 0 := by
    let seq : ℕ → ℂ := fun n => ((2 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)
    have hlim : Tendsto seq atTop (𝓝 (2 : ℂ)) := by
      have h1 : Tendsto (fun n : ℕ => 2 + 1 / ((n : ℝ) + 1)) atTop (𝓝 (2 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      rw [add_zero] at h1
      exact (Complex.continuous_ofReal.tendsto 2).comp h1
    have hne : ∀ n : ℕ, seq n ≠ (2 : ℂ) := by
      intro n hc
      have := congrArg Complex.re hc
      simp only [seq, ofReal_re, re_ofNat] at this
      have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    have htend : Tendsto seq atTop (𝓝[≠] (2 : ℂ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hne⟩
    refine htend.frequently (Frequently.of_forall (f := atTop) fun n => ?_)
    have hgt1 : 1 < (seq n).re := by
      simp only [seq, ofReal_re]
      have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    dsimp [G]
    rw [tsum_zetaDiffTerm_eq_of_one_lt_re hgt1, sub_self]
  have hzero := hG_an.eqOn_zero_of_preconnected_of_frequently_eq_zero
    hU_conv.isPreconnected (show (2 : ℂ) ∈ U by simp [U]) hfreq hs
  exact sub_eq_zero.mp hzero

private def zetaRemConst : ℝ :=
  ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))

private theorem zetaRemConst_nonneg : 0 ≤ zetaRemConst :=
  tsum_nonneg fun _ => by positivity

/-- Polynomial bound `‖riemannZeta s‖ ≤ 1 + zetaRemConst * ‖s‖` on `Re s ≥ 1/4, |Im s| ≥ 1`. -/
private theorem norm_riemannZeta_le_of_re_ge_quarter {s : ℂ}
    (hre : 1 / 4 ≤ s.re) (him : 1 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 1 + zetaRemConst * ‖s‖ := by
  have hs1 : s ≠ 1 := by
    rintro rfl; simp at him; linarith
  have hs1_norm : 1 ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    simp only [sub_im, one_im, sub_zero] at h
    linarith
  have hinv_le : ‖(s - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hs1_norm
  have hsum_maj : Summable fun k : ℕ => ‖s‖ * ((k + 1 : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)) := by
    have h := summable_zetaDiff_majorant ‖s‖ (δ₀ := 1 / 4) (by norm_num)
    exact h.congr fun k => by norm_num
  have hexp54 : -(1 + (1 / 4 : ℝ)) = -(5 / 4 : ℝ) := by norm_num
  have hsum_norm : Summable fun k : ℕ => ‖zetaDiffTerm k s‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => by
        have h := norm_zetaDiffTerm_le (k := k) (δ₀ := 1 / 4) (M := ‖s‖) (by norm_num) hre le_rfl
        rwa [hexp54] at h)
      hsum_maj
  have hz0_le : ‖riemannZeta₀ s‖ ≤ zetaRemConst * ‖s‖ := by
    rw [← tsum_zetaDiffTerm_eq_riemannZeta₀ (by linarith)]
    calc ‖∑' k : ℕ, zetaDiffTerm k s‖
        ≤ ∑' k : ℕ, ‖zetaDiffTerm k s‖ := norm_tsum_le_tsum_norm hsum_norm
      _ ≤ ∑' k : ℕ, ‖s‖ * ((k + 1 : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)) := by
          refine Summable.tsum_le_tsum (fun k => ?_) hsum_norm hsum_maj
          have h := norm_zetaDiffTerm_le (k := k) (δ₀ := 1 / 4) (M := ‖s‖) (by norm_num) hre le_rfl
          rwa [hexp54] at h
      _ = ‖s‖ * zetaRemConst := tsum_mul_left
      _ = zetaRemConst * ‖s‖ := mul_comm _ _
  rw [riemannZeta_eq_inv_sub_add hs1]
  exact (norm_add_le _ _).trans (add_le_add hinv_le hz0_le)

/-- Uniform upper bound `‖riemannZeta s‖ ≤ zetaRemConst` on `Re s ≥ 5/4`. -/
private theorem norm_riemannZeta_le_of_five_quarters {s : ℂ} (hs : 5 / 4 ≤ s.re) :
    ‖riemannZeta s‖ ≤ zetaRemConst := by
  have hs1 : 1 < s.re := by linarith
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs1]
  have hmaj : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)) := by
    have h1 : Summable fun n : ℕ => (n : ℝ) ^ (-(5 / 4 : ℝ)) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    exact (summable_nat_add_iff 1).mpr h1
  have hterm_le : ∀ n : ℕ, ‖1 / ((n : ℂ) + 1) ^ s‖ ≤ ((n + 1 : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)) := by
    intro n
    have he : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    have hn1 : 1 ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    rw [he, norm_div, norm_one, Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n),
      one_div, ← Real.rpow_neg (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hsn : Summable fun n : ℕ => ‖1 / ((n : ℂ) + 1) ^ s‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le hmaj
  exact (norm_tsum_le_tsum_norm hsn).trans (Summable.tsum_le_tsum hterm_le hsn hmaj)

/-- Lower bound `1 / 4 ≤ ‖riemannZeta (2 + t * I)‖` on the line `Re s = 2`. -/
private theorem norm_zeta_two_add_ge (t : ℝ) : 1 / 4 ≤ ‖riemannZeta (2 + (t : ℂ) * I)‖ := by
  set s : ℂ := 2 + (t : ℂ) * I with hs_def
  have hre : s.re = 2 := by simp [hs_def]
  have h1 : (1 : ℝ) < s.re := by rw [hre]; norm_num
  have hz := zeta_eq_tsum_one_div_nat_add_one_cpow h1
  have hsh1 : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    simpa using (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  have hsh2 : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
    simpa [Finset.sum_range_succ] using (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
  have hnorm : ∀ n : ℕ, ‖1 / ((n : ℂ) + 1) ^ s‖ = 1 / ((n : ℝ) + 1) ^ 2 := by
    intro n
    have e : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [e, norm_div, norm_one, Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n), hre,
      Real.rpow_two]
    push_cast; ring
  have hsn : Summable fun n : ℕ => ‖1 / ((n : ℂ) + 1) ^ s‖ := by
    simp_rw [hnorm]; exact hsh1.summable
  have hsum : Summable fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s := hsn.of_norm
  rw [hsum.tsum_eq_zero_add] at hz
  have h0 : (1 : ℂ) / (((0 : ℕ) : ℂ) + 1) ^ s = 1 := by simp
  rw [h0] at hz
  have htail : ‖∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s‖ ≤ Real.pi ^ 2 / 6 - 1 := by
    have hsn' : Summable fun n : ℕ => ‖1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s‖ :=
      (summable_nat_add_iff 1).mpr hsn
    refine (norm_tsum_le_tsum_norm hsn').trans (le_of_eq ?_)
    rw [← hsh2.tsum_eq]
    refine tsum_congr fun n => ?_
    rw [hnorm]; push_cast; ring
  have hpi : Real.pi ^ 2 / 6 - 1 ≤ 3 / 4 := by
    have h := Real.pi_lt_d2
    have h3 := Real.pi_pos
    nlinarith
  rw [hz]
  have hsub := norm_sub_norm_le (1 : ℂ) (-(∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s))
  rw [norm_one, norm_neg, sub_neg_eq_add] at hsub
  linarith

/-! ### 2. Holomorphic Reciprocal `invZeta` and Subpower Growth `O((|t| + 2)^δ)` -/

/-- Entire-numerator reciprocal `invZeta s = (s - 1) / riemannZeta₁ s`, which agrees with
`(riemannZeta s)⁻¹` for all `s ≠ 1` and is holomorphic across `s = 1` (`invZeta 1 = 0`). -/
def invZeta (s : ℂ) : ℂ := (s - 1) / riemannZeta₁ s

private theorem invZeta_eq_inv {s : ℂ} (hs : s ≠ 1) : invZeta s = (riemannZeta s)⁻¹ := by
  unfold invZeta
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hz1 : riemannZeta₁ s = (s - 1) * riemannZeta s := by
    rw [riemannZeta_eq_inv_sub_mul hs, ← mul_assoc, mul_inv_cancel₀ hsub, one_mul]
  rw [hz1]
  by_cases hz : riemannZeta s = 0
  · simp [hz]
  · field_simp [hsub, hz]

private theorem differentiableAt_invZeta_of_zeroFree {θ : ℝ}
    (hz : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) {s : ℂ} (hs : θ < s.re) :
    DifferentiableAt ℂ invZeta s := by
  have hz1_ne : riemannZeta₁ s ≠ 0 := by
    rcases eq_or_ne s 1 with rfl | hne
    · simp [riemannZeta₁_one]
    · have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hne
      have heq : riemannZeta₁ s = (s - 1) * riemannZeta s := by
        rw [riemannZeta_eq_inv_sub_mul hne, ← mul_assoc, mul_inv_cancel₀ hsub, one_mul]
      rw [heq]
      exact mul_ne_zero hsub (hz s hs)
  unfold invZeta
  exact (differentiableAt_id.sub (differentiableAt_const 1)).div
    (differentiable_riemannZeta₁ s) hz1_ne

/-- Holomorphic logarithm on an open disc (`isExactOn_ball`). -/
private theorem exists_log_on_ball {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball c r)) (hne : ∀ z ∈ ball c r, f z ≠ 0) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball c r) ∧ h c = 0 ∧
      ∀ z ∈ ball c r, f z = f c * cexp (h z) := by
  have hd : DifferentiableOn ℂ (fun z => deriv f z / f z) (ball c r) :=
    (hf.deriv isOpen_ball).div hf hne
  obtain ⟨h, hc, hh⟩ := hd.isExactOn_ball.with_val_at c 0
  have hcb : c ∈ ball c r := mem_ball_self hr
  refine ⟨h, fun z hz => (hh z hz).differentiableAt.differentiableWithinAt, hc, ?_⟩
  have hg : ∀ z ∈ ball c r, HasDerivAt (fun z => f z * cexp (-h z)) 0 z := by
    intro z hz
    have h1 : HasDerivAt f (deriv f z) z :=
      (hf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have h2 := (hh z hz).neg.cexp
    have h3 := h1.mul h2
    have e : deriv f z * cexp (-h z) + f z * (cexp (-h z) * -(deriv f z / f z)) = 0 := by
      have := hne z hz
      field_simp
      ring
    rw [← e]
    exact h3
  have hconst : ∀ z ∈ ball c r, f z * cexp (-h z) = f c * cexp (-h c) := fun z hz =>
    isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c r).isPreconnected
      (fun z hz => (hg z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hg z hz).deriv) hz hcb
  intro z hz
  have h0 := hconst z hz
  rw [hc, neg_zero, Complex.exp_zero, mul_one] at h0
  rw [← h0, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

/-- Borel–Carathéodory transfer from a real-part bound on `ball c R` to a norm bound on `closedBall c r`. -/
private theorem norm_le_of_re_le_on_ball {h : ℂ → ℂ} {c : ℂ} {r R M : ℝ}
    (hr0 : 0 ≤ r) (hrR : r < R) (hM : 0 < M)
    (hh : DifferentiableOn ℂ h (ball c R)) (hhc : h c = 0)
    (hre : ∀ z ∈ ball c R, (h z).re ≤ M) :
    ∀ z ∈ closedBall c r, ‖h z‖ ≤ 2 * M * r / (R - r) := by
  have hR0 : 0 < R := hr0.trans_lt hrR
  have hmem : ∀ w ∈ ball (0 : ℂ) R, c + w ∈ ball c R := by
    intro w hw
    rw [mem_ball_zero_iff] at hw
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hw
  have hHd : DifferentiableOn ℂ (fun w => h (c + w)) (ball 0 R) := fun w hw =>
    ((hh.differentiableAt (isOpen_ball.mem_nhds (hmem w hw))).comp w
      (differentiableAt_id.const_add c)).differentiableWithinAt
  have hHm : MapsTo (fun w => h (c + w)) (ball 0 R) {z | z.re ≤ M} :=
    fun w hw => hre _ (hmem w hw)
  have h0 : (fun w => h (c + w)) 0 = 0 := by simp [hhc]
  intro z hz
  rw [mem_closedBall, dist_eq_norm] at hz
  have hw : z - c ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]; linarith
  have hbc := Complex.borelCaratheodory_zero hM hHd hHm hR0 hw h0
  simp only [add_sub_cancel] at hbc
  refine hbc.trans ?_
  have hden1 : 0 < R - ‖z - c‖ := by linarith
  have hden2 : 0 < R - r := by linarith
  rw [div_le_div_iff₀ hden1 hden2]
  have hdiff_pos : 0 ≤ 2 * M * R * (r - ‖z - c‖) :=
    mul_nonneg (by positivity) (by linarith)
  linarith [show 2 * M * r * (R - ‖z - c‖) - 2 * M * ‖z - c‖ * (R - r) =
    2 * M * R * (r - ‖z - c‖) by ring]

/-- Sublinear power absorption: for `0 < α < 1`, `A > 0`, `δ > 0`, there is `B ≥ 0` such that
`A * L ^ α ≤ δ * L + B` for all `L ≥ 0`. -/
private theorem mul_rpow_le_linear_add {α A δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hA : 0 < A) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ L : ℝ, 0 ≤ L → A * L ^ α ≤ δ * L + B := by
  let L₀ : ℝ := max 1 ((A / δ) ^ (1 / (1 - α)))
  have hL₀1 : 1 ≤ L₀ := le_max_left _ _
  have hL₀0 : 0 < L₀ := zero_lt_one.trans_le hL₀1
  refine ⟨A * L₀ ^ α, by positivity, fun L hL => ?_⟩
  rcases le_or_gt L L₀ with hle | hgt
  · have h1 : A * L ^ α ≤ A * L₀ ^ α :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hL hle hα0.le) hA.le
    linarith [mul_nonneg hδ.le hL]
  · have h1α : 0 < 1 - α := by linarith
    have hAd_le : A / δ ≤ L ^ (1 - α) := by
      have hmax : (A / δ) ^ (1 / (1 - α)) ≤ L := (le_max_right _ _).trans hgt.le
      have hpow := Real.rpow_le_rpow (by positivity) hmax h1α.le
      rw [← Real.rpow_mul (by positivity), one_div_mul_cancel h1α.ne', Real.rpow_one] at hpow
      exact hpow
    have hAL : A * L ^ α ≤ δ * L := by
      have hL_pos : 0 < L := hL₀0.trans hgt
      have hmul := mul_le_mul_of_nonneg_right ((div_le_iff₀ hδ).mp hAd_le)
        (Real.rpow_nonneg hL α)
      have hrpow_sum : L ^ (1 - α) * L ^ α = L := by
        rw [← Real.rpow_add hL_pos, sub_add_cancel, Real.rpow_one]
      calc A * L ^ α ≤ L ^ (1 - α) * δ * L ^ α := hmul
        _ = δ * (L ^ (1 - α) * L ^ α) := by ring
        _ = δ * L := by rw [hrpow_sum]
    have hB0 : 0 ≤ A * L₀ ^ α := by positivity
    linarith

/-- Hadamard three-circles / three-lines interpolation on concentric discs around `2 + t * I`. -/
private theorem norm_le_rpow_of_annulus {h : ℂ → ℂ} {t r₁ r₂ r₃ R M₁ M₃ : ℝ}
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ ≤ r₂) (hr₂₃ : r₂ < r₃) (hr₃R : r₃ < R)
    (hM₁ : 1 ≤ M₁) (hM₃ : 1 ≤ M₃)
    (hh : DifferentiableOn ℂ h (ball (2 + (t : ℂ) * I) R))
    (hb₁ : ∀ z ∈ closedBall (2 + (t : ℂ) * I) r₁, ‖h z‖ ≤ M₁)
    (hb₃ : ∀ z ∈ closedBall (2 + (t : ℂ) * I) r₃, ‖h z‖ ≤ M₃)
    {σ : ℝ} (hσ_lo : r₁ ≤ 2 - σ) (hσ_hi : 2 - σ ≤ r₂) :
    ‖h ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      M₁ * M₃ ^ ((Real.log r₂ - Real.log r₁) / (Real.log r₃ - Real.log r₁)) := by
  set c : ℂ := 2 + (t : ℂ) * I with hc_def
  have hr₁₃ : r₁ < r₃ := hr₁₂.trans_lt hr₂₃
  have hr₃_pos : 0 < r₃ := hr₁.trans hr₁₃
  have hR_pos : 0 < R := hr₃_pos.trans hr₃R
  set l : ℝ := Real.log r₁
  set u : ℝ := Real.log r₃
  have hlu : l < u := Real.log_lt_log hr₁ hr₁₃
  let F : ℂ → ℂ := fun w => h (c + cexp w)
  have hF_in_outer : ∀ w : ℂ, w.re < Real.log R → c + cexp w ∈ ball c R := by
    intro w hw
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
    exact (Real.lt_log_iff_exp_lt hR_pos).mp hw
  have hF_diff : DifferentiableOn ℂ F {w : ℂ | w.re < Real.log R} := by
    intro w hw
    have hw' : w.re < Real.log R := hw
    have hd1 : DifferentiableAt ℂ (fun z : ℂ => c + cexp z) w := by fun_prop
    exact ((hh.differentiableAt (isOpen_ball.mem_nhds (hF_in_outer w hw'))).comp
      w hd1).differentiableWithinAt
  have hstrip_sub : closure (Complex.HadamardThreeLines.verticalStrip l u) ⊆
      {w : ℂ | w.re < Real.log R} := by
    have hcl_sub : Complex.HadamardThreeLines.verticalStrip l u ⊆
        Complex.HadamardThreeLines.verticalClosedStrip l u := by
      intro w hw
      rw [Complex.HadamardThreeLines.verticalStrip] at hw
      rw [Complex.HadamardThreeLines.verticalClosedStrip]
      exact ⟨hw.1.le, hw.2.le⟩
    have hclosed : IsClosed (Complex.HadamardThreeLines.verticalClosedStrip l u) := by
      rw [Complex.HadamardThreeLines.verticalClosedStrip]
      exact isClosed_Icc.preimage Complex.continuous_re
    refine (closure_minimal hcl_sub hclosed).trans fun w hw => ?_
    rw [Complex.HadamardThreeLines.verticalClosedStrip, mem_preimage] at hw
    exact hw.2.trans_lt (Real.log_lt_log hr₃_pos hr₃R)
  have hF_diffCont : DiffContOnCl ℂ F (Complex.HadamardThreeLines.verticalStrip l u) :=
    ⟨hF_diff.mono ((subset_closure).trans hstrip_sub),
      (hF_diff.mono hstrip_sub).continuousOn⟩
  have hF_closedStrip_le : ∀ w ∈ Complex.HadamardThreeLines.verticalClosedStrip l u,
      ‖F w‖ ≤ M₃ := by
    intro w hw
    rw [Complex.HadamardThreeLines.verticalClosedStrip, mem_preimage] at hw
    refine hb₃ (c + cexp w) ?_
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
    exact (Real.exp_le_exp.mpr hw.2).trans_eq (Real.exp_log hr₃_pos)
  have hF_bdd : BddAbove (norm ∘ F '' Complex.HadamardThreeLines.verticalClosedStrip l u) :=
    ⟨M₃, by rintro _ ⟨w, hw, rfl⟩; exact hF_closedStrip_le w hw⟩
  have hF_left : ∀ w ∈ Complex.re ⁻¹' {l}, ‖F w‖ ≤ M₁ := by
    intro w hw
    rw [mem_preimage, mem_singleton_iff] at hw
    refine hb₁ (c + cexp w) ?_
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp, hw,
      Real.exp_log hr₁]
  have hF_right : ∀ w ∈ Complex.re ⁻¹' {u}, ‖F w‖ ≤ M₃ := by
    intro w hw
    rw [mem_preimage, mem_singleton_iff] at hw
    exact hF_closedStrip_le w ⟨hlu.le.trans_eq hw.symm, hw.le⟩
  have h2σ_pos : 0 < 2 - σ := hr₁.trans_le hσ_lo
  set w₀ : ℂ := (Real.log (2 - σ) : ℂ) + (Real.pi : ℂ) * I with hw₀_def
  have hw₀_re : w₀.re = Real.log (2 - σ) := by simp [hw₀_def]
  have hw₀_mem : w₀ ∈ Complex.HadamardThreeLines.verticalClosedStrip l u := by
    rw [Complex.HadamardThreeLines.verticalClosedStrip, mem_preimage, hw₀_re]
    exact ⟨Real.log_le_log hr₁ hσ_lo, Real.log_le_log h2σ_pos (hσ_hi.trans hr₂₃.le)⟩
  have hw₀_eval : F w₀ = h ((σ : ℂ) + (t : ℂ) * I) := by
    dsimp [F]
    congr 1
    rw [hw₀_def, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log h2σ_pos,
      Complex.exp_pi_mul_I]
    dsimp [c]
    push_cast; ring
  have hhad := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    hlu hw₀_mem hF_diffCont hF_bdd hF_left hF_right
  rw [hw₀_eval, hw₀_re] at hhad
  set α : ℝ := (Real.log (2 - σ) - l) / (u - l)
  set α_max : ℝ := (Real.log r₂ - l) / (u - l)
  have hα0 : 0 ≤ α :=
    div_nonneg (sub_nonneg.mpr (Real.log_le_log hr₁ hσ_lo)) (sub_pos.mpr hlu).le
  have hα_le : α ≤ α_max :=
    div_le_div_of_nonneg_right
      (sub_le_sub_right (Real.log_le_log h2σ_pos hσ_hi) l)
      (sub_pos.mpr hlu).le
  have hM₁_pow : M₁ ^ (1 - α) ≤ M₁ := by
    simpa using Real.rpow_le_rpow_of_exponent_le hM₁ (by linarith : 1 - α ≤ 1)
  have hM₃_pow : M₃ ^ α ≤ M₃ ^ α_max :=
    Real.rpow_le_rpow_of_exponent_le hM₃ hα_le
  exact hhad.trans (mul_le_mul hM₁_pow hM₃_pow (Real.rpow_nonneg (by linarith) _) (by linarith))

/-- **Key Hadamard Three-Circles / Three-Lines Estimate on `invZeta`:**
Under `hz : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0` (`1 / 2 ≤ θ`, `0 < δ`, `θ + 4 * δ < 1`),
there exists `K_inv > 0` such that `‖invZeta (σ + t * I)‖ ≤ K_inv * (|t| + 2) ^ δ`
uniformly for all `σ ∈ [θ + 2 * δ, 2]` and all `t : ℝ`. -/
theorem exists_invZeta_subpower_bound {θ δ : ℝ} (half : 1 / 2 ≤ θ)
    (hδ : 0 < δ) (hθ4 : θ + 4 * δ < 1)
    (hz : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) :
    ∃ K_inv : ℝ, 0 < K_inv ∧ ∀ σ t : ℝ, θ + 2 * δ ≤ σ → σ ≤ 2 →
      ‖invZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ K_inv * (|t| + 2) ^ δ := by
  let R_outer : ℝ := 2 - θ - δ
  let R_mid : ℝ := 2 - θ - 3 * δ / 2
  let R_target : ℝ := 2 - θ - 2 * δ
  have h_half_lt_target : 1 / 2 < R_target := by dsimp [R_target]; linarith
  have h_target_lt_mid : R_target < R_mid := by dsimp [R_target, R_mid]; linarith
  have h_mid_lt_outer : R_mid < R_outer := by dsimp [R_mid, R_outer]; linarith
  have h_outer_lt_32 : R_outer < 3 / 2 := by dsimp [R_outer]; linarith
  have h_34_lt_outer : 3 / 4 < R_outer := by dsimp [R_outer]; linarith
  -- Inner constant `M₀`, `M₁` independent of `t`
  let M₀ : ℝ := Real.log (4 * zetaRemConst + 1) + 1
  have hM₀_pos : 0 < M₀ := by
    have h1 : 1 ≤ 4 * zetaRemConst + 1 := by linarith [zetaRemConst_nonneg]
    dsimp [M₀]
    linarith [Real.log_nonneg h1]
  let M₁ : ℝ := max 1 (2 * M₀ * (1 / 2) / (3 / 4 - 1 / 2))
  have hM₁_ge1 : 1 ≤ M₁ := le_max_left _ _
  have hM₁_pos : 0 < M₁ := zero_lt_one.trans_le hM₁_ge1
  -- Outer growth constants `C_ζ`, `C₂`, `C₃` independent of `t` (`|t| ≥ 4`)
  let C_ζ : ℝ := 4 * (1 + 3 * zetaRemConst) + 1
  have hC_ζ_ge1 : 1 ≤ C_ζ := by dsimp [C_ζ]; linarith [zetaRemConst_nonneg]
  let C₂ : ℝ := Real.log C_ζ + 2
  have hC₂_pos : 0 < C₂ := by dsimp [C₂]; linarith [Real.log_nonneg hC_ζ_ge1]
  let C₃ : ℝ := max 2 (2 * C₂ * R_mid / (R_outer - R_mid))
  have hC₃_ge2 : 2 ≤ C₃ := le_max_left _ _
  have hC₃_pos : 0 < C₃ := by linarith
  -- Hadamard interpolation exponent `α_max ∈ (0, 1)`
  let l : ℝ := Real.log (1 / 2)
  let u : ℝ := Real.log R_mid
  have hlu : l < u := Real.log_lt_log (by norm_num) (h_half_lt_target.trans h_target_lt_mid)
  let α_max : ℝ := (Real.log R_target - l) / (u - l)
  have hα_pos : 0 < α_max :=
    div_pos (sub_pos.mpr (Real.log_lt_log (by norm_num) h_half_lt_target)) (sub_pos.mpr hlu)
  have hα_lt1 : α_max < 1 := by
    rw [div_lt_one (sub_pos.mpr hlu)]
    linarith [Real.log_lt_log (by linarith) h_target_lt_mid]
  obtain ⟨B_abs, hB_abs0, hB_abs⟩ :=
    mul_rpow_le_linear_add hα_pos hα_lt1 (mul_pos hM₁_pos (Real.rpow_pos_of_pos hC₃_pos α_max)) hδ
  let C_exp : ℝ := max M₁ B_abs
  have hC_exp0 : 0 ≤ C_exp := le_trans hB_abs0 (le_max_right _ _)
  let K_high : ℝ := 4 * Real.exp C_exp
  -- High-height estimate: `4 ≤ |t|`
  have h_high : ∀ σ t : ℝ, 4 ≤ |t| → θ + 2 * δ ≤ σ → σ ≤ 2 →
      ‖invZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ K_high * (|t| + 2) ^ δ := by
    intro σ t ht4 hσ_lo hσ_hi
    set c : ℂ := 2 + (t : ℂ) * I with hc_def
    have hc_ge : 1 / 4 ≤ ‖riemannZeta c‖ := norm_zeta_two_add_ge t
    have hc_pos : 0 < ‖riemannZeta c‖ := by linarith
    -- Holomorphicity and nonvanishing of `riemannZeta` on `ball c R_outer`
    have hball_props : ∀ z ∈ ball c R_outer,
        θ < z.re ∧ 1 / 4 ≤ z.re ∧ 1 ≤ |z.im| ∧ z ≠ 1 ∧ ‖z‖ ≤ 3 * (|t| + 2) := by
      intro z hz_mem
      have hdist : ‖z - c‖ < R_outer := mem_ball_iff_norm.mp hz_mem
      have hre_diff := (abs_lt.mp ((Complex.abs_re_le_norm (z - c)).trans_lt hdist)).1
      have hre_diff2 := (abs_lt.mp ((Complex.abs_re_le_norm (z - c)).trans_lt hdist)).2
      have him_diff := abs_lt.mp ((Complex.abs_im_le_norm (z - c)).trans_lt hdist)
      have hcre : c.re = 2 := by simp [hc_def]
      have hcim : c.im = t := by simp [hc_def]
      rw [Complex.sub_re, hcre] at hre_diff hre_diff2
      rw [Complex.sub_im, hcim] at him_diff
      have hz_θ : θ < z.re := by dsimp [R_outer] at hre_diff; linarith
      have hz_14 : 1 / 4 ≤ z.re := by linarith
      have hz_im_lo : 1 ≤ |z.im| := by
        rcases le_total 0 t with ht0 | ht0
        · rw [abs_of_nonneg ht0] at ht4
          have him_pos : 1 ≤ z.im := by linarith [him_diff.1, h_outer_lt_32]
          exact him_pos.trans (le_abs_self _)
        · rw [abs_of_nonpos ht0] at ht4
          have him_neg : z.im ≤ -1 := by linarith [him_diff.2, h_outer_lt_32]
          have : 1 ≤ -z.im := by linarith
          exact this.trans (neg_le_abs _)
      have hz_ne1 : z ≠ 1 := by rintro rfl; simp at hz_im_lo; linarith
      have hz_norm : ‖z‖ ≤ 3 * (|t| + 2) := by
        have hre_abs : |z.re| ≤ 7 / 2 := by
          rw [abs_of_pos (by linarith)]
          linarith [h_outer_lt_32]
        have him_abs : |z.im| ≤ |t| + 3 / 2 := by
          have htri := abs_add_le (z.im - t) t
          rw [sub_add_cancel] at htri
          have hzim_t : |z.im - t| < 3 / 2 := (abs_lt.mpr him_diff).trans h_outer_lt_32
          linarith
        calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
          _ ≤ 7 / 2 + (|t| + 3 / 2) := add_le_add hre_abs him_abs
          _ = |t| + 5 := by ring
          _ ≤ 3 * (|t| + 2) := by linarith [abs_nonneg t]
      exact ⟨hz_θ, hz_14, hz_im_lo, hz_ne1, hz_norm⟩
    have hf_diff : DifferentiableOn ℂ riemannZeta (ball c R_outer) := fun z hz_mem =>
      (differentiableAt_riemannZeta (hball_props z hz_mem).2.2.2.1).differentiableWithinAt
    have hf_ne : ∀ z ∈ ball c R_outer, riemannZeta z ≠ 0 :=
      fun z hz_mem => hz z (hball_props z hz_mem).1
    obtain ⟨h, hh_diff, hhc, h_exp⟩ :=
      exists_log_on_ball (by linarith : 0 < R_outer) hf_diff hf_ne
    -- Inner Borel–Carathéodory on `ball c (3/4)` -> `closedBall c (1/2)`
    have h_inner_bd : ∀ z ∈ closedBall c (1 / 2), ‖h z‖ ≤ M₁ := by
      have hsub34 : ball c (3 / 4) ⊆ ball c R_outer := ball_subset_ball h_34_lt_outer.le
      have hre34 : ∀ z ∈ ball c (3 / 4), (h z).re ≤ M₀ := by
        intro z hz34
        have hdist : ‖z - c‖ < 3 / 4 := mem_ball_iff_norm.mp hz34
        have hre_d := (abs_lt.mp ((Complex.abs_re_le_norm (z - c)).trans_lt hdist)).1
        have hcre : c.re = 2 := by simp [hc_def]
        rw [Complex.sub_re, hcre] at hre_d
        have hz_54 : 5 / 4 ≤ z.re := by linarith
        have hz_up : ‖riemannZeta z‖ ≤ zetaRemConst := norm_riemannZeta_le_of_five_quarters hz_54
        have heq := congrArg norm (h_exp z (hsub34 hz34))
        rw [norm_mul, Complex.norm_exp] at heq
        have hexp_le : Real.exp (h z).re ≤ 4 * zetaRemConst + 1 := by
          have : ‖riemannZeta c‖ * Real.exp (h z).re ≤ zetaRemConst := by linarith
          have h4 := mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 4)
          have h14 : 1 ≤ 4 * ‖riemannZeta c‖ := by linarith
          nlinarith [Real.exp_pos (h z).re]
        have hlog_le := Real.log_le_log (Real.exp_pos _) hexp_le
        rw [Real.log_exp] at hlog_le
        dsimp [M₀]; linarith
      intro z hz12
      exact (norm_le_of_re_le_on_ball (by norm_num) (by norm_num : (1 / 2 : ℝ) < 3 / 4)
        hM₀_pos (hh_diff.mono hsub34) hhc hre34 z hz12).trans (le_max_right _ _)
    -- Outer Borel–Carathéodory on `ball c R_outer` -> `closedBall c R_mid`
    set L : ℝ := Real.log (|t| + 2) with hL_def
    have hL_gt1 : 1 < L := by
      dsimp [L]
      have h6 : (3 : ℝ) ≤ |t| + 2 := by linarith
      have hexp1 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
      exact (Real.lt_log_iff_exp_lt (by positivity)).mpr (hexp1.trans_le h6)
    have hL_pos : 0 < L := zero_lt_one.trans hL_gt1
    have h_outer_bd : ∀ z ∈ closedBall c R_mid, ‖h z‖ ≤ C₃ * L := by
      have hre_out : ∀ z ∈ ball c R_outer, (h z).re ≤ C₂ * L := by
        intro z hz_mem
        obtain ⟨_, hz_14, hz_im1, _, hz_norm⟩ := hball_props z hz_mem
        have hz_up1 := norm_riemannZeta_le_of_re_ge_quarter hz_14 hz_im1
        have hz_up2 : ‖riemannZeta z‖ ≤ (1 + 3 * zetaRemConst) * (|t| + 2) := by
          have ht2_ge1 : 1 ≤ |t| + 2 := by linarith
          calc ‖riemannZeta z‖
              ≤ 1 + zetaRemConst * ‖z‖ := hz_up1
            _ ≤ (|t| + 2) + zetaRemConst * (3 * (|t| + 2)) :=
                add_le_add ht2_ge1 (mul_le_mul_of_nonneg_left hz_norm zetaRemConst_nonneg)
            _ = (1 + 3 * zetaRemConst) * (|t| + 2) := by ring
        have heq := congrArg norm (h_exp z hz_mem)
        rw [norm_mul, Complex.norm_exp] at heq
        have hexp_le : Real.exp (h z).re ≤ C_ζ * (|t| + 2) := by
          have h1 : ‖riemannZeta c‖ * Real.exp (h z).re ≤ (1 + 3 * zetaRemConst) * (|t| + 2) := by
            linarith
          have h4 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 4)
          have h14 : 1 ≤ 4 * ‖riemannZeta c‖ := by linarith
          dsimp [C_ζ]
          nlinarith [Real.exp_pos (h z).re]
        have hlog_le := Real.log_le_log (Real.exp_pos _) hexp_le
        rw [Real.log_exp, Real.log_mul (by linarith) (by positivity)] at hlog_le
        dsimp [C₂]
        nlinarith [Real.log_nonneg hC_ζ_ge1]
      intro z hz_mid
      have hbc := norm_le_of_re_le_on_ball (by linarith : 0 ≤ R_mid) h_mid_lt_outer
        (mul_pos hC₂_pos hL_pos) hh_diff hhc hre_out z hz_mid
      have heq_mul : 2 * (C₂ * L) * R_mid / (R_outer - R_mid) =
          (2 * C₂ * R_mid / (R_outer - R_mid)) * L := by ring
      rw [heq_mul] at hbc
      exact hbc.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hL_pos.le)
    -- Bound `‖h (σ + t * I)‖` across `σ ∈ [θ + 2*δ, 2]`
    set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs_def
    have hs_in_outer : s ∈ ball c R_outer := by
      rw [mem_ball, dist_eq_norm]
      have hdiff : s - c = (((σ - 2) : ℝ) : ℂ) := by dsimp [s, c]; push_cast; ring
      rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      dsimp [R_outer]; linarith
    have hs_ne1 : s ≠ 1 := (hball_props s hs_in_outer).2.2.2.1
    have h_norm_hs : ‖h s‖ ≤ δ * L + C_exp := by
      rcases le_or_gt (3 / 2 : ℝ) σ with hσ_32 | hσ_lt_32
      · -- `σ ∈ [3/2, 2]`: directly inside `closedBall c (1/2)`
        have hs12 : s ∈ closedBall c (1 / 2) := by
          rw [mem_closedBall, dist_eq_norm]
          have hdiff : s - c = (((σ - 2) : ℝ) : ℂ) := by dsimp [s, c]; push_cast; ring
          rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
          linarith
        calc ‖h s‖ ≤ M₁ := h_inner_bd s hs12
          _ ≤ C_exp := le_max_left _ _
          _ ≤ δ * L + C_exp := by linarith [mul_pos hδ hL_pos]
      · -- `σ ∈ [θ + 2*δ, 3/2)`: apply `norm_le_rpow_of_annulus`
        have hC₃L_ge1 : 1 ≤ C₃ * L := by nlinarith
        have hhad := norm_le_rpow_of_annulus (σ := σ) (r₁ := 1 / 2) (r₂ := R_target) (r₃ := R_mid)
          (R := R_outer) (by norm_num) h_half_lt_target.le h_target_lt_mid h_mid_lt_outer
          hM₁_ge1 hC₃L_ge1 hh_diff h_inner_bd h_outer_bd
          (by linarith) (by dsimp [R_target]; linarith)
        calc ‖h s‖ ≤ M₁ * (C₃ * L) ^ α_max := hhad
          _ = (M₁ * C₃ ^ α_max) * L ^ α_max := by
              rw [Real.mul_rpow hC₃_pos.le hL_pos.le, mul_assoc]
          _ ≤ δ * L + B_abs := hB_abs L hL_pos.le
          _ ≤ δ * L + C_exp := add_le_add le_rfl (le_max_right _ _)
    -- Convert `‖h s‖` bound to `‖invZeta s‖`
    rw [invZeta_eq_inv hs_ne1, h_exp s hs_in_outer, mul_inv, norm_mul, norm_inv,
      ← Complex.exp_neg, Complex.norm_exp]
    have hinv_c : ‖riemannZeta c‖⁻¹ ≤ 4 := by
      rw [inv_le_comm₀ hc_pos (by norm_num)]
      linarith [hc_ge]
    have hneg_re : (-h s).re ≤ ‖h s‖ := by
      rw [neg_re]
      exact (neg_le_abs _).trans (Complex.abs_re_le_norm _)
    have hexp_bound : Real.exp (-h s).re ≤ Real.exp C_exp * (|t| + 2) ^ δ := by
      calc Real.exp (-h s).re
          ≤ Real.exp (δ * L + C_exp) := Real.exp_le_exp.mpr (hneg_re.trans h_norm_hs)
        _ = Real.exp C_exp * Real.exp (L * δ) := by
            rw [Real.exp_add, mul_comm (Real.exp (δ * L)), mul_comm δ L]
        _ = Real.exp C_exp * (|t| + 2) ^ δ := by
            dsimp [L]; rw [← Real.rpow_def_of_pos (by positivity)]
    calc ‖riemannZeta c‖⁻¹ * Real.exp (-h s).re
        ≤ 4 * (Real.exp C_exp * (|t| + 2) ^ δ) :=
          mul_le_mul hinv_c hexp_bound (Real.exp_pos _).le (by norm_num)
      _ = K_high * (|t| + 2) ^ δ := by dsimp [K_high]; ring
  -- Compact low-height rectangle `[θ + 2*δ, 2] ×ℂ [-4, 4]`
  let rectLow : Set ℂ := Icc (θ + 2 * δ) 2 ×ℂ Icc (-4 : ℝ) 4
  have hrect_comp : IsCompact rectLow := isCompact_Icc.reProdIm isCompact_Icc
  have hrect_cont : ContinuousOn invZeta rectLow := by
    intro z hz_mem
    have hz_re : θ < z.re := by linarith [hz_mem.1.1]
    exact (differentiableAt_invZeta_of_zeroFree hz hz_re).continuousAt.continuousWithinAt
  obtain ⟨B_low, hB_low⟩ := hrect_comp.exists_bound_of_continuousOn hrect_cont
  let K_inv : ℝ := max K_high (max B_low 0 + 1)
  have hK_inv_pos : 0 < K_inv := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  refine ⟨K_inv, hK_inv_pos, fun σ t hσ_lo hσ_hi => ?_⟩
  rcases le_or_gt 4 |t| with ht4 | ht4
  · exact (h_high σ t ht4 hσ_lo hσ_hi).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hmem : (σ : ℂ) + (t : ℂ) * I ∈ rectLow := by
      refine ⟨⟨by simpa using hσ_lo, by simpa using hσ_hi⟩, ?_⟩
      have him : ((σ : ℂ) + (t : ℂ) * I).im = t := by simp
      rw [mem_preimage, him]
      exact ⟨(abs_lt.mp ht4).1.le, (abs_lt.mp ht4).2.le⟩
    have h1 := hB_low _ hmem
    have ht_pow_ge1 : 1 ≤ (|t| + 2) ^ δ :=
      Real.one_le_rpow (by linarith [abs_nonneg t]) hδ.le
    have hK_ge : B_low ≤ K_inv :=
      (le_max_left B_low 0).trans ((le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _))
    calc ‖invZeta ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ B_low := h1
      _ ≤ K_inv := hK_ge
      _ = K_inv * 1 := (mul_one _).symm
      _ ≤ K_inv * (|t| + 2) ^ δ := mul_le_mul_of_nonneg_left ht_pow_ge1 hK_inv_pos.le

/-! ### 3. Truncated Perron Kernel Estimates (Adapted from First-Party `ZetaPerron`) -/

private def kf (L : ℝ) (s : ℂ) : ℂ := cexp (s * (L : ℂ)) / s

private def kint (L c T : ℝ) : ℂ := ∫ t in (-T)..T, kf L ((c : ℂ) + (t : ℂ) * I)

private theorem norm_kf (L : ℝ) (s : ℂ) : ‖kf L s‖ = Real.exp (s.re * L) / ‖s‖ := by
  unfold kf
  rw [norm_div, Complex.norm_exp]
  have : (s * (L : ℂ)).re = s.re * L := by
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  rw [this]

private theorem horiz_ne (σ h : ℝ) (hh : h ≠ 0) : (σ : ℂ) + (h : ℂ) * I ≠ 0 := by
  intro H; have := congrArg Complex.im H; simp at this; exact hh this

private theorem vert_ne (x t : ℝ) (hx : x ≠ 0) : (x : ℂ) + (t : ℂ) * I ≠ 0 := by
  intro H; have := congrArg Complex.re H; simp at this; exact hx this

private theorem cont_kf_horiz (L h : ℝ) (hh : h ≠ 0) :
    Continuous fun σ : ℝ => kf L ((σ : ℂ) + (h : ℂ) * I) := by
  unfold kf; exact Continuous.div (by fun_prop) (by fun_prop) fun σ => horiz_ne σ h hh

private theorem cont_kf_vert (L x : ℝ) (hx : x ≠ 0) :
    Continuous fun t : ℝ => kf L ((x : ℂ) + (t : ℂ) * I) := by
  unfold kf; exact Continuous.div (by fun_prop) (by fun_prop) fun t => vert_ne x t hx

private theorem cont_inv_horiz (h : ℝ) (hh : h ≠ 0) :
    Continuous fun σ : ℝ => ((σ : ℂ) + (h : ℂ) * I)⁻¹ :=
  Continuous.inv₀ (by fun_prop) fun σ => horiz_ne σ h hh

private theorem cont_inv_vert (x : ℝ) (hx : x ≠ 0) :
    Continuous fun t : ℝ => ((x : ℂ) + (t : ℂ) * I)⁻¹ :=
  Continuous.inv₀ (by fun_prop) fun t => vert_ne x t hx

private theorem norm_vert_le (L x T : ℝ) (hx : x ≠ 0) (hT : 0 ≤ T) :
    ‖∫ t in (-T)..T, kf L ((x : ℂ) + (t : ℂ) * I)‖ ≤ 2 * T * (Real.exp (x * L) / |x|) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T)
    (C := Real.exp (x * L) / |x|) (f := fun t : ℝ => kf L ((x : ℂ) + (t : ℂ) * I)) ?_
  · have habs : |T - -T| = 2 * T := by rw [abs_of_nonneg (by linarith)]; ring
    rw [habs] at h; linarith [h]
  · intro t _
    rw [norm_kf]
    have hre : ((x : ℂ) + (t : ℂ) * I).re = x := by simp
    rw [hre]
    have hle : |x| ≤ ‖(x : ℂ) + (t : ℂ) * I‖ := by
      have := Complex.abs_re_le_norm ((x : ℂ) + (t : ℂ) * I); rwa [hre] at this
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le (abs_pos.mpr hx) hle

private theorem norm_horiz_le (L p q h : ℝ) (hpq : p ≤ q) (hh : h ≠ 0) :
    ‖∫ σ in p..q, kf L ((σ : ℂ) + (h : ℂ) * I)‖ ≤ (∫ σ in p..q, Real.exp (σ * L)) / |h| := by
  have hpos : 0 < |h| := abs_pos.mpr hh
  have key : ∀ σ : ℝ, ‖kf L ((σ : ℂ) + (h : ℂ) * I)‖ ≤ Real.exp (σ * L) / |h| := by
    intro σ
    rw [norm_kf]
    have hre : ((σ : ℂ) + (h : ℂ) * I).re = σ := by simp
    have him : ((σ : ℂ) + (h : ℂ) * I).im = h := by simp
    rw [hre]
    have hle : |h| ≤ ‖(σ : ℂ) + (h : ℂ) * I‖ := by
      have := Complex.abs_im_le_norm ((σ : ℂ) + (h : ℂ) * I); rwa [him] at this
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hpos hle
  have := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hpq
    (Filter.Eventually.of_forall fun σ _ => key σ)
    (Continuous.intervalIntegrable (by fun_prop) p q)
  rwa [intervalIntegral.integral_div] at this

private theorem integral_exp_mul_le_pos {L p q : ℝ} (hL : 0 < L) :
    ∫ σ in p..q, Real.exp (σ * L) ≤ Real.exp (q * L) / L := by
  rw [intervalIntegral.integral_comp_mul_right (fun x => Real.exp x) hL.ne', integral_exp,
    smul_eq_mul, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (p * L)]) hL.le

private theorem integral_exp_mul_le_neg {L p q : ℝ} (hL : L < 0) :
    ∫ σ in p..q, Real.exp (σ * L) ≤ Real.exp (p * L) / (-L) := by
  rw [intervalIntegral.integral_comp_mul_right (fun x => Real.exp x) hL.ne, integral_exp,
    smul_eq_mul, inv_mul_eq_div]
  have hL' : 0 < -L := by linarith
  have : (Real.exp (q * L) - Real.exp (p * L)) / L
      = (Real.exp (p * L) - Real.exp (q * L)) / (-L) := by
    rw [div_neg, ← neg_div]; ring
  rw [this]
  exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (q * L)]) hL'.le

private theorem integral_exp_mul_le_const {L p q M : ℝ} (hpq : p ≤ q)
    (h : ∀ σ ∈ Icc p q, Real.exp (σ * L) ≤ M) :
    ∫ σ in p..q, Real.exp (σ * L) ≤ (q - p) * M := by
  have := intervalIntegral.integral_mono_on (μ := volume) hpq
    (Continuous.intervalIntegrable (by fun_prop) p q)
    (intervalIntegrable_const (c := M)) h
  simpa using this

private theorem differentiableAt_kf (L : ℝ) {s : ℂ} (hs : s ≠ 0) : DifferentiableAt ℂ (kf L) s := by
  unfold kf
  exact ((differentiableAt_id.mul_const _).cexp).div differentiableAt_id hs

private theorem rect_kf_right (L p q T : ℝ) (hp : 0 < p) (hpq : p ≤ q) :
    (∫ σ in p..q, kf L ((σ : ℂ) + ((-T : ℝ) : ℂ) * I))
      - (∫ σ in p..q, kf L ((σ : ℂ) + ((T : ℝ) : ℂ) * I))
      + I • (∫ t in (-T)..T, kf L ((q : ℂ) + (t : ℂ) * I))
      - I • (∫ t in (-T)..T, kf L ((p : ℂ) + (t : ℂ) * I)) = 0 := by
  have H : DifferentiableOn ℂ (kf L) ([[p, q]] ×ℂ [[-T, T]]) := by
    intro s hs
    have h1 : s.re ∈ [[p, q]] := hs.1
    rw [Set.uIcc_of_le hpq] at h1
    have hs0 : s ≠ 0 := by intro h; rw [h] at h1; simp at h1; linarith [h1.1]
    exact (differentiableAt_kf L hs0).differentiableWithinAt
  exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn (kf L) ⟨p, -T⟩ ⟨q, T⟩ H

private theorem norm_kint_le_right (L c R T : ℝ) (hc : 0 < c) (hcR : c ≤ R) (hT : 0 < T) :
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
    unfold kint; linear_combination -H
  have hn : ‖kint L c T‖ = ‖I • kint L c T‖ := by rw [norm_smul, Complex.norm_I, one_mul]
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

private theorem log_neg_of_im_neg {z : ℂ} (h : z.im < 0) :
    Complex.log (-z) = Complex.log z + π * I := by
  rw [Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_add_pi_of_im_neg h]
  push_cast; ring

private theorem log_neg_of_im_pos {z : ℂ} (h : 0 < z.im) :
    Complex.log (-z) = Complex.log z - π * I := by
  rw [Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_sub_pi_of_im_pos h]
  push_cast; ring

private theorem integral_inv_horiz (p q h : ℝ) (hh : h ≠ 0) :
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

private theorem integral_inv_vert_pos (x T : ℝ) (hx : 0 < x) :
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
    simpa [div_eq_mul_inv] using h1.clog_real h2
  · exact (continuous_const.mul (cont_inv_vert x hx.ne')).intervalIntegrable _ _

private theorem integral_inv_vert_neg (x T : ℝ) (hx : x < 0) (hT : 0 < T) :
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

private theorem rect_kf_pole (L a c T : ℝ) (ha : 0 < a) (hc : 0 < c) (hT : 0 < T) :
    (∫ σ in (-a)..c, kf L ((σ : ℂ) + ((-T : ℝ) : ℂ) * I))
      - (∫ σ in (-a)..c, kf L ((σ : ℂ) + ((T : ℝ) : ℂ) * I))
      + I • (∫ t in (-T)..T, kf L ((c : ℂ) + (t : ℂ) * I))
      - I • (∫ t in (-T)..T, kf L (((-a : ℝ) : ℂ) + (t : ℂ) * I)) = 2 * π * I := by
  set g : ℂ → ℂ := dslope (fun s : ℂ => cexp (s * (L : ℂ))) 0 with hg
  have hdiff : Differentiable ℂ (fun s : ℂ => cexp (s * (L : ℂ))) := by fun_prop
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
    exact intervalIntegral.integral_congr fun σ _ => hgs _ (horiz_ne σ (-T) hTn)
  have e2 : (∫ σ in (-a)..c, g ((σ : ℂ) + ((T : ℝ) : ℂ) * I))
      = (∫ σ in (-a)..c, kf L ((σ : ℂ) + ((T : ℝ) : ℂ) * I))
        - ∫ σ in (-a)..c, ((σ : ℂ) + ((T : ℝ) : ℂ) * I)⁻¹ := by
    rw [← intervalIntegral.integral_sub ((cont_kf_horiz L T hT.ne').intervalIntegrable _ _)
      ((cont_inv_horiz T hT.ne').intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun σ _ => hgs _ (horiz_ne σ T hT.ne')
  have e3 : (∫ t in (-T)..T, g ((c : ℂ) + (t : ℂ) * I))
      = (∫ t in (-T)..T, kf L ((c : ℂ) + (t : ℂ) * I))
        - ∫ t in (-T)..T, ((c : ℂ) + (t : ℂ) * I)⁻¹ := by
    rw [← intervalIntegral.integral_sub ((cont_kf_vert L c hc.ne').intervalIntegrable _ _)
      ((cont_inv_vert c hc.ne').intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun t _ => hgs _ (vert_ne c t hc.ne')
  have e4 : (∫ t in (-T)..T, g (((-a : ℝ) : ℂ) + (t : ℂ) * I))
      = (∫ t in (-T)..T, kf L (((-a : ℝ) : ℂ) + (t : ℂ) * I))
        - ∫ t in (-T)..T, (((-a : ℝ) : ℂ) + (t : ℂ) * I)⁻¹ := by
    rw [← intervalIntegral.integral_sub ((cont_kf_vert L (-a) han).intervalIntegrable _ _)
      ((cont_inv_vert (-a) han).intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun t _ => hgs _ (vert_ne (-a) t han)
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

private theorem norm_kint_sub_le_left (L a c T : ℝ) (ha : 0 < a) (hc : 0 < c) (hT : 0 < T) :
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
    unfold kint; simp only [smul_eq_mul] at H ⊢; linear_combination H
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

private theorem kint_bound_neg {L c T : ℝ} (hL : L < 0) (hc : 0 < c) (hT : 0 < T) :
    ‖kint L c T‖ ≤ 2 * Real.exp (c * L) / (T * (-L)) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hq : 0 < 2 * T / ε := by positivity
  set R := c + 2 * T / ε
  have hcR : c ≤ R := by linarith
  have H := norm_kint_le_right L c R T hc hcR hT
  have hint := integral_exp_mul_le_neg (p := c) (q := R) hL
  have h1 : 2 * T * (Real.exp (R * L) / R) ≤ ε := by
    have he : Real.exp (R * L) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith)
    have hR2 : 2 * T / ε ≤ R := by linarith
    have : Real.exp (R * L) / R ≤ 1 / (2 * T / ε) := div_le_div₀ zero_le_one he hq hR2
    calc 2 * T * (Real.exp (R * L) / R) ≤ 2 * T * (1 / (2 * T / ε)) := by gcongr
      _ = ε := by field_simp
  have h2 : (∫ σ in c..R, Real.exp (σ * L)) / T ≤ Real.exp (c * L) / (-L) / T :=
    div_le_div_of_nonneg_right hint hT.le
  have h3 : 2 * (Real.exp (c * L) / (-L) / T) = 2 * Real.exp (c * L) / (T * (-L)) := by
    field_simp
  linarith

private theorem kint_bound_nonpos {L c T : ℝ} (hL : L ≤ 0) (hc : 0 < c) (hT : 0 < T) :
    ‖kint L c T‖ ≤ 4 * Real.exp (c * L) := by
  have hcR : c ≤ c + T := by linarith
  have H := norm_kint_le_right L c (c + T) T hc hcR hT
  have hint := integral_exp_mul_le_const (L := L) (p := c) (q := c + T) (M := Real.exp (c * L)) hcR
    fun σ hσ => Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hσ.1 hL)
  have h1 : 2 * T * (Real.exp ((c + T) * L) / (c + T)) ≤ 2 * Real.exp (c * L) := by
    have he : Real.exp ((c + T) * L) ≤ Real.exp (c * L) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hcR hL)
    have hcT : 0 < c + T := by linarith
    rw [← mul_div_assoc, div_le_iff₀ hcT]
    nlinarith [Real.exp_pos ((c + T) * L)]
  have h2 : (∫ σ in c..(c + T), Real.exp (σ * L)) / T ≤ Real.exp (c * L) := by
    rw [div_le_iff₀ hT]; linarith
  linarith

private theorem kint_bound_pos {L c T : ℝ} (hL : 0 < L) (hc : 0 < c) (hT : 0 < T) :
    ‖kint L c T - 2 * π‖ ≤ 2 * Real.exp (c * L) / (T * L) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have ha : 0 < 2 * T / ε := by positivity
  set a := 2 * T / ε with ha_def
  have H := norm_kint_sub_le_left L a c T ha hc hT
  have hint := integral_exp_mul_le_pos (p := -a) (q := c) hL
  have h1 : 2 * T * (Real.exp (-a * L) / a) ≤ ε := by
    have he : Real.exp (-a * L) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith)
    have : Real.exp (-a * L) / a ≤ 1 / a := div_le_div_of_nonneg_right he ha.le
    calc 2 * T * (Real.exp (-a * L) / a) ≤ 2 * T * (1 / a) := by gcongr
      _ = ε := by rw [ha_def]; field_simp
  have h2 : (∫ σ in (-a)..c, Real.exp (σ * L)) / T ≤ Real.exp (c * L) / L / T :=
    div_le_div_of_nonneg_right hint hT.le
  have h3 : 2 * (Real.exp (c * L) / L / T) = 2 * Real.exp (c * L) / (T * L) := by
    field_simp
  linarith

private theorem kint_bound_nonneg {L c T : ℝ} (hL : 0 ≤ L) (hc : 0 < c) (hT : 0 < T) :
    ‖kint L c T - 2 * π‖ ≤ (4 + 2 * c / T) * Real.exp (c * L) := by
  have H := norm_kint_sub_le_left L T c T hT hc hT
  have hac : -T ≤ c := by linarith
  have hint := integral_exp_mul_le_const (L := L) (p := -T) (q := c) (M := Real.exp (c * L)) hac
    fun σ hσ => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hσ.2 hL)
  have hE : 1 ≤ Real.exp (c * L) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by positivity)
  have h1 : 2 * T * (Real.exp (-T * L) / T) ≤ 2 * Real.exp (c * L) := by
    have he : Real.exp (-T * L) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith)
    have : 2 * T * (Real.exp (-T * L) / T) = 2 * Real.exp (-T * L) := by field_simp
    rw [this]; linarith
  have h2 : (∫ σ in (-T)..c, Real.exp (σ * L)) / T ≤ (c - -T) * Real.exp (c * L) / T :=
    div_le_div_of_nonneg_right hint hT.le
  have h3 : (4 + 2 * c / T) * Real.exp (c * L)
      = 2 * Real.exp (c * L) + 2 * ((c - -T) * Real.exp (c * L) / T) := by
    field_simp; ring
  linarith

/-! ### 4. Truncated Perron Formula for Summatory Möbius `M(N)` -/

private def Ln (u : ℝ) (n : ℕ) : ℝ := Real.log u - Real.log n

private theorem sum_range_rpow_le (ε : ℝ) (hε : 0 < ε) (a : ℕ) :
    ∑ i ∈ Finset.range (a + 2), ((i : ℝ) ^ (1 + ε))⁻¹ ≤ 1 + 1 / ε := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have h0 : (((0 : ℕ) : ℝ) ^ (1 + ε))⁻¹ = 0 := by
    rw [Nat.cast_zero, Real.zero_rpow (by linarith), inv_zero]
  have h1 : (((0 + 1 : ℕ) : ℝ) ^ (1 + ε))⁻¹ = 1 := by simp
  rw [h0, h1, add_zero]
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-(1 + ε))) (Icc (1 : ℝ) (1 + (a : ℝ))) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)).mono
      fun x hx => lt_of_lt_of_le zero_lt_one hx.1
  have hsum := AntitoneOn.sum_le_integral (x₀ := 1) (a := a)
    (f := fun x : ℝ => x ^ (-(1 + ε))) hanti
  have hterm : ∀ i ∈ Finset.range a, (((i + 1 + 1 : ℕ) : ℝ) ^ (1 + ε))⁻¹
      = (fun x : ℝ => x ^ (-(1 + ε))) (1 + ((i + 1 : ℕ) : ℝ)) := by
    intro i _
    have hpos : (0 : ℝ) ≤ 1 + ((i + 1 : ℕ) : ℝ) := by positivity
    show _ = (1 + ((i + 1 : ℕ) : ℝ)) ^ (-(1 + ε))
    rw [Real.rpow_neg hpos]; congr 2; push_cast; ring
  rw [Finset.sum_congr rfl hterm]
  have hint : ∫ x in (1 : ℝ)..1 + (a : ℝ), x ^ (-(1 + ε)) ≤ 1 / ε := by
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    rw [integral_rpow (Or.inr ⟨by linarith, by
      rw [Set.uIcc_of_le (by linarith)]; intro h; linarith [h.1]⟩)]
    have e : -(1 + ε) + 1 = -ε := by ring
    rw [e, Real.one_rpow, div_neg, ← neg_div, neg_sub]
    exact div_le_div_of_nonneg_right
      (by linarith [Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + a) (-ε)]) hε.le
  linarith

private theorem tsum_rpow_le (ε : ℝ) (hε : 0 < ε) :
    ∑' n : ℕ, ((n : ℝ) ^ (1 + ε))⁻¹ ≤ 1 + 1 / ε := by
  apply Real.tsum_le_of_sum_range_le (fun _ => by positivity)
  intro n
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (by omega : n ≤ n + 2)) fun _ _ _ => by positivity)
    (sum_range_rpow_le ε hε n)

private def muAbs (n : ℕ) : ℝ := if n = 0 then 0 else 1

private theorem norm_moebius_le_muAbs (n : ℕ) :
    ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ muAbs n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [muAbs]
  · rw [muAbs, if_neg hn, Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one

private theorem muAbs_mul_exp_le (u c η : ℝ) (hη : 0 < η) (hc : c = 1 + η) (n : ℕ) :
    muAbs n * Real.exp (c * Ln u n) ≤ Real.exp (c * Real.log u) * ((n : ℝ) ^ (1 + η))⁻¹ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [muAbs, if_pos rfl, zero_mul, Nat.cast_zero, Real.zero_rpow (by linarith),
      inv_zero, mul_zero]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [muAbs, if_neg hn.ne', one_mul]
    have h2 : Real.exp (c * Ln u n) = Real.exp (c * Real.log u) * ((n : ℝ) ^ (1 + η))⁻¹ := by
      rw [← Real.rpow_neg hn'.le, Real.rpow_def_of_pos hn', ← Real.exp_add]
      congr 1; unfold Ln; rw [hc]; ring
    exact h2.le

private theorem summable_muA (u c η : ℝ) (hη : 0 < η) (hc : c = 1 + η) :
    Summable fun n : ℕ => muAbs n * Real.exp (c * Ln u n) :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (by unfold muAbs; split_ifs <;> norm_num) (Real.exp_pos _).le)
    (muAbs_mul_exp_le u c η hη hc)
    ((Real.summable_nat_rpow_inv.mpr (by linarith)).mul_left _)

private theorem tsum_muA_le (u c η : ℝ) (hη : 0 < η) (hc : c = 1 + η) :
    ∑' n : ℕ, muAbs n * Real.exp (c * Ln u n) ≤ Real.exp (c * Real.log u) * (1 + 1 / η) := by
  have hs : Summable fun n : ℕ => ((n : ℝ) ^ (1 + η))⁻¹ :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  calc ∑' n : ℕ, muAbs n * Real.exp (c * Ln u n)
      ≤ ∑' n : ℕ, Real.exp (c * Real.log u) * ((n : ℝ) ^ (1 + η))⁻¹ :=
        Summable.tsum_le_tsum (muAbs_mul_exp_le u c η hη hc) (summable_muA u c η hη hc)
          (hs.mul_left _)
    _ = Real.exp (c * Real.log u) * ∑' n : ℕ, ((n : ℝ) ^ (1 + η))⁻¹ := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (tsum_rpow_le η hη) (Real.exp_pos _).le

private def moebiusPerronIntegrand (u : ℝ) (s : ℂ) : ℂ :=
  invZeta s * kf (Real.log u) s

private theorem moebius_term_mul_eq (u : ℝ) (s : ℂ) (n : ℕ) :
    LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) s n * kf (Real.log u) s =
      (ArithmeticFunction.moebius n : ℂ) * kf (Ln u n) s := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn]
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.natCast_log]
    unfold kf Ln
    have : s * ((Real.log u - Real.log n : ℝ) : ℂ)
        = s * (Real.log u : ℂ) - (Real.log n : ℂ) * s := by push_cast; ring
    rw [this, Complex.exp_sub]
    ring

private theorem hasSum_moebius_integrand (u : ℝ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ) * kf (Ln u n) s)
      (moebiusPerronIntegrand u s) := by
  have hs_ne1 : s ≠ 1 := by rintro rfl; simp at hs
  have h1 : HasSum (LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) s)
      (LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s) :=
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs).LSeriesHasSum
  have h2 := h1.mul_right (kf (Real.log u) s)
  have hprod := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at hprod
  have hinv : LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s = invZeta s := by
    rw [invZeta_eq_inv hs_ne1]
    exact eq_inv_of_mul_eq_one_right hprod
  rw [hinv] at h2
  exact h2.congr_fun fun n => (moebius_term_mul_eq u s n).symm

private theorem hasSum_moebius_kint (u c T : ℝ) (hc : 1 < c)
    (hsumm : Summable fun n : ℕ => muAbs n * Real.exp (c * Ln u n)) :
    HasSum (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ) * kint (Ln u n) c T)
      (∫ t in (-T)..T, moebiusPerronIntegrand u ((c : ℂ) + (t : ℂ) * I)) := by
  have hc0 : c ≠ 0 := by linarith
  have hb : ∀ (n : ℕ) (t : ℝ),
      ‖(ArithmeticFunction.moebius n : ℂ) * kf (Ln u n) ((c : ℂ) + (t : ℂ) * I)‖
        ≤ muAbs n * Real.exp (c * Ln u n) := by
    intro n t
    rw [norm_mul, norm_kf]
    have hre : ((c : ℂ) + (t : ℂ) * I).re = c := by simp
    rw [hre]
    have hle : 1 ≤ ‖(c : ℂ) + (t : ℂ) * I‖ := by
      have := Complex.abs_re_le_norm ((c : ℂ) + (t : ℂ) * I)
      rw [hre, abs_of_pos (by linarith)] at this
      linarith
    exact mul_le_mul (norm_moebius_le_muAbs n)
      (div_le_self (Real.exp_pos _).le hle) (by positivity)
      (by unfold muAbs; split_ifs <;> norm_num)
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := -T) (b := T)
    (F := fun (n : ℕ) (t : ℝ) =>
      (ArithmeticFunction.moebius n : ℂ) * kf (Ln u n) ((c : ℂ) + (t : ℂ) * I))
    (f := fun t : ℝ => moebiusPerronIntegrand u ((c : ℂ) + (t : ℂ) * I))
    (fun (n : ℕ) (_ : ℝ) => muAbs n * Real.exp (c * Ln u n))
    (fun _ => (continuous_const.mul (cont_kf_vert _ c hc0)).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun t _ => hb n t)
    (Filter.Eventually.of_forall fun _ _ => hsumm)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun _ _ => hasSum_moebius_integrand u (by simpa using hc))
  exact key.congr_fun fun n => (intervalIntegral.integral_const_mul _ _).symm

private def muAterm (u c : ℝ) (n : ℕ) : ℝ := muAbs n * Real.exp (c * Ln u n)

private def muB1 (u T : ℝ) (N n : ℕ) : ℝ :=
  if 1 ≤ n ∧ n < N then (Real.exp 1 * u / T) / ((N : ℝ) - n) else 0

private def muB2 (u T : ℝ) (N n : ℕ) : ℝ :=
  if N + 2 ≤ n ∧ n < 2 * N + 2 then (2 * u / T) / ((n : ℝ) - N - 1) else 0

private def muB3 (N n : ℕ) : ℝ :=
  if n = N ∨ n = N + 1 then 11 else 0

private def muErrTerm (u c T : ℝ) (N n : ℕ) : ℂ :=
  (ArithmeticFunction.moebius n : ℂ) *
    ((if n ≤ N then (1 : ℂ) else 0) - kint (Ln u n) c T / (2 * π))

private def muBnd (u c T : ℝ) (N n : ℕ) : ℝ :=
  (2 / T) * muAterm u c n + muB1 u T N n + muB2 u T N n + muB3 N n

private theorem two_pi_ne : (2 * (π : ℂ)) ≠ 0 :=
  mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

private theorem norm_two_pi : ‖(2 * (π : ℂ))‖ = 2 * π := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_two]

private theorem norm_one_sub_div (K : ℂ) : ‖(1 : ℂ) - K / (2 * π)‖ = ‖K - 2 * π‖ / (2 * π) := by
  have e : (1 : ℂ) - K / (2 * π) = -((K - 2 * π) / (2 * π)) := by
    rw [← neg_div, neg_sub, sub_div, div_self two_pi_ne]
  rw [e, norm_neg, norm_div, norm_two_pi]

private theorem muErr_le_bnd (u c T : ℝ) (N : ℕ) (hu : 2 ≤ u) (hT : 2 ≤ T) (hc1 : 1 < c)
    (hc3 : c ≤ 3) (hcu : c * Real.log u = Real.log u + 1) (hNu : (N : ℝ) ≤ u)
    (huN : u < N + 1) (n : ℕ) :
    ‖muErrTerm u c T N n‖ ≤ muBnd u c T N n := by
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hN2 : 2 ≤ N := by
    have h1 : (1 : ℝ) < N := by linarith
    have h2 : 1 < N := by exact_mod_cast h1
    omega
  have hA0 : 0 ≤ muAterm u c n :=
    mul_nonneg (by unfold muAbs; split_ifs <;> norm_num) (Real.exp_pos _).le
  have hA2 : 0 ≤ (2 / T) * muAterm u c n := mul_nonneg (by positivity) hA0
  unfold muBnd muB1 muB2 muB3
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have cN : (0 : ℕ) ≠ N := by omega
    simp [muErrTerm, cN]
    linarith
  have hmu_le1 : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    simpa [muAbs, hn.ne'] using norm_moebius_le_muAbs n
  have hmuAbs_eq : muAbs n = 1 := if_neg hn.ne'
  rcases lt_trichotomy n N with h | rfl | h
  · -- `1 ≤ n < N`
    have c1 : 1 ≤ n ∧ n < N := ⟨hn, h⟩
    have c2 : ¬(N + 2 ≤ n ∧ n < 2 * N + 2) := by omega
    have c3 : ¬(n = N ∨ n = N + 1) := by omega
    rw [if_pos c1, if_neg c2, if_neg c3]
    unfold muErrTerm
    rw [if_pos h.le, norm_mul, norm_one_sub_div]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnNR : (n : ℝ) + 1 ≤ N := by exact_mod_cast h
    have hn0 : (0 : ℝ) < n := by linarith
    have hN0 : (0 : ℝ) < N := by linarith
    have hd : 0 < (N : ℝ) - n := by linarith
    have hLlow : ((N : ℝ) - n) / N ≤ Ln u n := by
      have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hN0 hn0)
      have h2 := Real.log_div hN0.ne' hn0.ne'
      have h3 := Real.log_le_log hN0 hNu
      have h4 : 1 - ((N : ℝ) / n)⁻¹ = ((N : ℝ) - n) / N := by field_simp
      unfold Ln; linarith
    have hLpos : 0 < Ln u n := lt_of_lt_of_le (div_pos hd hN0) hLlow
    have hK := kint_bound_pos (L := Ln u n) (c := c) (T := T) hLpos (by linarith) hT0
    have hpi : (2 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
    have key1 : ‖kint (Ln u n) c T - 2 * π‖ / (2 * π) ≤ Real.exp (c * Ln u n) / (T * Ln u n) := by
      calc ‖kint (Ln u n) c T - 2 * π‖ / (2 * π) ≤ ‖kint (Ln u n) c T - 2 * π‖ / 2 :=
            div_le_div_of_nonneg_left (norm_nonneg _) two_pos hpi
        _ ≤ (2 * Real.exp (c * Ln u n) / (T * Ln u n)) / 2 :=
            div_le_div_of_nonneg_right hK two_pos.le
        _ = Real.exp (c * Ln u n) / (T * Ln u n) := by ring
    have key2 : Real.exp (c * Ln u n) / (T * Ln u n)
        ≤ Real.exp (c * Ln u n) / (T * (((N : ℝ) - n) / N)) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
        (mul_le_mul_of_nonneg_left hLlow hT0.le)
    have key3 : Real.exp (c * Ln u n) / (T * (((N : ℝ) - n) / N))
        = (1 / T) * Real.exp (c * Ln u n) + (Real.exp (c * Ln u n) * n) / T / ((N : ℝ) - n) := by
      have hdne : (N : ℝ) - n ≠ 0 := hd.ne'; field_simp; ring
    have key4 : Real.exp (c * Ln u n) * n ≤ Real.exp 1 * u := by
      have h1 : Real.exp (c * Ln u n) * n = Real.exp (c * Ln u n + Real.log n) := by
        rw [Real.exp_add, Real.exp_log hn0]
      have h2 : c * Ln u n + Real.log n ≤ Real.log u + 1 := by
        unfold Ln; nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ c - 1) (Real.log_nonneg hnR)]
      have h3 : Real.exp (Real.log u + 1) = Real.exp 1 * u := by
        rw [Real.exp_add, Real.exp_log hu0, mul_comm]
      rw [h1, ← h3]; exact Real.exp_le_exp.mpr h2
    have hterm2 : (Real.exp (c * Ln u n) * n) / T / ((N : ℝ) - n)
        ≤ (Real.exp 1 * u / T) / ((N : ℝ) - n) :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right key4 hT0.le) hd.le
    have hterm1 : (1 / T) * Real.exp (c * Ln u n) ≤ (2 / T) * muAterm u c n := by
      unfold muAterm; rw [hmuAbs_eq, one_mul]
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by norm_num) hT0.le)
        (Real.exp_pos _).le
    have hprod_le : ‖(ArithmeticFunction.moebius n : ℂ)‖ *
        (‖kint (Ln u n) c T - 2 * π‖ / (2 * π)) ≤
        1 * (‖kint (Ln u n) c T - 2 * π‖ / (2 * π)) :=
      mul_le_mul_of_nonneg_right hmu_le1 (by positivity)
    linarith [key1.trans (key2.trans_eq key3)]
  · -- `n = N`
    have c1 : ¬(1 ≤ n ∧ n < n) := by omega
    have c2 : ¬(n + 2 ≤ n ∧ n < 2 * n + 2) := by omega
    have c3 : n = n ∨ n = n + 1 := Or.inl rfl
    rw [if_neg c1, if_neg c2, if_pos c3]
    unfold muErrTerm
    rw [if_pos le_rfl, norm_mul, norm_one_sub_div]
    have hN0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hL0 : 0 ≤ Ln u n := by unfold Ln; linarith [Real.log_le_log hN0 hNu]
    have hL1 : Ln u n ≤ 1 / 2 := by
      have h1 := Real.log_le_sub_one_of_pos (div_pos hu0 hN0)
      have h2 := Real.log_div hu0.ne' hN0.ne'
      have h3 : u / n - 1 ≤ 1 / 2 := by
        rw [div_sub_one hN0.ne', div_le_iff₀ hN0]
        have hN2R : (2 : ℝ) ≤ n := by exact_mod_cast hN2
        linarith
      unfold Ln; linarith
    have hK := kint_bound_nonneg (L := Ln u n) (c := c) (T := T) hL0 (by linarith) hT0
    have hE : Real.exp (c * Ln u n) ≤ 9 := by
      have h0 : c * Ln u n ≤ 3 * (1 / 2) := mul_le_mul hc3 hL1 hL0 (by norm_num)
      have h1 : c * Ln u n ≤ 1 + 1 := by linarith
      have h4 : Real.exp (c * Ln u n) ≤ Real.exp (1 + 1) := Real.exp_le_exp.mpr h1
      rw [Real.exp_add] at h4
      nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
    have hcoef : 4 + 2 * c / T ≤ 7 := by
      have : 2 * c / T ≤ 3 := by rw [div_le_iff₀ hT0]; nlinarith
      linarith
    have hKb : ‖kint (Ln u n) c T - 2 * π‖ ≤ 63 :=
      hK.trans ((mul_le_mul hcoef hE (Real.exp_pos _).le (by norm_num)).trans_eq (by norm_num))
    have hdiv : ‖kint (Ln u n) c T - 2 * π‖ / (2 * π) ≤ 11 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_three]
    have hprod_le := mul_le_mul hmu_le1 hdiv (by positivity) zero_le_one
    linarith
  · rcases Nat.lt_or_ge n (N + 2) with h2 | h2
    · -- `n = N + 1`
      have hn' : n = N + 1 := by omega
      have c1 : ¬(1 ≤ n ∧ n < N) := by omega
      have c2 : ¬(N + 2 ≤ n ∧ n < 2 * N + 2) := by omega
      have c3 : n = N ∨ n = N + 1 := Or.inr hn'
      rw [if_neg c1, if_neg c2, if_pos c3]
      unfold muErrTerm
      rw [if_neg (not_le.mpr h), zero_sub, norm_mul, norm_neg, norm_div, norm_two_pi]
      have hL : Ln u n ≤ 0 := by
        rw [hn']; unfold Ln; push_cast; linarith [Real.log_le_log hu0 huN.le]
      have hK := kint_bound_nonpos (L := Ln u n) (c := c) (T := T) hL (by linarith) hT0
      have hE : Real.exp (c * Ln u n) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos (by linarith) hL)
      have hdiv : ‖kint (Ln u n) c T‖ / (2 * π) ≤ 11 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_three]
      have hprod_le := mul_le_mul hmu_le1 hdiv (by positivity) zero_le_one
      linarith
    · -- `n ≥ N + 2`
      unfold muErrTerm
      rw [if_neg (not_le.mpr h), zero_sub, norm_mul, norm_neg, norm_div, norm_two_pi]
      have hnR : (N : ℝ) + 2 ≤ n := by exact_mod_cast h2
      have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      have hn0 : (0 : ℝ) < n := by linarith
      have hm : 0 < (n : ℝ) - N - 1 := by linarith
      have hLlow : ((n : ℝ) - N - 1) / n ≤ -Ln u n := by
        have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hn0 hN1)
        have h2 := Real.log_div hn0.ne' hN1.ne'
        have h3 := Real.log_le_log hu0 huN.le
        have h4 : 1 - ((n : ℝ) / ((N : ℝ) + 1))⁻¹ = ((n : ℝ) - N - 1) / n := by field_simp; ring
        unfold Ln; linarith
      have hLneg : Ln u n < 0 := by linarith [div_pos hm hn0]
      have hK := kint_bound_neg (L := Ln u n) (c := c) (T := T) hLneg (by linarith) hT0
      have hpi : (2 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
      have key1 : ‖kint (Ln u n) c T‖ / (2 * π) ≤ Real.exp (c * Ln u n) / (T * (-Ln u n)) := by
        calc ‖kint (Ln u n) c T‖ / (2 * π) ≤ ‖kint (Ln u n) c T‖ / 2 :=
              div_le_div_of_nonneg_left (norm_nonneg _) two_pos hpi
          _ ≤ (2 * Real.exp (c * Ln u n) / (T * (-Ln u n))) / 2 :=
              div_le_div_of_nonneg_right hK two_pos.le
          _ = Real.exp (c * Ln u n) / (T * (-Ln u n)) := by ring
      have key2 : Real.exp (c * Ln u n) / (T * (-Ln u n))
          ≤ Real.exp (c * Ln u n) / (T * (((n : ℝ) - N - 1) / n)) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
          (mul_le_mul_of_nonneg_left hLlow hT0.le)
      have key3 : Real.exp (c * Ln u n) / (T * (((n : ℝ) - N - 1) / n))
          = (1 / T) * Real.exp (c * Ln u n)
            + (1 / T) * (Real.exp (c * Ln u n) * ((N : ℝ) + 1)) / ((n : ℝ) - N - 1) := by
        have hmne : (n : ℝ) - N - 1 ≠ 0 := hm.ne'; field_simp; ring
      have hA_eq : muAterm u c n = Real.exp (c * Ln u n) := by
        unfold muAterm; rw [hmuAbs_eq, one_mul]
      have hprod_le : ‖(ArithmeticFunction.moebius n : ℂ)‖ *
          (‖kint (Ln u n) c T‖ / (2 * π)) ≤
          1 * (‖kint (Ln u n) c T‖ / (2 * π)) :=
        mul_le_mul_of_nonneg_right hmu_le1 (by positivity)
      rcases Nat.lt_or_ge n (2 * N + 2) with h3 | h3
      · have c1 : ¬(1 ≤ n ∧ n < N) := by omega
        have c2 : N + 2 ≤ n ∧ n < 2 * N + 2 := ⟨h2, h3⟩
        have c3 : ¬(n = N ∨ n = N + 1) := by omega
        rw [if_neg c1, if_pos c2, if_neg c3]
        have hE1 : Real.exp (c * Ln u n) ≤ 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos (by linarith) hLneg.le)
        have hN1_le : (N : ℝ) + 1 ≤ 2 * u := by linarith
        have hprod2 : Real.exp (c * Ln u n) * ((N : ℝ) + 1) ≤ 2 * u := by
          calc Real.exp (c * Ln u n) * ((N : ℝ) + 1) ≤ 1 * (2 * u) :=
                mul_le_mul hE1 hN1_le (by positivity) zero_le_one
            _ = 2 * u := one_mul _
        have hfin : (1 / T) * (Real.exp (c * Ln u n) * ((N : ℝ) + 1)) / ((n : ℝ) - N - 1)
            ≤ (2 * u / T) / ((n : ℝ) - N - 1) := by
          apply div_le_div_of_nonneg_right _ hm.le
          rw [one_div_mul_eq_div]
          exact div_le_div_of_nonneg_right hprod2 hT0.le
        have h6 : (1 / T) * Real.exp (c * Ln u n) ≤ (2 / T) * muAterm u c n := by
          rw [hA_eq]
          exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by norm_num) hT0.le)
            (Real.exp_pos _).le
        linarith [key1.trans (key2.trans_eq key3)]
      · have c1 : ¬(1 ≤ n ∧ n < N) := by omega
        have c2 : ¬(N + 2 ≤ n ∧ n < 2 * N + 2) := by omega
        have c3 : ¬(n = N ∨ n = N + 1) := by omega
        rw [if_neg c1, if_neg c2, if_neg c3]
        have h4 : 2 * (N : ℝ) + 2 ≤ n := by exact_mod_cast h3
        have hfin : (1 / T) * (Real.exp (c * Ln u n) * ((N : ℝ) + 1)) / ((n : ℝ) - N - 1)
            ≤ (1 / T) * Real.exp (c * Ln u n) := by
          rw [div_le_iff₀ hm]
          have h5 : Real.exp (c * Ln u n) * ((N : ℝ) + 1) ≤
              Real.exp (c * Ln u n) * ((n : ℝ) - N - 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
          calc (1 / T) * (Real.exp (c * Ln u n) * ((N : ℝ) + 1))
              ≤ (1 / T) * (Real.exp (c * Ln u n) * ((n : ℝ) - N - 1)) :=
                mul_le_mul_of_nonneg_left h5 (by positivity)
            _ = (1 / T) * Real.exp (c * Ln u n) * ((n : ℝ) - N - 1) := by ring
        rw [hA_eq]
        have h8 : (2 / T) * Real.exp (c * Ln u n) =
            (1 / T) * Real.exp (c * Ln u n) + (1 / T) * Real.exp (c * Ln u n) := by ring
        linarith [key1.trans (key2.trans_eq key3)]

private theorem sum_range_inv_le (N : ℕ) :
    ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  have e : ((harmonic N : ℚ) : ℝ) = ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) := by
    unfold harmonic; push_cast; simp [one_div]
  rwa [e] at h

private theorem sum_Ico_reflect_le (N : ℕ) :
    ∑ n ∈ Finset.Ico 1 N, 1 / ((N : ℝ) - n) ≤ 1 + Real.log N := by
  have e : ∀ n ∈ Finset.Ico 1 N, 1 / ((N : ℝ) - n) = (fun j : ℕ => 1 / (j : ℝ)) (N - n) := by
    intro n hn; simp only; rw [Nat.cast_sub (Finset.mem_Ico.mp hn).2.le]
  rw [Finset.sum_congr rfl e, Finset.sum_Ico_reflect (fun j : ℕ => 1 / (j : ℝ)) 1 (Nat.le_succ N)]
  have e1 : N + 1 - N = 1 := by omega
  have e2 : N + 1 - 1 = N := by omega
  rw [e1, e2, Finset.sum_Ico_eq_sum_range]
  have e3 : ∀ k ∈ Finset.range (N - 1), 1 / (((1 + k : ℕ)) : ℝ) = 1 / ((k : ℝ) + 1) := by
    intro k _; push_cast; ring
  rw [Finset.sum_congr rfl e3]
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le N 1))
    fun _ _ _ => by positivity) (sum_range_inv_le N)

private theorem sum_Ico_shift_le (N : ℕ) :
    ∑ n ∈ Finset.Ico (N + 2) (2 * N + 2), 1 / ((n : ℝ) - N - 1) ≤ 1 + Real.log N := by
  rw [Finset.sum_Ico_eq_sum_range]
  have e1 : 2 * N + 2 - (N + 2) = N := by omega
  rw [e1]
  have e3 : ∀ k ∈ Finset.range N, 1 / ((((N + 2 + k : ℕ)) : ℝ) - N - 1) = 1 / ((k : ℝ) + 1) := by
    intro k _; congr 1; push_cast; ring
  rw [Finset.sum_congr rfl e3]
  exact sum_range_inv_le N

private theorem hasSum_mertens (N : ℕ) :
    HasSum (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ) * (if n ≤ N then (1 : ℂ) else 0))
      ((∑ d ∈ Finset.range (N + 1), (ArithmeticFunction.moebius d : ℝ) : ℝ) : ℂ) := by
  have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (f := fun n : ℕ => (ArithmeticFunction.moebius n : ℂ) * (if n ≤ N then (1 : ℂ) else 0))
    (s := Finset.range (N + 1))
    fun n hn => by
      have hnot : ¬ n ≤ N := fun hle => hn (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
      rw [if_neg hnot, mul_zero]
  have e : ∑ n ∈ Finset.range (N + 1),
      (ArithmeticFunction.moebius n : ℂ) * (if n ≤ N then (1 : ℂ) else 0) =
      ((∑ d ∈ Finset.range (N + 1), (ArithmeticFunction.moebius d : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)), mul_one]
    push_cast; rfl
  rwa [e] at h

/-- **Truncated Perron Formula for `M(N)` at `u = T = (N : ℝ)` (`N ≥ 2`):**
`‖M(N) - (1 / 2π) ∫_{-N}^N invZeta(c + it) * kf(log N)(c + it) dt‖ ≤ 50 * Real.log N + 50`. -/
private theorem moebius_perron_bound {N : ℕ} (hN2 : 2 ≤ N) :
    let u : ℝ := (N : ℝ)
    let c : ℝ := 1 + 1 / Real.log u
    ‖((∑ d ∈ Finset.range (N + 1), (ArithmeticFunction.moebius d : ℝ) : ℝ) : ℂ) -
        (1 / (2 * (π : ℂ))) *
          ∫ t in (-u)..u, moebiusPerronIntegrand u ((c : ℂ) + (t : ℂ) * I)‖
      ≤ 50 * Real.log u + 50 := by
  intro u c
  have hu : 2 ≤ u := by dsimp [u]; exact_mod_cast hN2
  have hu0 : 0 < u := by linarith
  have hl : 1 / 2 < Real.log u := by
    have h1 := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log u := Real.log_le_log two_pos hu
    linarith
  have hl0 : 0 < Real.log u := by linarith
  have hc1 : 1 < c := by dsimp [c]; linarith [show 0 < 1 / Real.log u by positivity]
  have hc3 : c ≤ 3 := by
    dsimp [c]
    have : 1 / Real.log u ≤ 2 := by rw [div_le_iff₀ hl0]; linarith
    linarith
  have hcu : c * Real.log u = Real.log u + 1 := by dsimp [c]; field_simp
  have hη : 0 < 1 / Real.log u := by positivity
  have hA := summable_muA u c (1 / Real.log u) hη rfl
  have h2 := hasSum_moebius_kint u c u hc1 hA
  have herr : HasSum (fun n => muErrTerm u c u N n)
      (((∑ d ∈ Finset.range (N + 1), (ArithmeticFunction.moebius d : ℝ) : ℝ) : ℂ) -
        (1 / (2 * (π : ℂ))) *
          ∫ t in (-u)..u, moebiusPerronIntegrand u ((c : ℂ) + (t : ℂ) * I)) := by
    have h3 := (hasSum_mertens N).sub (h2.mul_left (1 / (2 * (π : ℂ))))
    exact h3.congr_fun fun n => by unfold muErrTerm; ring
  have hB1' : HasSum (fun n => muB1 u u N n)
      ((Real.exp 1 * u / u) * ∑ n ∈ Finset.Ico 1 N, 1 / ((N : ℝ) - n)) := by
    have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
      (f := fun n => muB1 u u N n) (s := Finset.Ico 1 N)
      fun n hn => if_neg fun hh => hn (Finset.mem_Ico.mpr hh)
    have e : ∑ n ∈ Finset.Ico 1 N, muB1 u u N n =
        (Real.exp 1 * u / u) * ∑ n ∈ Finset.Ico 1 N, 1 / ((N : ℝ) - n) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      unfold muB1; rw [if_pos (Finset.mem_Ico.mp hn)]; ring
    rwa [e] at h
  have hB2' : HasSum (fun n => muB2 u u N n)
      ((2 * u / u) * ∑ n ∈ Finset.Ico (N + 2) (2 * N + 2), 1 / ((n : ℝ) - N - 1)) := by
    have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
      (f := fun n => muB2 u u N n) (s := Finset.Ico (N + 2) (2 * N + 2))
      fun n hn => if_neg fun hh => hn (Finset.mem_Ico.mpr hh)
    have e : ∑ n ∈ Finset.Ico (N + 2) (2 * N + 2), muB2 u u N n =
        (2 * u / u) * ∑ n ∈ Finset.Ico (N + 2) (2 * N + 2), 1 / ((n : ℝ) - N - 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      unfold muB2; rw [if_pos (Finset.mem_Ico.mp hn)]; ring
    rwa [e] at h
  have hB3' : HasSum (fun n => muB3 N n) (11 + 11) := by
    have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
      (f := fun n => muB3 N n) (s := {N, N + 1})
      fun n hn => if_neg fun hh => hn (by
        rcases hh with rfl | rfl
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have e : ∑ n ∈ ({N, N + 1} : Finset ℕ), muB3 N n = 11 + 11 := by
      rw [Finset.sum_pair (by omega)]; unfold muB3
      rw [if_pos (Or.inl rfl), if_pos (Or.inr rfl)]
    rwa [e] at h
  have hb : HasSum (fun n => muBnd u c u N n)
      ((2 / u) * ∑' n, muAterm u c n
        + (Real.exp 1 * u / u) * ∑ n ∈ Finset.Ico 1 N, 1 / ((N : ℝ) - n)
        + (2 * u / u) * ∑ n ∈ Finset.Ico (N + 2) (2 * N + 2), 1 / ((n : ℝ) - N - 1)
        + (11 + 11)) :=
    ((((hA.hasSum.mul_left (2 / u)).add hB1').add hB2').add hB3')
  have hnorm := herr.norm_le_of_bounded hb
    (muErr_le_bnd u c u N hu hu hc1 hc3 hcu le_rfl (by dsimp [u]; linarith))
  refine hnorm.trans ?_
  have he3 : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have hSA : (2 / u) * ∑' n, muAterm u c n ≤ 6 * (1 + Real.log u) := by
    have h1 := tsum_muA_le u c (1 / Real.log u) hη rfl
    have h2 : Real.exp (c * Real.log u) * (1 + 1 / (1 / Real.log u)) =
        u * Real.exp 1 * (1 + Real.log u) := by
      rw [hcu, Real.exp_add, Real.exp_log hu0]; field_simp
    change (2 / u) * ∑' n, muAbs n * Real.exp (c * Ln u n) ≤ _
    rw [h2] at h1
    have h3 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 / u by positivity)
    have h4 : (2 / u) * (u * Real.exp 1 * (1 + Real.log u)) =
        2 * Real.exp 1 * (1 + Real.log u) := by field_simp
    rw [h4] at h3
    nlinarith
  have hs1 : ∑ n ∈ Finset.Ico 1 N, 1 / ((N : ℝ) - n) ≤ 1 + Real.log u := sum_Ico_reflect_le N
  have hs2 : ∑ n ∈ Finset.Ico (N + 2) (2 * N + 2), 1 / ((n : ℝ) - N - 1) ≤ 1 + Real.log u :=
    sum_Ico_shift_le N
  have hp1 : (Real.exp 1 * u / u) * ∑ n ∈ Finset.Ico 1 N, 1 / ((N : ℝ) - n)
      ≤ 3 * (1 + Real.log u) := by
    rw [mul_div_cancel_right₀ _ hu0.ne']
    nlinarith [Finset.sum_nonneg fun (n : ℕ) (hn : n ∈ Finset.Ico 1 N) =>
      show (0 : ℝ) ≤ 1 / ((N : ℝ) - n) by
        have : (n : ℝ) < N := by exact_mod_cast (Finset.mem_Ico.mp hn).2
        positivity]
  have hp2 : (2 * u / u) * ∑ n ∈ Finset.Ico (N + 2) (2 * N + 2), 1 / ((n : ℝ) - N - 1)
      ≤ 2 * (1 + Real.log u) := by
    rw [mul_div_cancel_right₀ _ hu0.ne']
    linarith
  linarith

/-! ### 5. Contour Shift and Final Proof of `prefixExponent_of_zeroFree` -/

private theorem integral_inv_one_add_abs (u : ℝ) (hu : 0 ≤ u) :
    (∫ t in (-u)..u, 4 / (1 + |t|)) = 8 * Real.log (1 + u) := by
  have hcont : Continuous fun t : ℝ => 4 / (1 + |t|) :=
    continuous_const.div (continuous_const.add continuous_abs) fun t => by positivity
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (-u) 0) (hcont.intervalIntegrable 0 u)]
  have hpos : (∫ t in (0 : ℝ)..u, 4 / (1 + |t|)) = 4 * Real.log (1 + u) := by
    have hcongr : EqOn (fun t : ℝ => 4 / (1 + |t|)) (fun t : ℝ => 4 * (1 + t)⁻¹) (uIcc 0 u) := by
      rw [uIcc_of_le hu]
      intro t ht
      dsimp only
      rw [abs_of_nonneg ht.1, div_eq_mul_inv]
    rw [intervalIntegral.integral_congr hcongr]
    have hder : ∀ t ∈ uIcc 0 u,
        HasDerivAt (fun x : ℝ => 4 * Real.log (1 + x)) (4 * (1 + t)⁻¹) t := by
      rw [uIcc_of_le hu]
      intro t ht
      have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 t := (hasDerivAt_id t).const_add 1
      have h2 := (h1.log (by linarith [ht.1])).const_mul 4
      simpa [div_eq_mul_inv] using h2
    have hint : IntervalIntegrable (fun t : ℝ => 4 * (1 + t)⁻¹) volume 0 u := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hu]
      have hne : ∀ t ∈ Icc 0 u, 1 + t ≠ 0 := fun t ht => by linarith [ht.1]
      fun_prop (disch := assumption)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint]
    simp
  have hneg : (∫ t in (-u)..(0 : ℝ), 4 / (1 + |t|)) = 4 * Real.log (1 + u) := by
    have hcongr : EqOn (fun t : ℝ => 4 / (1 + |t|)) (fun t : ℝ => 4 * (1 - t)⁻¹) (uIcc (-u) 0) := by
      rw [uIcc_of_le (by linarith)]
      intro t ht
      dsimp only
      rw [abs_of_nonpos ht.2, sub_eq_add_neg, div_eq_mul_inv]
    rw [intervalIntegral.integral_congr hcongr]
    have hder : ∀ t ∈ uIcc (-u) 0,
        HasDerivAt (fun x : ℝ => -(4 * Real.log (1 - x))) (4 * (1 - t)⁻¹) t := by
      rw [uIcc_of_le (by linarith)]
      intro t ht
      have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) t :=
        (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).congr_of_eventuallyEq
          (Eventually.of_forall fun _ => rfl)).congr_deriv (by ring)
      have h2 := ((h1.log (by linarith [ht.2])).const_mul 4).neg
      refine h2.congr_deriv ?_
      have h1t_ne : 1 - t ≠ 0 := by linarith [ht.2]
      field_simp [h1t_ne]
    have hint : IntervalIntegrable (fun t : ℝ => 4 * (1 - t)⁻¹) volume (-u) 0 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le (by linarith)]
      have hne : ∀ t ∈ Icc (-u) 0, 1 - t ≠ 0 := fun t ht => by linarith [ht.2]
      fun_prop (disch := assumption)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint]
    simp [sub_neg_eq_add]
  rw [hneg, hpos]; ring

end ZetaMertens

namespace HalvingMertens

/-- **Littlewood's Classical Zero-Free Half-Plane to Mertens Theorem:**
A zero-free half-plane `{Re s > θ}` (`1 / 2 ≤ θ ≤ 1`) for `riemannZeta` implies
`PrefixExponent θ` (`M(N) = O_ε((N + 1)^{θ + ε})`). -/
theorem prefixExponent_of_zeroFree {θ : ℝ} (half : 1 / 2 ≤ θ) (one : θ ≤ 1)
    (hz : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) :
    PrefixExponent θ := by
  have _hone : θ - 1 ≤ 0 := sub_nonpos.mpr one
  intro ε hε
  -- Trivial bound `|M(N)| ≤ N + 1` for all `N`
  have htriv : ∀ N : ℕ,
      |∑ d ∈ Finset.range (N + 1), (ArithmeticFunction.moebius d : ℝ)| ≤ (N : ℝ) + 1 := by
    intro N
    calc |∑ d ∈ Finset.range (N + 1), (ArithmeticFunction.moebius d : ℝ)|
        ≤ ∑ d ∈ Finset.range (N + 1), |(ArithmeticFunction.moebius d : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ Finset.range (N + 1), (1 : ℝ) := by
          refine Finset.sum_le_sum fun d _ => ?_
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      _ = (N : ℝ) + 1 := by simp
  -- Case 1: `1 ≤ θ + ε`
  rcases le_or_gt 1 (θ + ε) with hge1 | hlt1
  · refine ⟨1, zero_le_one, fun N => ?_⟩
    have hN1 : 1 ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
    calc |∑ d ∈ Finset.range (N + 1), (ArithmeticFunction.moebius d : ℝ)|
        ≤ (N : ℝ) + 1 := htriv N
      _ = ((N : ℝ) + 1) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ 1 * ((N : ℝ) + 1) ^ (θ + ε) := by
          rw [one_mul]; exact Real.rpow_le_rpow_of_exponent_le hN1 hge1
  -- Case 2: `θ + ε < 1`
  · open ZetaMertens in
    let δ : ℝ := ε / 4
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have hθ4_eq : θ + 4 * δ = θ + ε := by dsimp [δ]; ring
    have hθ4 : θ + 4 * δ < 1 := hθ4_eq.trans_lt hlt1
    obtain ⟨K_inv, hK_inv_pos, hK_inv⟩ := exists_invZeta_subpower_bound half hδ hθ4 hz
    let σ₁ : ℝ := θ + 2 * δ
    have hσ₁_gt_θ : θ < σ₁ := by dsimp [σ₁]; linarith
    have hσ₁_ge_half : 1 / 2 ≤ σ₁ := by linarith
    -- Explicit uniform constant for `N ≥ 4`
    let C_big : ℝ := 500 + 24 * K_inv + 32 * K_inv / δ
    have hC_big0 : 0 ≤ C_big := by dsimp [C_big]; positivity
    refine ⟨max 4 C_big, le_trans (by norm_num) (le_max_left _ _), fun N => ?_⟩
    have hN1_ge1 : 1 ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
    have hpow_ge1 : 1 ≤ ((N : ℝ) + 1) ^ (θ + ε) :=
      Real.one_le_rpow hN1_ge1 (by linarith)
    rcases lt_or_ge N 4 with hN4 | hN4
    · -- Small `N < 4`: `|M(N)| ≤ 4 ≤ max 4 C_big * (N + 1)^(θ + ε)`
      have hN_le3 : (N : ℝ) ≤ 3 := by exact_mod_cast (by omega : N ≤ 3)
      calc |∑ d ∈ Finset.range (N + 1), (ArithmeticFunction.moebius d : ℝ)|
          ≤ (N : ℝ) + 1 := htriv N
        _ ≤ 4 := by linarith
        _ ≤ max 4 C_big * 1 := by rw [mul_one]; exact le_max_left _ _
        _ ≤ max 4 C_big * ((N : ℝ) + 1) ^ (θ + ε) :=
            mul_le_mul_of_nonneg_left hpow_ge1 (by positivity)
    · -- `N ≥ 4`: Perron formula + Cauchy rectangle shift `[σ₁, c] × [-u, u]` (`u = N`)
      set u : ℝ := (N : ℝ) with hu_def
      have hu4 : 4 ≤ u := by dsimp [u]; exact_mod_cast hN4
      have hu0 : 0 < u := by linarith
      have hu1 : 1 ≤ u := by linarith
      have hlog_u_gt1 : 1 < Real.log u := by
        have h4 : Real.log 4 ≤ Real.log u := Real.log_le_log (by norm_num) hu4
        have hl4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        linarith [Real.log_two_gt_d9]
      set c : ℝ := 1 + 1 / Real.log u with hc_def
      have hc_gt1 : 1 < c := by dsimp [c]; linarith [show 0 < 1 / Real.log u by positivity]
      have hc_le2 : c ≤ 2 := by
        dsimp [c]
        have : 1 / Real.log u ≤ 1 := div_le_one_of_le₀ hlog_u_gt1.le (by positivity)
        linarith
      have hσ₁_le_c : σ₁ ≤ c := by dsimp [σ₁]; linarith
      -- Perron approximation at `T = u`
      have hperron := moebius_perron_bound (N := N) (by omega : 2 ≤ N)
      -- Cauchy rectangle theorem on `[[σ₁, c]] ×ℂ [[-u, u]]`
      have hF_diff : DifferentiableOn ℂ (moebiusPerronIntegrand u)
          ([[σ₁, c]] ×ℂ [[-u, u]]) := by
        intro s hs_mem
        have hs_re : s.re ∈ [[σ₁, c]] := hs_mem.1
        rw [Set.uIcc_of_le hσ₁_le_c] at hs_re
        have hs_gt_θ : θ < s.re := hσ₁_gt_θ.trans_le hs_re.1
        have hs0 : s ≠ 0 := by
          intro hc0; rw [hc0] at hs_re; simp at hs_re; linarith [hs_re.1]
        unfold moebiusPerronIntegrand
        exact ((differentiableAt_invZeta_of_zeroFree hz hs_gt_θ).mul
          (differentiableAt_kf (Real.log u) hs0)).differentiableWithinAt
      have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
        (moebiusPerronIntegrand u) ⟨σ₁, -u⟩ ⟨c, u⟩ hF_diff
      have hshift_eq : I • (∫ t in (-u)..u, moebiusPerronIntegrand u ((c : ℂ) + (t : ℂ) * I)) =
          I • (∫ t in (-u)..u, moebiusPerronIntegrand u ((σ₁ : ℂ) + (t : ℂ) * I)) -
            (∫ σ in σ₁..c, moebiusPerronIntegrand u ((σ : ℂ) + ((-u : ℝ) : ℂ) * I)) +
            (∫ σ in σ₁..c, moebiusPerronIntegrand u ((σ : ℂ) + ((u : ℝ) : ℂ) * I)) := by
        linear_combination hrect
      -- Bound horizontal edges `h = ±u`
      have h_horiz : ∀ h : ℝ, |h| = u →
          ‖∫ σ in σ₁..c, moebiusPerronIntegrand u ((σ : ℂ) + (h : ℂ) * I)‖ ≤
            12 * K_inv * u ^ δ := by
        intro h hh_abs
        refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 6 * K_inv * u ^ δ)
          fun σ hσ => ?_).trans ?_
        · rw [uIoc_of_le hσ₁_le_c] at hσ
          have hσ_lo : θ + 2 * δ ≤ σ := hσ.1.le
          have hσ_hi : σ ≤ 2 := hσ.2.trans hc_le2
          unfold moebiusPerronIntegrand
          rw [norm_mul, norm_kf]
          have hre_s : ((σ : ℂ) + (h : ℂ) * I).re = σ := by simp
          have him_s : ((σ : ℂ) + (h : ℂ) * I).im = h := by simp
          rw [hre_s]
          have hinv_bd := hK_inv σ h hσ_lo hσ_hi
          rw [hh_abs] at hinv_bd
          have hu2_le : (u + 2) ^ δ ≤ 2 * u ^ δ := by
            calc (u + 2) ^ δ ≤ (2 * u) ^ δ :=
                  Real.rpow_le_rpow (by positivity) (by linarith) hδ.le
              _ = 2 ^ δ * u ^ δ := Real.mul_rpow (by norm_num) hu0.le
              _ ≤ 2 * u ^ δ := by
                  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                  simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
                    (by linarith : δ ≤ 1)
          have hexp_le : Real.exp (σ * Real.log u) ≤ 3 * u := by
            have h1 : σ * Real.log u ≤ c * Real.log u :=
              mul_le_mul_of_nonneg_right hσ.2 (by positivity)
            have h2 : c * Real.log u = Real.log u + 1 := by dsimp [c]; field_simp
            have h3 : Real.exp (Real.log u + 1) = u * Real.exp 1 := by
              rw [Real.exp_add, Real.exp_log hu0]
            calc Real.exp (σ * Real.log u)
                ≤ Real.exp (Real.log u + 1) := Real.exp_le_exp.mpr (h1.trans_eq h2)
              _ = u * Real.exp 1 := h3
              _ ≤ 3 * u := by nlinarith [Real.exp_one_lt_three]
          have hden_ge : u ≤ ‖(σ : ℂ) + (h : ℂ) * I‖ := by
            have := Complex.abs_im_le_norm ((σ : ℂ) + (h : ℂ) * I)
            rwa [him_s, hh_abs] at this
          have hkf_bd : Real.exp (σ * Real.log u) / ‖(σ : ℂ) + (h : ℂ) * I‖ ≤ 3 := by
            calc Real.exp (σ * Real.log u) / ‖(σ : ℂ) + (h : ℂ) * I‖
                ≤ (3 * u) / u := div_le_div₀ (by positivity) hexp_le hu0 hden_ge
              _ = 3 := mul_div_cancel_right₀ 3 hu0.ne'
          calc ‖invZeta ((σ : ℂ) + (h : ℂ) * I)‖ *
                (Real.exp (σ * Real.log u) / ‖(σ : ℂ) + (h : ℂ) * I‖)
              ≤ (K_inv * (2 * u ^ δ)) * 3 :=
                mul_le_mul (hinv_bd.trans (mul_le_mul_of_nonneg_left hu2_le hK_inv_pos.le))
                  hkf_bd (by positivity) (by positivity)
            _ = 6 * K_inv * u ^ δ := by ring
        · have hlen : |c - σ₁| ≤ 2 := by
            rw [abs_of_nonneg (by linarith)]
            linarith
          calc 6 * K_inv * u ^ δ * |c - σ₁|
              ≤ 6 * K_inv * u ^ δ * 2 := mul_le_mul_of_nonneg_left hlen (by positivity)
            _ = 12 * K_inv * u ^ δ := by ring
      -- Bound left vertical segment `σ = σ₁`, `t ∈ [-u, u]`
      have h_vert : ‖∫ t in (-u)..u, moebiusPerronIntegrand u ((σ₁ : ℂ) + (t : ℂ) * I)‖ ≤
          16 * K_inv * u ^ (σ₁ + δ) * Real.log (1 + u) := by
        have hdom_cont : Continuous fun t : ℝ =>
            (2 * K_inv * u ^ (σ₁ + δ)) * (4 / (1 + |t|)) :=
          continuous_const.mul
            (continuous_const.div (continuous_const.add continuous_abs) fun _ => by positivity)
        have hpt : ∀ t ∈ Icc (-u) u,
            ‖moebiusPerronIntegrand u ((σ₁ : ℂ) + (t : ℂ) * I)‖ ≤
              (2 * K_inv * u ^ (σ₁ + δ)) * (4 / (1 + |t|)) := by
          intro t ht
          have htabs : |t| ≤ u := abs_le.mpr ht
          unfold moebiusPerronIntegrand
          rw [norm_mul, norm_kf]
          have hre_s : ((σ₁ : ℂ) + (t : ℂ) * I).re = σ₁ := by simp
          have him_s : ((σ₁ : ℂ) + (t : ℂ) * I).im = t := by simp
          rw [hre_s]
          have hinv_bd : ‖invZeta ((σ₁ : ℂ) + (t : ℂ) * I)‖ ≤ 2 * K_inv * u ^ δ := by
            have h1 := hK_inv σ₁ t le_rfl (by dsimp [σ₁]; linarith)
            have h2 : (|t| + 2) ^ δ ≤ 2 * u ^ δ := by
              calc (|t| + 2) ^ δ ≤ (2 * u) ^ δ :=
                    Real.rpow_le_rpow (by positivity) (by linarith) hδ.le
                _ = 2 ^ δ * u ^ δ := Real.mul_rpow (by norm_num) hu0.le
                _ ≤ 2 * u ^ δ := by
                    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
                      (by linarith : δ ≤ 1)
            calc ‖invZeta ((σ₁ : ℂ) + (t : ℂ) * I)‖
                ≤ K_inv * (2 * u ^ δ) :=
                  h1.trans (mul_le_mul_of_nonneg_left h2 hK_inv_pos.le)
              _ = 2 * K_inv * u ^ δ := by ring
          have hexp_eq : Real.exp (σ₁ * Real.log u) = u ^ σ₁ := by
            rw [Real.rpow_def_of_pos hu0, mul_comm]
          have hnorm_ge : (1 + |t|) / 4 ≤ ‖(σ₁ : ℂ) + (t : ℂ) * I‖ := by
            have hre_ge := Complex.abs_re_le_norm ((σ₁ : ℂ) + (t : ℂ) * I)
            have him_ge := Complex.abs_im_le_norm ((σ₁ : ℂ) + (t : ℂ) * I)
            rw [hre_s, abs_of_pos (by linarith)] at hre_ge
            rw [him_s] at him_ge
            linarith
          have hkf_bd : Real.exp (σ₁ * Real.log u) / ‖(σ₁ : ℂ) + (t : ℂ) * I‖ ≤
              u ^ σ₁ * (4 / (1 + |t|)) := by
            rw [hexp_eq]
            calc u ^ σ₁ / ‖(σ₁ : ℂ) + (t : ℂ) * I‖
                ≤ u ^ σ₁ / ((1 + |t|) / 4) :=
                  div_le_div_of_nonneg_left (by positivity) (by positivity) hnorm_ge
              _ = u ^ σ₁ * (4 / (1 + |t|)) := by field_simp
          calc ‖invZeta ((σ₁ : ℂ) + (t : ℂ) * I)‖ *
                (Real.exp (σ₁ * Real.log u) / ‖(σ₁ : ℂ) + (t : ℂ) * I‖)
              ≤ (2 * K_inv * u ^ δ) * (u ^ σ₁ * (4 / (1 + |t|))) :=
                mul_le_mul hinv_bd hkf_bd (by positivity) (by positivity)
            _ = (2 * K_inv * (u ^ σ₁ * u ^ δ)) * (4 / (1 + |t|)) := by ring
            _ = (2 * K_inv * u ^ (σ₁ + δ)) * (4 / (1 + |t|)) := by
                rw [← Real.rpow_add hu0]
        have hint_le := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
          (by linarith : -u ≤ u)
          (Filter.Eventually.of_forall fun t ht =>
            hpt t ⟨ht.1.le, ht.2⟩)
          (hdom_cont.intervalIntegrable (-u) u)
        rw [intervalIntegral.integral_const_mul, integral_inv_one_add_abs u hu0.le] at hint_le
        calc ‖∫ t in (-u)..u, moebiusPerronIntegrand u ((σ₁ : ℂ) + (t : ℂ) * I)‖
            ≤ (2 * K_inv * u ^ (σ₁ + δ)) * (8 * Real.log (1 + u)) := hint_le
          _ = 16 * K_inv * u ^ (σ₁ + δ) * Real.log (1 + u) := by ring
      -- Assemble shifted Perron integral bound
      have h_int_c : ‖∫ t in (-u)..u, moebiusPerronIntegrand u ((c : ℂ) + (t : ℂ) * I)‖ ≤
          24 * K_inv * u ^ δ + 16 * K_inv * u ^ (σ₁ + δ) * Real.log (1 + u) := by
        have hn1 : ‖∫ t in (-u)..u, moebiusPerronIntegrand u ((c : ℂ) + (t : ℂ) * I)‖ =
            ‖I • (∫ t in (-u)..u, moebiusPerronIntegrand u ((c : ℂ) + (t : ℂ) * I))‖ := by
          rw [norm_smul, Complex.norm_I, one_mul]
        rw [hn1, hshift_eq]
        have hn2 : ‖I • (∫ t in (-u)..u, moebiusPerronIntegrand u ((σ₁ : ℂ) + (t : ℂ) * I))‖ =
            ‖∫ t in (-u)..u, moebiusPerronIntegrand u ((σ₁ : ℂ) + (t : ℂ) * I)‖ := by
          rw [norm_smul, Complex.norm_I, one_mul]
        have ht_top := h_horiz u (abs_of_pos hu0)
        have ht_bot := h_horiz (-u) (by rw [abs_neg, abs_of_pos hu0])
        have htri1 := norm_add_le
          (I • (∫ t in (-u)..u, moebiusPerronIntegrand u ((σ₁ : ℂ) + (t : ℂ) * I)) -
            (∫ σ in σ₁..c, moebiusPerronIntegrand u ((σ : ℂ) + ((-u : ℝ) : ℂ) * I)))
          (∫ σ in σ₁..c, moebiusPerronIntegrand u ((σ : ℂ) + ((u : ℝ) : ℂ) * I))
        have htri2 := norm_sub_le
          (I • (∫ t in (-u)..u, moebiusPerronIntegrand u ((σ₁ : ℂ) + (t : ℂ) * I)))
          (∫ σ in σ₁..c, moebiusPerronIntegrand u ((σ : ℂ) + ((-u : ℝ) : ℂ) * I))
        rw [hn2] at htri2
        linarith
      -- Divide by `2 * π ≥ 1`
      have h_perron_int_bd :
          ‖(1 / (2 * (π : ℂ))) *
              ∫ t in (-u)..u, moebiusPerronIntegrand u ((c : ℂ) + (t : ℂ) * I)‖ ≤
            24 * K_inv * u ^ δ + 16 * K_inv * u ^ (σ₁ + δ) * Real.log (1 + u) := by
        rw [norm_mul, one_div, norm_inv, norm_two_pi]
        have h2pi_ge1 : 1 ≤ 2 * π := by linarith [Real.pi_gt_three]
        have hinv_le1 : (2 * π)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h2pi_ge1
        calc (2 * π)⁻¹ * ‖∫ t in (-u)..u, moebiusPerronIntegrand u ((c : ℂ) + (t : ℂ) * I)‖
            ≤ 1 * (24 * K_inv * u ^ δ + 16 * K_inv * u ^ (σ₁ + δ) * Real.log (1 + u)) :=
              mul_le_mul hinv_le1 h_int_c (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
      -- Compare each term to `(u + 1) ^ (θ + ε)`
      have hu_pow_le : ∀ β : ℝ, β ≤ θ + ε → u ^ β ≤ ((N : ℝ) + 1) ^ (θ + ε) := by
        intro β hβ
        calc u ^ β ≤ u ^ (θ + ε) := Real.rpow_le_rpow_of_exponent_le hu1 hβ
          _ ≤ ((N : ℝ) + 1) ^ (θ + ε) :=
              Real.rpow_le_rpow hu0.le (by dsimp [u]; linarith) (by linarith)
      have hlog_u_le : Real.log u ≤ 4 * ((N : ℝ) + 1) ^ (θ + ε) := by
        have h1 : Real.log u ≤ u ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) :=
          Real.log_le_rpow_div hu0.le (by norm_num)
        have h2 : u ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) = 4 * u ^ (1 / 4 : ℝ) := by ring
        rw [h2] at h1
        exact h1.trans (mul_le_mul_of_nonneg_left (hu_pow_le (1 / 4) (by linarith)) (by norm_num))
      have hlog1u_term : u ^ (σ₁ + δ) * Real.log (1 + u) ≤
          (2 / δ) * ((N : ℝ) + 1) ^ (θ + ε) := by
        have h1 : Real.log (1 + u) ≤ Real.log (2 * u) :=
          Real.log_le_log (by positivity) (by linarith)
        have h2 : Real.log (2 * u) ≤ (2 * u) ^ δ / δ :=
          Real.log_le_rpow_div (by positivity) hδ
        have h3 : (2 * u) ^ δ ≤ 2 * u ^ δ := by
          rw [Real.mul_rpow (by norm_num) hu0.le]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have hδ_le1 : δ ≤ 1 := by linarith
          calc (2 : ℝ) ^ δ ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ_le1
            _ = 2 := Real.rpow_one 2
        have hlog_bd : Real.log (1 + u) ≤ (2 / δ) * u ^ δ := by
          calc Real.log (1 + u) ≤ (2 * u) ^ δ / δ := h1.trans h2
            _ ≤ (2 * u ^ δ) / δ := div_le_div_of_nonneg_right h3 hδ.le
            _ = (2 / δ) * u ^ δ := by ring
        have hexp_sum : (σ₁ + δ) + δ = θ + ε := by dsimp [σ₁]; linarith [hθ4_eq]
        calc u ^ (σ₁ + δ) * Real.log (1 + u)
            ≤ u ^ (σ₁ + δ) * ((2 / δ) * u ^ δ) :=
              mul_le_mul_of_nonneg_left hlog_bd (by positivity)
          _ = (2 / δ) * (u ^ (σ₁ + δ) * u ^ δ) := by ring
          _ = (2 / δ) * u ^ (θ + ε) := by rw [← Real.rpow_add hu0, hexp_sum]
          _ ≤ (2 / δ) * ((N : ℝ) + 1) ^ (θ + ε) :=
              mul_le_mul_of_nonneg_left (hu_pow_le (θ + ε) le_rfl) (by positivity)
      -- Combine triangle inequality with `moebius_perron_bound`
      set M_N : ℝ := ∑ d ∈ Finset.range (N + 1), (ArithmeticFunction.moebius d : ℝ)
      have htri_M : |M_N| ≤
          ‖(M_N : ℂ) - (1 / (2 * (π : ℂ))) *
            ∫ t in (-u)..u, moebiusPerronIntegrand u ((c : ℂ) + (t : ℂ) * I)‖ +
          ‖(1 / (2 * (π : ℂ))) *
            ∫ t in (-u)..u, moebiusPerronIntegrand u ((c : ℂ) + (t : ℂ) * I)‖ := by
        have h := norm_add_le
          ((M_N : ℂ) - (1 / (2 * (π : ℂ))) *
            ∫ t in (-u)..u, moebiusPerronIntegrand u ((c : ℂ) + (t : ℂ) * I))
          ((1 / (2 * (π : ℂ))) *
            ∫ t in (-u)..u, moebiusPerronIntegrand u ((c : ℂ) + (t : ℂ) * I))
        rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs] at h
        exact h
      have h50 : 50 * Real.log u + 50 ≤ 500 * ((N : ℝ) + 1) ^ (θ + ε) := by
        nlinarith [hlog_u_le, hpow_ge1]
      have h24 : 24 * K_inv * u ^ δ ≤ 24 * K_inv * ((N : ℝ) + 1) ^ (θ + ε) :=
        mul_le_mul_of_nonneg_left (hu_pow_le δ (by linarith)) (by positivity)
      have h16 : 16 * K_inv * u ^ (σ₁ + δ) * Real.log (1 + u) ≤
          (32 * K_inv / δ) * ((N : ℝ) + 1) ^ (θ + ε) := by
        calc 16 * K_inv * u ^ (σ₁ + δ) * Real.log (1 + u)
            = 16 * K_inv * (u ^ (σ₁ + δ) * Real.log (1 + u)) := by ring
          _ ≤ 16 * K_inv * ((2 / δ) * ((N : ℝ) + 1) ^ (θ + ε)) :=
              mul_le_mul_of_nonneg_left hlog1u_term (by positivity)
          _ = (32 * K_inv / δ) * ((N : ℝ) + 1) ^ (θ + ε) := by ring
      have htot : |M_N| ≤ C_big * ((N : ℝ) + 1) ^ (θ + ε) := by
        dsimp [C_big]
        linarith [htri_M, hperron, h_perron_int_bd, h50, h24, h16]
      exact htot.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

/-- **Littlewood's Theorem under `RiemannHypothesis`:**
`RiemannHypothesis` implies `M(N) = O_ε((N + 1)^{1/2 + ε})` for every `ε > 0`. -/
theorem rh_implies_prefixExponent_half (hRH : RiemannHypothesis) :
    PrefixExponent (1 / 2) := by
  refine prefixExponent_of_zeroFree le_rfl (by norm_num) fun s hs hz => ?_
  have htriv : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, rfl⟩
    have hre : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [hre] at hs
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hs1 : s ≠ 1 := by rintro rfl; exact riemannZeta_one_ne_zero hz
  have hre_eq := hRH s hz htriv hs1
  linarith

end HalvingMertens
