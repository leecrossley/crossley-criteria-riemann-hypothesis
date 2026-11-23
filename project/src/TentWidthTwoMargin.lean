import TentZeroBudget
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section
namespace TentWidthTwoMargin

/-!
# All-Widths Critical-Line Tent Zero-Mass Cap and Width-Two Margin Bound

Formalized from Mathlib alone on top of `TentZeroBudget`:
1. Complex tent transform `tentKernel` (`H_b(s)`) and dephased companion `tentDephased` (`P_b(s)`),
   their identity `b^(1/2 - s) * H_b(s) = P_b(s)`, real-coordinate bridge to
   `TentZeroBudget.companionRe`, critical-line norm equality `Re P_b(1/2 + i t) = ‖H_b(1/2 + i t)‖ > 0`,
   and `s ↦ 1 - s` / conjugation symmetries.
2. Unconditional all-widths critical-line upper bound `∑_{Re ρ = 1/2} ‖H_b(ρ)‖ ≤ L_b^*` and
   strict equality criterion (equality holds if and only if every zero lies on `Re s = 1/2`).
3. Exact evaluation of the width-two single-ramp series and equivalence of the ramp formula
   `√2 * (3 C_0 - 2 S(2))` with `widthTwoCapClosed = √2 * (3 log 3 - 2 log 2 - γ_E - log π)`.
4. Pure-Mathlib 14-digit rational enclosure of `widthTwoMargin = 0.21997921744308...` via
   odd-power `artanh` bounds for `log 2`, `log 3`, `log π` and Euler–Maclaurin monotonicity bounds
   for `eulerMascheroniConstant`.
-/

/-! ## 1. Complex Tent Kernel and Dephased Companion -/

/-- Mellin-Laplace kernel `H_b(s) = (b^s - 1)(b^s - b) / (s(s - 1))` of the tent window of width `b`. -/
def tentKernel (b : ℝ) (s : ℂ) : ℂ :=
  ((b : ℂ) ^ s - 1) * ((b : ℂ) ^ s - b) / (s * (s - 1))

/-- Dephased companion `P_b(s) = √b * ((b + 1) - b^s - b^(1 - s)) / (s(1 - s))`. -/
def tentDephased (b : ℝ) (s : ℂ) : ℂ :=
  (Real.sqrt b : ℂ) * ((b + 1 : ℂ) - (b : ℂ) ^ s - (b : ℂ) ^ (1 - s)) / (s * (1 - s))

private lemma ofReal_cpow_eq_exp {b : ℝ} (hb : 0 < b) (z : ℂ) :
    (b : ℂ) ^ z = Complex.exp ((Real.log b : ℂ) * z) := by
  have hb0 : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  rw [Complex.cpow_def_of_ne_zero hb0, ← Complex.ofReal_log hb.le]

private lemma ofReal_sqrt_eq_exp {b : ℝ} (hb : 0 < b) :
    (Real.sqrt b : ℂ) = Complex.exp ((Real.log b : ℂ) * (1 / 2 : ℂ)) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hb, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

private lemma ofReal_eq_exp {b : ℝ} (hb : 0 < b) :
    (b : ℂ) = Complex.exp (Real.log b : ℂ) := by
  rw [← Complex.ofReal_exp, Real.exp_log hb]

/-- Dephasing identity `b^(1/2 - s) * H_b(s) = P_b(s)` for `1 < b`. -/
theorem tentDephased_eq_mul_tentKernel {b : ℝ} (hb : 1 < b) (s : ℂ) :
    (b : ℂ) ^ ((1 / 2 : ℂ) - s) * tentKernel b s = tentDephased b s := by
  have hb0 : 0 < b := by linarith
  unfold tentKernel tentDephased
  rw [mul_div_assoc']
  have hnum :
      (b : ℂ) ^ ((1 / 2 : ℂ) - s) * (((b : ℂ) ^ s - 1) * ((b : ℂ) ^ s - (b : ℂ))) =
        -((Real.sqrt b : ℂ) * ((b + 1 : ℂ) - (b : ℂ) ^ s - (b : ℂ) ^ (1 - s))) := by
    rw [ofReal_cpow_eq_exp hb0 ((1 / 2 : ℂ) - s),
      ofReal_cpow_eq_exp hb0 s,
      ofReal_cpow_eq_exp hb0 (1 - s),
      ofReal_sqrt_eq_exp hb0]
    conv_lhs =>
      arg 2; arg 2; arg 2
      rw [ofReal_eq_exp hb0]
    set L : ℂ := (Real.log b : ℂ)
    have e1 :
        Complex.exp (L * ((1 / 2 : ℂ) - s)) * (Complex.exp (L * s) * Complex.exp (L * s)) =
          Complex.exp (L * (1 / 2 : ℂ)) * Complex.exp (L * s) := by
      repeat rw [← Complex.exp_add]
      congr 1; ring
    have e2 :
        Complex.exp (L * ((1 / 2 : ℂ) - s)) * Complex.exp (L * s) =
          Complex.exp (L * (1 / 2 : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1; ring
    have e3 :
        Complex.exp (L * ((1 / 2 : ℂ) - s)) * (Complex.exp (L * s) * Complex.exp L) =
          Complex.exp (L * (1 / 2 : ℂ)) * (b : ℂ) := by
      rw [← ofReal_eq_exp hb0]
      calc
        Complex.exp (L * ((1 / 2 : ℂ) - s)) * (Complex.exp (L * s) * (b : ℂ))
            = (Complex.exp (L * ((1 / 2 : ℂ) - s)) * Complex.exp (L * s)) * (b : ℂ) := by ring
        _ = Complex.exp (L * (1 / 2 : ℂ)) * (b : ℂ) := by rw [e2]
    have e4 :
        Complex.exp (L * ((1 / 2 : ℂ) - s)) * Complex.exp L =
          Complex.exp (L * (1 / 2 : ℂ)) * Complex.exp (L * (1 - s)) := by
      repeat rw [← Complex.exp_add]
      congr 1; ring
    calc
      Complex.exp (L * ((1 / 2 : ℂ) - s)) *
          ((Complex.exp (L * s) - 1) * (Complex.exp (L * s) - Complex.exp L))
          = Complex.exp (L * ((1 / 2 : ℂ) - s)) * (Complex.exp (L * s) * Complex.exp (L * s)) -
              Complex.exp (L * ((1 / 2 : ℂ) - s)) * (Complex.exp (L * s) * Complex.exp L) -
              Complex.exp (L * ((1 / 2 : ℂ) - s)) * Complex.exp (L * s) +
              Complex.exp (L * ((1 / 2 : ℂ) - s)) * Complex.exp L := by ring
      _ = Complex.exp (L * (1 / 2 : ℂ)) * Complex.exp (L * s) -
            Complex.exp (L * (1 / 2 : ℂ)) * (b : ℂ) -
            Complex.exp (L * (1 / 2 : ℂ)) +
            Complex.exp (L * (1 / 2 : ℂ)) * Complex.exp (L * (1 - s)) := by
          rw [e1, e2, e3, e4]
      _ = -(Complex.exp (L * (1 / 2 : ℂ)) *
            ((b + 1 : ℂ) - Complex.exp (L * s) - Complex.exp (L * (1 - s)))) := by ring
  have hden : s * (s - 1) = -(s * (1 - s)) := by ring
  rw [hnum, hden, neg_div_neg_eq]

private lemma cpow_re_im {b : ℝ} (hb : 0 < b) (z : ℂ) :
    ((b : ℂ) ^ z).re = b ^ z.re * Real.cos (z.im * Real.log b) ∧
      ((b : ℂ) ^ z).im = b ^ z.re * Real.sin (z.im * Real.log b) := by
  rw [ofReal_cpow_eq_exp hb z]
  have hre : ((Real.log b : ℂ) * z).re = Real.log b * z.re := by simp
  have him : ((Real.log b : ℂ) * z).im = z.im * Real.log b := by simp [mul_comm]
  rw [Complex.exp_re, Complex.exp_im, hre, him, ← Real.rpow_def_of_pos hb]
  exact ⟨rfl, rfl⟩

/-- Real-coordinate identity matching `tentDephased` with `TentZeroBudget.companionRe`. -/
theorem tentDephased_re_eq_companionRe {b : ℝ} (hb : 1 < b) (s : ℂ) :
    (tentDephased b s).re = TentZeroBudget.companionRe b s.re s.im := by
  have hb0 : 0 < b := by linarith
  obtain ⟨hs_re, hs_im⟩ := cpow_re_im hb0 s
  obtain ⟨h1s_re, h1s_im⟩ := cpow_re_im hb0 (1 - s)
  have h1s_re' : (1 - s).re = 1 - s.re := by simp
  have h1s_im' : (1 - s).im = -s.im := by simp
  rw [h1s_re', h1s_im', neg_mul, Real.cos_neg] at h1s_re
  rw [h1s_re', h1s_im', neg_mul, Real.sin_neg, mul_neg] at h1s_im
  unfold tentDephased TentZeroBudget.companionRe
  set num : ℂ := (Real.sqrt b : ℂ) * ((b + 1 : ℂ) - (b : ℂ) ^ s - (b : ℂ) ^ (1 - s))
  set den : ℂ := s * (1 - s)
  have hden_re : den.re = s.im ^ 2 + s.re * (1 - s.re) := by
    simp [den, Complex.mul_re]
    ring
  have hden_im : den.im = s.im * (1 - 2 * s.re) := by
    simp [den, Complex.mul_im]
    ring
  have hden_nsq : Complex.normSq den =
      (s.im ^ 2 + s.re * (1 - s.re)) ^ 2 + (s.im * (1 - 2 * s.re)) ^ 2 := by
    rw [Complex.normSq_apply, hden_re, hden_im]
    ring
  have hnum_re : num.re =
      Real.sqrt b * ((b + 1) - (b ^ s.re + b ^ (1 - s.re)) * Real.cos (s.im * Real.log b)) := by
    simp only [num, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
      Complex.add_re, Complex.one_re, zero_mul, sub_zero, hs_re, h1s_re]
    ring
  have hnum_im : num.im =
      -(Real.sqrt b * ((b ^ s.re - b ^ (1 - s.re)) * Real.sin (s.im * Real.log b))) := by
    simp only [num, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
      Complex.add_im, Complex.one_im, zero_mul, add_zero, hs_im, h1s_im]
    ring
  rw [Complex.div_re, hnum_re, hnum_im, hden_re, hden_im, hden_nsq, ← add_div]
  congr 1
  ring

/-- Imaginary part of `tentDephased b s` vanishes on the critical line `Re s = 1/2`. -/
theorem tentDephased_criticalLine_im_eq_zero {b : ℝ} {s : ℂ} (hb : 1 < b) (hs : s.re = 1 / 2) :
    (tentDephased b s).im = 0 := by
  have hb0 : 0 < b := by linarith
  obtain ⟨_, hs_im⟩ := cpow_re_im hb0 s
  obtain ⟨_, h1s_im⟩ := cpow_re_im hb0 (1 - s)
  have h1s_re' : (1 - s).re = 1 / 2 := by simp [hs]; norm_num
  have h1s_im' : (1 - s).im = -s.im := by simp
  rw [hs] at hs_im
  rw [h1s_re', h1s_im', neg_mul, Real.sin_neg, mul_neg] at h1s_im
  unfold tentDephased
  set num : ℂ := (Real.sqrt b : ℂ) * ((b + 1 : ℂ) - (b : ℂ) ^ s - (b : ℂ) ^ (1 - s))
  set den : ℂ := s * (1 - s)
  have hnum_im : num.im = 0 := by
    simp [num, Complex.mul_im, hs_im, h1s_im]
  have hden_im : den.im = 0 := by
    simp [den, Complex.mul_im, hs]
    ring
  rw [Complex.div_im, hnum_im, hden_im]
  ring

/-- On the critical line `Re s = 1/2`, `Re P_b(s)` is strictly positive for every `b > 1`. -/
theorem tentDephased_criticalLine_re_pos {b : ℝ} {s : ℂ} (hb : 1 < b) (hs : s.re = 1 / 2) :
    0 < (tentDephased b s).re := by
  rw [tentDephased_re_eq_companionRe hb s]
  unfold TentZeroBudget.companionRe
  rw [hs]
  have hb0 : 0 < b := by linarith
  have hsqrt_gt : 1 < Real.sqrt b := by
    rw [Real.lt_sqrt (by norm_num)]
    linarith
  have hb_half : b ^ (1 / 2 : ℝ) = Real.sqrt b := (Real.sqrt_eq_rpow b).symm
  have h1_sub : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  have h2_sub : (1 : ℝ) - 2 * (1 / 2 : ℝ) = 0 := by norm_num
  rw [h1_sub, h2_sub, hb_half]
  have hcos : Real.cos (s.im * Real.log b) ≤ 1 := Real.cos_le_one _
  have hsq : b + 1 - 2 * Real.sqrt b = (Real.sqrt b - 1) ^ 2 := by
    have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0.le
    nlinarith
  have hfactor : 0 < (b + 1) - (Real.sqrt b + Real.sqrt b) * Real.cos (s.im * Real.log b) := by
    have hsb_pos : 0 < Real.sqrt b := by linarith
    have h1 : (Real.sqrt b + Real.sqrt b) * Real.cos (s.im * Real.log b) ≤ 2 * Real.sqrt b := by
      nlinarith
    have h2 : 0 < (Real.sqrt b - 1) ^ 2 := sq_pos_of_pos (by linarith)
    linarith
  have hu : 0 < s.im ^ 2 + (1 / 2 : ℝ) * (1 / 2 : ℝ) := by positivity
  simp only [mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  positivity

/-- On the critical line `Re s = 1/2`, `P_b(s)` is real and positive and equals `‖H_b(s)‖`. -/
theorem tentDephased_criticalLine_eq_norm {b : ℝ} {s : ℂ} (hb : 1 < b) (hs : s.re = 1 / 2) :
    (tentDephased b s).re = ‖tentKernel b s‖ ∧ (tentDephased b s).im = 0 := by
  have hb0 : 0 < b := by linarith
  have him : (tentDephased b s).im = 0 := tentDephased_criticalLine_im_eq_zero hb hs
  have hpos : 0 < (tentDephased b s).re := tentDephased_criticalLine_re_pos hb hs
  refine ⟨?_, him⟩
  have hmul := congrArg norm (tentDephased_eq_mul_tentKernel hb s)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hb0] at hmul
  have hexp_re : ((1 / 2 : ℂ) - s).re = 0 := by simp [hs]
  rw [hexp_re, Real.rpow_zero, one_mul] at hmul
  have hz : tentDephased b s = ((tentDephased b s).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hnorm_re : ‖tentDephased b s‖ = (tentDephased b s).re := by
    conv_lhs => rw [hz]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  linarith

/-- Pointwise strict positivity `0 < ‖H_b(1/2 + t * I)‖` for every `b > 1` and `t : ℝ`. -/
theorem tentKernel_criticalLine_norm_pos {b : ℝ} (hb : 1 < b) (t : ℝ) :
    0 < ‖tentKernel b ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ := by
  set s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  have hs : s.re = 1 / 2 := by simp [s]
  rw [← (tentDephased_criticalLine_eq_norm hb hs).1]
  exact tentDephased_criticalLine_re_pos hb hs

/-- Functional symmetry `P_b(1 - s) = P_b(s)`. -/
theorem tentDephased_one_sub (b : ℝ) (s : ℂ) :
    tentDephased b (1 - s) = tentDephased b s := by
  unfold tentDephased
  have h1 : 1 - (1 - s) = s := by ring
  rw [h1]
  congr 1
  · congr 1; ring
  · ring

/-- Conjugation symmetry `Re P_b(conj s) = Re P_b(s)` for `1 < b`. -/
theorem tentDephased_conj_re {b : ℝ} (hb : 1 < b) (s : ℂ) :
    (tentDephased b (starRingEnd ℂ s)).re = (tentDephased b s).re := by
  rw [tentDephased_re_eq_companionRe hb, tentDephased_re_eq_companionRe hb]
  unfold TentZeroBudget.companionRe
  simp only [Complex.conj_re, Complex.conj_im, even_two, Even.neg_pow, neg_mul, Real.cos_neg,
    Real.sin_neg, mul_neg]
  ring

/-- Combined functional and conjugation symmetry of `tentDephased`. -/
theorem tentDephased_symm {b : ℝ} (hb : 1 < b) (s : ℂ) :
    tentDephased b (1 - s) = tentDephased b s ∧
      (tentDephased b (starRingEnd ℂ s)).re = (tentDephased b s).re :=
  ⟨tentDephased_one_sub b s, tentDephased_conj_re hb s⟩

/-! ## 2. Unconditional All-Widths Critical-Line Cap and Equality Criterion -/

/-- Summability of the critical-line tent norms from summability of `Re P_b(ρ_i)` under `1 ≤ e t^2`. -/
theorem summable_criticalLine_tent_of_quadratic {ι : Type*} {b : ℝ} {ρ : ι → ℂ}
    (hb : 1 < b)
    (hsum : Summable (fun i => (tentDephased b (ρ i)).re))
    (hoff : ∀ i, (ρ i).re ≠ 1 / 2 →
      ∃ e : ℝ, 0 < e ∧ e ≤ (ρ i).re ∧ e ≤ 1 - (ρ i).re ∧ 1 ≤ e * (ρ i).im ^ 2) :
    Summable (fun i => if (ρ i).re = 1 / 2 then ‖tentKernel b (ρ i)‖ else 0) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hsum
  · split_ifs
    · exact norm_nonneg _
    · exact le_rfl
  · split_ifs with h
    · exact (tentDephased_criticalLine_eq_norm hb h).1.symm.le
    · obtain ⟨e, he, hl, hr, ht⟩ := hoff i h
      rw [tentDephased_re_eq_companionRe hb]
      exact (TentZeroBudget.companionRe_pos hb he hl hr ht).le

/-- Unconditional critical-line upper bound under the quadratic strip-height condition `1 ≤ e t^2`. -/
theorem criticalLine_tent_sum_le_cap_of_quadratic {ι : Type*} {b L : ℝ} {ρ : ι → ℂ}
    (hb : 1 < b)
    (hsum : Summable (fun i => (tentDephased b (ρ i)).re))
    (hmass : (∑' i, (tentDephased b (ρ i)).re) = L)
    (hoff : ∀ i, (ρ i).re ≠ 1 / 2 →
      ∃ e : ℝ, 0 < e ∧ e ≤ (ρ i).re ∧ e ≤ 1 - (ρ i).re ∧ 1 ≤ e * (ρ i).im ^ 2) :
    (∑' i, (if (ρ i).re = 1 / 2 then ‖tentKernel b (ρ i)‖ else 0)) ≤ L := by
  have hg := summable_criticalLine_tent_of_quadratic hb hsum hoff
  rw [← hmass]
  refine Summable.tsum_le_tsum (fun i => ?_) hg hsum
  split_ifs with h
  · exact (tentDephased_criticalLine_eq_norm hb h).1.symm.le
  · obtain ⟨e, he, hl, hr, ht⟩ := hoff i h
    rw [tentDephased_re_eq_companionRe hb]
    exact (TentZeroBudget.companionRe_pos hb he hl hr ht).le

/-- Equality holds in the critical-line cap iff every indexed zero lies on `Re s = 1/2`
(under `1 ≤ e t^2`). -/
theorem criticalLine_tent_sum_eq_cap_iff_of_quadratic {ι : Type*} {b L : ℝ} {ρ : ι → ℂ}
    (hb : 1 < b)
    (hsum : Summable (fun i => (tentDephased b (ρ i)).re))
    (hmass : (∑' i, (tentDephased b (ρ i)).re) = L)
    (hoff : ∀ i, (ρ i).re ≠ 1 / 2 →
      ∃ e : ℝ, 0 < e ∧ e ≤ (ρ i).re ∧ e ≤ 1 - (ρ i).re ∧ 1 ≤ e * (ρ i).im ^ 2) :
    (∑' i, (if (ρ i).re = 1 / 2 then ‖tentKernel b (ρ i)‖ else 0)) = L ↔
      ∀ i, (ρ i).re = 1 / 2 := by
  constructor
  · intro heq i₀
    by_contra hne
    have hg := summable_criticalLine_tent_of_quadratic hb hsum hoff
    set d : ι → ℝ := fun i =>
      (tentDephased b (ρ i)).re - (if (ρ i).re = 1 / 2 then ‖tentKernel b (ρ i)‖ else 0)
    have hd_sum : Summable d := hsum.sub hg
    have hd_nonneg : ∀ j, 0 ≤ d j := by
      intro j
      dsimp [d]
      split_ifs with hj
      · rw [(tentDephased_criticalLine_eq_norm hb hj).1, sub_self]
      · obtain ⟨e, he, hl, hr, ht⟩ := hoff j hj
        rw [sub_zero, tentDephased_re_eq_companionRe hb]
        exact (TentZeroBudget.companionRe_pos hb he hl hr ht).le
    have hd_le : d i₀ ≤ ∑' i, d i := Summable.le_tsum hd_sum i₀ (fun j _ => hd_nonneg j)
    have hd_tsum : (∑' i, d i) = 0 := by
      dsimp [d]
      rw [hsum.tsum_sub hg, hmass, heq, sub_self]
    obtain ⟨e, he, hl, hr, ht⟩ := hoff i₀ hne
    have hd_pos : 0 < d i₀ := by
      dsimp [d]
      rw [if_neg hne, sub_zero, tentDephased_re_eq_companionRe hb]
      exact TentZeroBudget.companionRe_pos hb he hl hr ht
    linarith
  · intro hall
    rw [← hmass]
    congr 1
    ext i
    rw [if_pos (hall i), (tentDephased_criticalLine_eq_norm hb (hall i)).1]

/-- Unconditional all-widths critical-line upper bound under the classical logarithmic strip
(`|Im ρ| ≥ 6` and `1 ≤ 6 log|Im ρ| * e` for any off-line zero). -/
theorem criticalLine_tent_sum_le_cap {ι : Type*} {b L : ℝ} {ρ : ι → ℂ}
    (hb : 1 < b)
    (hsum : Summable (fun i => (tentDephased b (ρ i)).re))
    (hmass : (∑' i, (tentDephased b (ρ i)).re) = L)
    (hoff : ∀ i, (ρ i).re ≠ 1 / 2 →
      ∃ e : ℝ, 0 < e ∧ e ≤ (ρ i).re ∧ e ≤ 1 - (ρ i).re ∧
        6 ≤ |(ρ i).im| ∧ 1 ≤ 6 * Real.log |(ρ i).im| * e) :
    (∑' i, (if (ρ i).re = 1 / 2 then ‖tentKernel b (ρ i)‖ else 0)) ≤ L := by
  refine criticalLine_tent_sum_le_cap_of_quadratic hb hsum hmass (fun i hi => ?_)
  obtain ⟨e, he, hl, hr, ht, hw⟩ := hoff i hi
  exact ⟨e, he, hl, hr, TentZeroBudget.height_criterion ht he hw⟩

/-- Equality holds in the critical-line cap iff every zero lies on `Re s = 1/2`
(under the classical logarithmic strip above height `6`). -/
theorem criticalLine_tent_sum_eq_cap_iff {ι : Type*} {b L : ℝ} {ρ : ι → ℂ}
    (hb : 1 < b)
    (hsum : Summable (fun i => (tentDephased b (ρ i)).re))
    (hmass : (∑' i, (tentDephased b (ρ i)).re) = L)
    (hoff : ∀ i, (ρ i).re ≠ 1 / 2 →
      ∃ e : ℝ, 0 < e ∧ e ≤ (ρ i).re ∧ e ≤ 1 - (ρ i).re ∧
        6 ≤ |(ρ i).im| ∧ 1 ≤ 6 * Real.log |(ρ i).im| * e) :
    (∑' i, (if (ρ i).re = 1 / 2 then ‖tentKernel b (ρ i)‖ else 0)) = L ↔
      ∀ i, (ρ i).re = 1 / 2 := by
  refine criticalLine_tent_sum_eq_cap_iff_of_quadratic hb hsum hmass (fun i hi => ?_)
  obtain ⟨e, he, hl, hr, ht, hw⟩ := hoff i hi
  exact ⟨e, he, hl, hr, TentZeroBudget.height_criterion ht he hw⟩

/-! ## 3. Exact Closed-Form Ramp Series Identity at Width `b = 2` -/

/-- Limiting prime-square bias at width two: `B_2 = 6√2 - 8 = 2√2 (√2 - 1)^2`. -/
def primeSquareBias2 : ℝ := 6 * Real.sqrt 2 - 8

/-- Closed-form critical-line zero-mass cap at width two:
`L_2^* = √2 * (3 log 3 - 2 log 2 - γ_E - log π)`. -/
def widthTwoCapClosed : ℝ :=
  Real.sqrt 2 * (3 * Real.log 3 - 2 * Real.log 2 - Real.eulerMascheroniConstant - Real.log Real.pi)

/-- Completed-zeta sum `C_0 = 2 + γ_E - log(4π)`. -/
def cZero : ℝ := 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)

/-- Single-ramp explicit formula at `b = 2` (where the prime-power ramp `n ≤ 2` vanishes):
`S(2) = 2(1 + γ_E - log 2) - log(2π) + ∑_{k ≥ 0} 1 / (4^(k+1) * (2(k+1)) * (2(k+1)+1))`. -/
def rampTwoExplicit : ℝ :=
  2 * (1 + Real.eulerMascheroniConstant - Real.log 2) - Real.log (2 * Real.pi) +
    ∑' k : ℕ, (1 : ℝ) / ((4 : ℝ) ^ (k + 1) * (2 * (k + 1)) * (2 * (k + 1) + 1))

/-- Post-critical-line margin `Δ_2 = B_2 - L_2^*` at width two. -/
def widthTwoMargin : ℝ := primeSquareBias2 - widthTwoCapClosed

/-- Factored form `B_2 = 2√2 (√2 - 1)^2`. -/
theorem primeSquareBias2_eq :
    primeSquareBias2 = 2 * Real.sqrt 2 * (Real.sqrt 2 - 1) ^ 2 := by
  unfold primeSquareBias2
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith

/-- Odd-power series `∑_{j ≥ 0} 2 u^(2j+1) / (2j+1) = log((1 + u)/(1 - u))` for `|u| < 1`. -/
theorem hasSum_log_one_add_div_one_sub {u : ℝ} (hu : |u| < 1) :
    HasSum (fun j : ℕ => 2 * (u ^ (2 * j + 1) / (2 * (j : ℝ) + 1)))
      (Real.log ((1 + u) / (1 - u))) := by
  have hu_neg : |-u| < 1 := by simpa using hu
  have h1 : HasSum (fun n : ℕ => u ^ (n + 1) / ((n : ℝ) + 1)) (-Real.log (1 - u)) :=
    Real.hasSum_pow_div_log_of_abs_lt_one hu
  have h2 : HasSum (fun n : ℕ => (-u) ^ (n + 1) / ((n : ℝ) + 1)) (-Real.log (1 + u)) := by
    simpa [sub_neg_eq_add] using Real.hasSum_pow_div_log_of_abs_lt_one hu_neg
  have h1_sum : Summable (fun n : ℕ => u ^ (n + 1) / ((n : ℝ) + 1)) := h1.summable
  have h2_sum : Summable (fun n : ℕ => (-u) ^ (n + 1) / ((n : ℝ) + 1)) := h2.summable
  have inj_even : Function.Injective (fun j : ℕ => 2 * j) :=
    mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0)
  have inj_odd : Function.Injective (fun j : ℕ => 2 * j + 1) := by
    intro a b hab
    dsimp at hab
    omega
  have he1_raw : Summable (fun j : ℕ => u ^ (2 * j + 1) / ((2 * j : ℕ) + 1 : ℝ)) :=
    h1_sum.comp_injective inj_even
  have he1 : Summable (fun j : ℕ => u ^ (2 * j + 1) / (2 * (j : ℝ) + 1)) := by
    simpa [Nat.cast_mul] using he1_raw
  have ho1 : Summable (fun j : ℕ => u ^ (2 * j + 1 + 1) / ((2 * j + 1 : ℕ) + 1 : ℝ)) :=
    h1_sum.comp_injective inj_odd
  have he2 : Summable (fun j : ℕ => (-u) ^ (2 * j + 1) / ((2 * j : ℕ) + 1 : ℝ)) :=
    h2_sum.comp_injective inj_even
  have ho2 : Summable (fun j : ℕ => (-u) ^ (2 * j + 1 + 1) / ((2 * j + 1 : ℕ) + 1 : ℝ)) :=
    h2_sum.comp_injective inj_odd
  have split1 := tsum_even_add_odd (f := fun n : ℕ => u ^ (n + 1) / ((n : ℝ) + 1)) he1_raw ho1
  have split2 := tsum_even_add_odd (f := fun n : ℕ => (-u) ^ (n + 1) / ((n : ℝ) + 1)) he2 ho2
  rw [h1.tsum_eq] at split1
  rw [h2.tsum_eq] at split2
  have neg_even_term :
      (fun j : ℕ => (-u) ^ (2 * j + 1) / ((2 * j : ℕ) + 1 : ℝ)) =
        fun j : ℕ => -(u ^ (2 * j + 1) / ((2 * j : ℕ) + 1 : ℝ)) := by
    ext j
    have hodd : Odd (2 * j + 1) := ⟨j, rfl⟩
    rw [hodd.neg_pow, neg_div]
  have neg_odd_term :
      (fun j : ℕ => (-u) ^ (2 * j + 1 + 1) / ((2 * j + 1 : ℕ) + 1 : ℝ)) =
        fun j : ℕ => u ^ (2 * j + 1 + 1) / ((2 * j + 1 : ℕ) + 1 : ℝ) := by
    ext j
    have hev : Even (2 * j + 1 + 1) := ⟨j + 1, by ring⟩
    rw [hev.neg_pow]
  rw [neg_even_term, tsum_neg, neg_odd_term] at split2
  have hcast_even :
      (fun j : ℕ => u ^ (2 * j + 1) / ((2 * j : ℕ) + 1 : ℝ)) =
        fun j : ℕ => u ^ (2 * j + 1) / (2 * (j : ℝ) + 1) := by
    ext j; push_cast; rfl
  rw [hcast_even] at split1 split2
  have hu_pos : 0 < 1 + u := by linarith [(abs_lt.mp hu).1]
  have hu_pos' : 0 < 1 - u := by linarith [(abs_lt.mp hu).2]
  have hlog_div : Real.log ((1 + u) / (1 - u)) = Real.log (1 + u) - Real.log (1 - u) :=
    Real.log_div hu_pos.ne' hu_pos'.ne'
  have htsum :
      2 * (∑' j : ℕ, u ^ (2 * j + 1) / (2 * (j : ℝ) + 1)) = Real.log ((1 + u) / (1 - u)) := by
    linarith
  rw [← htsum]
  exact he1.hasSum.mul_left 2

/-- Even-power series `∑_{k ≥ 0} u^(2k+2) / (2k+2) = (-log(1 - u) - log(1 + u)) / 2` for `|u| < 1`. -/
theorem hasSum_even_pow_div_log {u : ℝ} (hu : |u| < 1) :
    HasSum (fun k : ℕ => u ^ (2 * k + 2) / (2 * (k : ℝ) + 2))
      ((-Real.log (1 - u) - Real.log (1 + u)) / 2) := by
  have hu2 : |u ^ 2| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg u) hu (by norm_num)
  have h := Real.hasSum_pow_div_log_of_abs_lt_one hu2
  have h_half := h.div_const 2
  have hterm :
      (fun k : ℕ => ((u ^ 2) ^ (k + 1) / ((k : ℝ) + 1)) / 2) =
        fun k : ℕ => u ^ (2 * k + 2) / (2 * (k : ℝ) + 2) := by
    ext k
    have hp : (u ^ 2) ^ (k + 1) = u ^ (2 * k + 2) := by
      rw [← pow_mul]
      ring_nf
    rw [hp, div_div]
    congr 1
    ring
  rw [hterm] at h_half
  have hu_pos : 0 < 1 + u := by linarith [(abs_lt.mp hu).1]
  have hu_pos' : 0 < 1 - u := by linarith [(abs_lt.mp hu).2]
  have hlog : -Real.log (1 - u ^ 2) = -Real.log (1 - u) - Real.log (1 + u) := by
    have hfac : 1 - u ^ 2 = (1 - u) * (1 + u) := by ring
    rw [hfac, Real.log_mul hu_pos'.ne' hu_pos.ne']
    ring
  simpa [hlog] using h_half

/-- Closed form of the archimedean Gamma-tail series at `b = 2`:
`∑_{k ≥ 0} 1 / (4^(k+1) * (2(k+1)) * (2(k+1)+1)) = 1 + log 2 - (3/2) log 3`. -/
theorem rampTwoSeries_hasSum :
    HasSum
      (fun k : ℕ => (1 : ℝ) / ((4 : ℝ) ^ (k + 1) * (2 * (k + 1)) * (2 * (k + 1) + 1)))
      (1 + Real.log 2 - (3 / 2 : ℝ) * Real.log 3) := by
  have hhalf : |(1 / 2 : ℝ)| < 1 := by norm_num
  have he := hasSum_even_pow_div_log hhalf
  have ho := hasSum_log_one_add_div_one_sub hhalf
  let fo : ℕ → ℝ := fun j => 2 * ((1 / 2 : ℝ) ^ (2 * j + 1) / (2 * (j : ℝ) + 1))
  have ho_shift :
      HasSum (fun k : ℕ => fo (k + 1))
        (Real.log (((1 : ℝ) + 1 / 2) / (1 - 1 / 2)) - 1) := by
    rw [hasSum_nat_add_iff (f := fo) 1]
    have h0 : ∑ i ∈ Finset.range 1, fo i = 1 := by
      simp [fo]
    rw [h0, sub_add_cancel]
    exact ho
  have hdiff := he.sub ho_shift
  have hterm :
      (fun k : ℕ => (1 / 2 : ℝ) ^ (2 * k + 2) / (2 * (k : ℝ) + 2) - fo (k + 1)) =
        fun k : ℕ => (1 : ℝ) / ((4 : ℝ) ^ (k + 1) * (2 * (k + 1)) * (2 * (k + 1) + 1)) := by
    ext k
    dsimp [fo]
    have hp1 : (1 / 2 : ℝ) ^ (2 * k + 2) = ((4 : ℝ) ^ (k + 1))⁻¹ := by
      calc
        (1 / 2 : ℝ) ^ (2 * k + 2) = ((1 / 2 : ℝ) ^ 2) ^ (k + 1) := by
          rw [← pow_mul]
          ring_nf
        _ = (4⁻¹ : ℝ) ^ (k + 1) := by norm_num
        _ = ((4 : ℝ) ^ (k + 1))⁻¹ := inv_pow 4 (k + 1)
    have hp2 : 2 * (1 / 2 : ℝ) ^ (2 * (k + 1) + 1) = ((4 : ℝ) ^ (k + 1))⁻¹ := by
      have hsplit : 2 * (k + 1) + 1 = (2 * k + 2) + 1 := by ring
      rw [hsplit, pow_succ, hp1]
      ring
    have hm1 : (0 : ℝ) < 2 * (k : ℝ) + 2 := by positivity
    have hm2 : (0 : ℝ) < 2 * (k : ℝ) + 3 := by positivity
    have h4 : (0 : ℝ) < (4 : ℝ) ^ (k + 1) := by positivity
    push_cast
    rw [← mul_div_assoc, hp1, hp2]
    field_simp
    ring
  rw [hterm] at hdiff
  have hval :
      (-Real.log (1 - 1 / 2) - Real.log (1 + 1 / 2)) / 2 -
          (Real.log (((1 : ℝ) + 1 / 2) / (1 - 1 / 2)) - 1) =
        1 + Real.log 2 - (3 / 2 : ℝ) * Real.log 3 := by
    have h1 : (1 : ℝ) - 1 / 2 = 2⁻¹ := by norm_num
    have h2 : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
    have h3 : ((1 : ℝ) + 1 / 2) / (1 - 1 / 2) = 3 := by norm_num
    rw [h3, h1, h2, Real.log_inv, Real.log_div (by norm_num) (by norm_num)]
    ring
  exact hval ▸ hdiff

/-- `tsum` form of `rampTwoSeries_hasSum`. -/
theorem rampTwoSeries_tsum :
    (∑' k : ℕ, (1 : ℝ) / ((4 : ℝ) ^ (k + 1) * (2 * (k + 1)) * (2 * (k + 1) + 1))) =
      1 + Real.log 2 - (3 / 2 : ℝ) * Real.log 3 :=
  rampTwoSeries_hasSum.tsum_eq

/-- Exact equivalence of the width-two explicit-ramp zero-mass cap `√2 * (3 C_0 - 2 S(2))`
with the closed form `widthTwoCapClosed = √2 * (3 log 3 - 2 log 2 - γ_E - log π)`. -/
theorem widthTwoCap_eq_from_rampTwo :
    Real.sqrt 2 * (3 * cZero - 2 * rampTwoExplicit) = widthTwoCapClosed := by
  unfold cZero rampTwoExplicit widthTwoCapClosed
  rw [rampTwoSeries_tsum]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlog4pi : Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num) hpi.ne']
    have h4 : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
    rw [h4, Real.log_pow]
    push_cast; ring
  have hlog2pi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) hpi.ne'
  rw [hlog4pi, hlog2pi]
  ring

alias widthTwoCap_eq_explicit_series := widthTwoCap_eq_from_rampTwo

/-! ## 4. Pure-Mathlib 14-Digit Certified Enclosure of `widthTwoMargin` -/

/-- `K`-term odd-power partial sum for `log((1 + u)/(1 - u))`. -/
def artanhPartial (u : ℝ) (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range K, 2 * (u ^ (2 * j + 1) / (2 * (j : ℝ) + 1))

/-- `K`-term upper enclosure for `log((1 + u)/(1 - u))` with geometric tail bound. -/
def artanhUpper (u : ℝ) (K : ℕ) : ℝ :=
  artanhPartial u K + 2 * (u ^ (2 * K + 1) / (2 * (K : ℝ) + 1)) / (1 - u ^ 2)

/-- Certified lower and upper enclosures for `log((1 + u)/(1 - u))` on `[0, 1)`. -/
theorem artanh_bounds_of_nonneg_of_lt_one {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (K : ℕ) :
    artanhPartial u K ≤ Real.log ((1 + u) / (1 - u)) ∧
      Real.log ((1 + u) / (1 - u)) ≤ artanhUpper u K := by
  have habs : |u| < 1 := by
    rw [abs_of_nonneg hu0]
    exact hu1
  let f : ℕ → ℝ := fun j => 2 * (u ^ (2 * j + 1) / (2 * (j : ℝ) + 1))
  have hf : HasSum f (Real.log ((1 + u) / (1 - u))) := hasSum_log_one_add_div_one_sub habs
  have hsplit : artanhPartial u K + ∑' m : ℕ, f (m + K) = Real.log ((1 + u) / (1 - u)) := by
    unfold artanhPartial
    rw [← hf.tsum_eq]
    exact hf.summable.sum_add_tsum_nat_add K
  have hf_shift : Summable (fun m : ℕ => f (m + K)) :=
    hf.summable.comp_injective (add_left_injective K)
  have htail_nonneg : 0 ≤ ∑' m : ℕ, f (m + K) := by
    refine tsum_nonneg (fun m => ?_)
    dsimp [f]
    positivity
  have hu2_lt : u ^ 2 < 1 := by nlinarith
  let c : ℝ := 2 * (u ^ (2 * K + 1) / (2 * (K : ℝ) + 1))
  have hgeom : HasSum (fun m : ℕ => c * (u ^ 2) ^ m) (c * (1 - u ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (sq_nonneg u) hu2_lt).mul_left c
  have hterm_le : ∀ m : ℕ, f (m + K) ≤ c * (u ^ 2) ^ m := by
    intro m
    dsimp [f, c]
    have hpow : u ^ (2 * (m + K) + 1) = u ^ (2 * K + 1) * (u ^ 2) ^ m := by
      have hexp : 2 * (m + K) + 1 = (2 * K + 1) + 2 * m := by ring
      rw [hexp, pow_add, pow_mul]
    have hden_pos : (0 : ℝ) < 2 * (K : ℝ) + 1 := by positivity
    have hden_le : 2 * (K : ℝ) + 1 ≤ 2 * ((m + K : ℕ) : ℝ) + 1 := by
      push_cast
      linarith
    have hnum_nonneg : 0 ≤ u ^ (2 * K + 1) * (u ^ 2) ^ m := by positivity
    rw [hpow]
    have hdiv :
        (u ^ (2 * K + 1) * (u ^ 2) ^ m) / (2 * ((m + K : ℕ) : ℝ) + 1) ≤
          (u ^ (2 * K + 1) * (u ^ 2) ^ m) / (2 * (K : ℝ) + 1) :=
      div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_le
    calc
      2 * ((u ^ (2 * K + 1) * (u ^ 2) ^ m) / (2 * ((m + K : ℕ) : ℝ) + 1))
          ≤ 2 * ((u ^ (2 * K + 1) * (u ^ 2) ^ m) / (2 * (K : ℝ) + 1)) := by linarith
      _ = 2 * (u ^ (2 * K + 1) / (2 * (K : ℝ) + 1)) * (u ^ 2) ^ m := by ring
  have htail_le : (∑' m : ℕ, f (m + K)) ≤ c / (1 - u ^ 2) := by
    rw [div_eq_mul_inv, ← hgeom.tsum_eq]
    exact Summable.tsum_le_tsum hterm_le hf_shift hgeom.summable
  unfold artanhUpper
  exact ⟨by linarith, by linarith⟩

/-- Euler–Maclaurin upper correction `-1/(2x) + 1/(12x^2) - 1/(120x^4) + 1/(252x^6)`. -/
def emUpperCorr (x : ℝ) : ℝ :=
  -1 / (2 * x) + 1 / (12 * x ^ 2) - 1 / (120 * x ^ 4) + 1 / (252 * x ^ 6)

/-- Euler–Maclaurin lower correction adding `-1/(240x^8)`. -/
def emLowerCorr (x : ℝ) : ℝ :=
  emUpperCorr x - 1 / (240 * x ^ 8)

/-- Strictly decreasing upper sequence converging to `eulerMascheroniConstant`. -/
def emUpper (n : ℕ) : ℝ :=
  (harmonic n : ℝ) - Real.log (n : ℝ) + emUpperCorr (n : ℝ)

/-- Strictly increasing lower sequence converging to `eulerMascheroniConstant`. -/
def emLower (n : ℕ) : ℝ :=
  (harmonic n : ℝ) - Real.log (n : ℝ) + emLowerCorr (n : ℝ)

/-- Strict decrease `emUpper (k + 1) < emUpper k` for every `k ≥ 1`. -/
theorem emUpper_succ_lt {k : ℕ} (hk : 1 ≤ k) : emUpper (k + 1) < emUpper k := by
  set m : ℝ := (k : ℝ) - 1
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr hk
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hk_eq : (k : ℝ) = m + 1 := by dsimp [m]; ring
  have hkp1_eq : ((k + 1 : ℕ) : ℝ) = m + 2 := by push_cast; linarith
  have hm1_pos : 0 < m + 1 := by linarith
  have hm2_pos : 0 < m + 2 := by linarith
  have h2m3_pos : 0 < 2 * m + 3 := by linarith
  set u : ℝ := 1 / (2 * m + 3)
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u < 1 := by
    dsimp [u]
    rw [div_lt_one h2m3_pos]
    linarith
  have hratio : (1 + u) / (1 - u) = (m + 2) / (m + 1) := by
    have h1mu : 1 - u ≠ 0 := by linarith
    rw [div_eq_iff h1mu]
    dsimp [u]
    field_simp
    ring
  have hlog_ge : artanhPartial u 4 ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) := by
    have h1 := (artanh_bounds_of_nonneg_of_lt_one hu0 hu1 4).1
    rw [hratio, Real.log_div hm2_pos.ne' hm1_pos.ne', ← hkp1_eq, ← hk_eq] at h1
    exact h1
  have hharm : (harmonic (k + 1) : ℝ) - (harmonic k : ℝ) = 1 / (m + 2) := by
    rw [harmonic_succ]
    push_cast
    rw [hk_eq]
    field_simp
    ring
  have hdiff_eq :
      emUpper k - emUpper (k + 1) =
        (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)) -
          (1 / (m + 2) + emUpperCorr (m + 2) - emUpperCorr (m + 1)) := by
    unfold emUpper
    rw [hk_eq, hkp1_eq]
    linarith [hharm]
  have hpoly :
      artanhPartial u 4 - (1 / (m + 2) + emUpperCorr (m + 2) - emUpperCorr (m + 1)) =
        (609678 + 4068252 * m + 12213945 * m ^ 2 + 21726720 * m ^ 3 +
          25359657 * m ^ 4 + 20294874 * m ^ 5 + 11277846 * m ^ 6 +
          4297104 * m ^ 7 + 1074402 * m ^ 8 + 159180 * m ^ 9 + 10612 * m ^ 10) /
        (2520 * (m + 1) ^ 6 * (m + 2) ^ 6 * (2 * m + 3) ^ 7) := by
    simp only [artanhPartial, Finset.sum_range_succ, Finset.sum_range_zero, emUpperCorr, u]
    push_cast
    field_simp
    ring
  have hpoly_pos :
      0 < (609678 + 4068252 * m + 12213945 * m ^ 2 + 21726720 * m ^ 3 +
          25359657 * m ^ 4 + 20294874 * m ^ 5 + 11277846 * m ^ 6 +
          4297104 * m ^ 7 + 1074402 * m ^ 8 + 159180 * m ^ 9 + 10612 * m ^ 10) /
        (2520 * (m + 1) ^ 6 * (m + 2) ^ 6 * (2 * m + 3) ^ 7) := by
    positivity
  linarith

/-- Strict increase `emLower k < emLower (k + 1)` for every `k ≥ 1`. -/
theorem emLower_lt_succ {k : ℕ} (hk : 1 ≤ k) : emLower k < emLower (k + 1) := by
  set m : ℝ := (k : ℝ) - 1
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr hk
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hk_eq : (k : ℝ) = m + 1 := by dsimp [m]; ring
  have hkp1_eq : ((k + 1 : ℕ) : ℝ) = m + 2 := by push_cast; linarith
  have hm1_pos : 0 < m + 1 := by linarith
  have hm2_pos : 0 < m + 2 := by linarith
  have h2m3_pos : 0 < 2 * m + 3 := by linarith
  set u : ℝ := 1 / (2 * m + 3)
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u < 1 := by
    dsimp [u]
    rw [div_lt_one h2m3_pos]
    linarith
  have hratio : (1 + u) / (1 - u) = (m + 2) / (m + 1) := by
    have h1mu : 1 - u ≠ 0 := by linarith
    rw [div_eq_iff h1mu]
    dsimp [u]
    field_simp
    ring
  have hlog_le : Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) ≤ artanhUpper u 4 := by
    have h2 := (artanh_bounds_of_nonneg_of_lt_one hu0 hu1 4).2
    rw [hratio, Real.log_div hm2_pos.ne' hm1_pos.ne', ← hkp1_eq, ← hk_eq] at h2
    exact h2
  have hharm : (harmonic (k + 1) : ℝ) - (harmonic k : ℝ) = 1 / (m + 2) := by
    rw [harmonic_succ]
    push_cast
    rw [hk_eq]
    field_simp
    ring
  have hdiff_eq :
      emLower (k + 1) - emLower k =
        (1 / (m + 2) + emLowerCorr (m + 2) - emLowerCorr (m + 1)) -
          (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)) := by
    unfold emLower
    rw [hk_eq, hkp1_eq]
    linarith [hharm]
  have h1mu2 : 1 - u ^ 2 = (4 * (m + 1) * (m + 2)) / (2 * m + 3) ^ 2 := by
    dsimp [u]
    field_simp
    ring
  have hpoly :
      (1 / (m + 2) + emLowerCorr (m + 2) - emLowerCorr (m + 1)) - artanhUpper u 4 =
        (61183089 + 483843186 * m + 1755509292 * m ^ 2 + 3864244320 * m ^ 3 +
          5747506632 * m ^ 4 + 6085329768 * m ^ 5 + 4702948488 * m ^ 6 +
          2673127224 * m ^ 7 + 1109059362 * m ^ 8 + 327558060 * m ^ 9 +
          65371464 * m ^ 10 + 7915320 * m ^ 11 + 439740 * m ^ 12) /
        (45360 * (m + 1) ^ 8 * (m + 2) ^ 8 * (2 * m + 3) ^ 7) := by
    unfold artanhUpper
    rw [h1mu2]
    simp only [artanhPartial, Finset.sum_range_succ, Finset.sum_range_zero,
      emLowerCorr, emUpperCorr, u]
    push_cast
    field_simp
    ring
  have hpoly_pos :
      0 < (61183089 + 483843186 * m + 1755509292 * m ^ 2 + 3864244320 * m ^ 3 +
          5747506632 * m ^ 4 + 6085329768 * m ^ 5 + 4702948488 * m ^ 6 +
          2673127224 * m ^ 7 + 1109059362 * m ^ 8 + 327558060 * m ^ 9 +
          65371464 * m ^ 10 + 7915320 * m ^ 11 + 439740 * m ^ 12) /
        (45360 * (m + 1) ^ 8 * (m + 2) ^ 8 * (2 * m + 3) ^ 7) := by
    positivity
  linarith

private lemma emUpper_le_of_le {N n : ℕ} (hN : 1 ≤ N) (hNn : N ≤ n) :
    emUpper n ≤ emUpper N := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNn
  clear hNn
  induction d with
  | zero => simp
  | succ d ih =>
    have hNd : 1 ≤ N + d := le_trans hN (Nat.le_add_right N d)
    exact (emUpper_succ_lt hNd).le.trans ih

private lemma emLower_le_of_le {N n : ℕ} (hN : 1 ≤ N) (hNn : N ≤ n) :
    emLower N ≤ emLower n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNn
  clear hNn
  induction d with
  | zero => simp
  | succ d ih =>
    have hNd : 1 ≤ N + d := le_trans hN (Nat.le_add_right N d)
    exact ih.trans (emLower_lt_succ hNd).le

private lemma tendsto_emUpper :
    Filter.Tendsto emUpper Filter.atTop (nhds Real.eulerMascheroniConstant) := by
  have hinv : Filter.Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  let p : ℝ → ℝ := fun r =>
    -(1 / 2 : ℝ) * r + (1 / 12 : ℝ) * r ^ 2 - (1 / 120 : ℝ) * r ^ 4 + (1 / 252 : ℝ) * r ^ 6
  have hp_cont : Continuous p := by continuity
  have hp0 : p 0 = 0 := by dsimp [p]; norm_num
  have hcorr : Filter.Tendsto (fun n : ℕ => emUpperCorr (n : ℝ)) Filter.atTop (nhds 0) := by
    have heq : (fun n : ℕ => emUpperCorr (n : ℝ)) = fun n : ℕ => p (((n : ℝ))⁻¹) := by
      ext n
      dsimp [emUpperCorr, p]
      simp only [inv_pow]
      ring
    rw [heq, ← hp0]
    exact (hp_cont.tendsto 0).comp hinv
  have hsum := Real.tendsto_eulerMascheroniSeq'.add hcorr
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : n ≠ 0 := by omega
  simp [Real.eulerMascheroniSeq', hn0, emUpper]

private lemma tendsto_emLower :
    Filter.Tendsto emLower Filter.atTop (nhds Real.eulerMascheroniConstant) := by
  have hinv : Filter.Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  let q : ℝ → ℝ := fun r => (1 / 240 : ℝ) * r ^ 8
  have hq_cont : Continuous q := by continuity
  have hq0 : q 0 = 0 := by dsimp [q]; norm_num
  have htail : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (240 * (n : ℝ) ^ 8)) Filter.atTop (nhds 0) := by
    have heq : (fun n : ℕ => (1 : ℝ) / (240 * (n : ℝ) ^ 8)) = fun n : ℕ => q (((n : ℝ))⁻¹) := by
      ext n
      dsimp [q]
      simp only [inv_pow]
      ring
    rw [heq, ← hq0]
    exact (hq_cont.tendsto 0).comp hinv
  have h := tendsto_emUpper.sub htail
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n _
  unfold emLower emUpper emLowerCorr
  ring

/-- Certified Euler–Maclaurin enclosure `emLower N ≤ γ_E ≤ emUpper N` for every `N ≥ 1`. -/
theorem eulerMascheroniConstant_bounds_of_pos {N : ℕ} (hN : 1 ≤ N) :
    emLower N ≤ Real.eulerMascheroniConstant ∧ Real.eulerMascheroniConstant ≤ emUpper N := by
  refine ⟨?_, ?_⟩
  · exact ge_of_tendsto tendsto_emLower
      (Filter.eventually_atTop.mpr ⟨N, fun n hn => emLower_le_of_le hN hn⟩)
  · exact le_of_tendsto tendsto_emUpper
      (Filter.eventually_atTop.mpr ⟨N, fun n hn => emUpper_le_of_le hN hn⟩)

/-- 17-digit rational enclosure of `√2`. -/
theorem sqrt_two_bounds_d17 :
    (141421356237309504 : ℝ) / 10 ^ 17 < Real.sqrt 2 ∧
      Real.sqrt 2 < (141421356237309505 : ℝ) / 10 ^ 17 := by
  refine ⟨?_, ?_⟩
  · rw [Real.lt_sqrt (by positivity)]
    norm_num
  · rw [Real.sqrt_lt' (by positivity)]
    norm_num

/-- 17-digit rational enclosure of `log 2` from `u = 1/3`, `K = 17`. -/
theorem log_two_bounds_d17 :
    (69314718055994530 : ℝ) / 10 ^ 17 < Real.log 2 ∧
      Real.log 2 < (69314718055994531 : ℝ) / 10 ^ 17 := by
  have h := artanh_bounds_of_nonneg_of_lt_one (u := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 17
  have hrat : ((1 : ℝ) + 1 / 3) / (1 - 1 / 3) = 2 := by norm_num
  rw [hrat] at h
  have hlo : (69314718055994530 : ℝ) / 10 ^ 17 < artanhPartial (1 / 3) 17 := by
    simp only [artanhPartial, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have hhi : artanhUpper (1 / 3) 17 < (69314718055994531 : ℝ) / 10 ^ 17 := by
    simp only [artanhUpper, artanhPartial, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  exact ⟨hlo.trans_le h.1, h.2.trans_lt hhi⟩

/-- 17-digit rational enclosure of `log (3 / 2)` from `u = 1/5`, `K = 12`. -/
theorem log_three_halves_bounds_d17 :
    (40546510810816438 : ℝ) / 10 ^ 17 < Real.log (3 / 2) ∧
      Real.log (3 / 2) < (40546510810816439 : ℝ) / 10 ^ 17 := by
  have h := artanh_bounds_of_nonneg_of_lt_one (u := (1 / 5 : ℝ)) (by norm_num) (by norm_num) 12
  have hrat : ((1 : ℝ) + 1 / 5) / (1 - 1 / 5) = 3 / 2 := by norm_num
  rw [hrat] at h
  have hlo : (40546510810816438 : ℝ) / 10 ^ 17 < artanhPartial (1 / 5) 12 := by
    simp only [artanhPartial, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have hhi : artanhUpper (1 / 5) 12 < (40546510810816439 : ℝ) / 10 ^ 17 := by
    simp only [artanhUpper, artanhPartial, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  exact ⟨hlo.trans_le h.1, h.2.trans_lt hhi⟩

/-- 17-digit rational enclosure of `log (π / 3)` from `Real.pi_gt_d20` and `Real.pi_lt_d20`. -/
theorem log_pi_div_three_bounds_d17 :
    (4611759718129046 : ℝ) / 10 ^ 17 < Real.log (Real.pi / 3) ∧
      Real.log (Real.pi / 3) < (4611759718129049 : ℝ) / 10 ^ 17 := by
  have hpi_lo : (314159265358979323 : ℝ) / 10 ^ 17 < Real.pi := by
    linarith [Real.pi_gt_d20]
  have hpi_hi : Real.pi < (314159265358979324 : ℝ) / 10 ^ 17 := by
    linarith [Real.pi_lt_d20]
  set uLo : ℝ := (2305471260895682 : ℝ) / 10 ^ 17
  set uHi : ℝ := (2305471260895683 : ℝ) / 10 ^ 17
  have hrat_lo : (1 + uLo) / (1 - uLo) < Real.pi / 3 := by
    have hnum : (1 + uLo) / (1 - uLo) < ((314159265358979323 : ℝ) / 10 ^ 17) / 3 := by
      dsimp [uLo]; norm_num
    linarith
  have hrat_hi : Real.pi / 3 < (1 + uHi) / (1 - uHi) := by
    have hnum : ((314159265358979324 : ℝ) / 10 ^ 17) / 3 < (1 + uHi) / (1 - uHi) := by
      dsimp [uHi]; norm_num
    linarith
  have hlog_mono_lo : Real.log ((1 + uLo) / (1 - uLo)) < Real.log (Real.pi / 3) :=
    Real.log_lt_log (by dsimp [uLo]; norm_num) hrat_lo
  have hlog_mono_hi : Real.log (Real.pi / 3) < Real.log ((1 + uHi) / (1 - uHi)) :=
    Real.log_lt_log (by linarith) hrat_hi
  have hb_lo := (artanh_bounds_of_nonneg_of_lt_one (u := uLo)
    (by dsimp [uLo]; norm_num) (by dsimp [uLo]; norm_num) 5).1
  have hb_hi := (artanh_bounds_of_nonneg_of_lt_one (u := uHi)
    (by dsimp [uHi]; norm_num) (by dsimp [uHi]; norm_num) 5).2
  have hnum_lo : (4611759718129046 : ℝ) / 10 ^ 17 < artanhPartial uLo 5 := by
    simp only [artanhPartial, Finset.sum_range_succ, Finset.sum_range_zero, uLo]
    norm_num
  have hnum_hi : artanhUpper uHi 5 < (4611759718129049 : ℝ) / 10 ^ 17 := by
    simp only [artanhUpper, artanhPartial, Finset.sum_range_succ, Finset.sum_range_zero, uHi]
    norm_num
  exact ⟨by linarith, by linarith⟩

private lemma harmonic_32_eq :
    (harmonic 32 : ℝ) = (586061125622639 : ℝ) / 144403552893600 := by
  have hq : harmonic 32 = (586061125622639 : ℚ) / 144403552893600 := by
    simp only [harmonic_succ, harmonic_zero]
    norm_num
  rw [hq]
  push_cast
  rfl

/-- Certified 15-digit enclosure of `eulerMascheroniConstant` evaluated at `N = 32 = 2^5`. -/
theorem eulerMascheroniConstant_bounds_d17 :
    (57721566490153285 : ℝ) / 10 ^ 17 < Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant < (57721566490153670 : ℝ) / 10 ^ 17 := by
  have hem := eulerMascheroniConstant_bounds_of_pos (N := 32) (by norm_num)
  have hlog32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    have h32 : (32 : ℝ) = 2 ^ (5 : ℕ) := by norm_num
    rw [h32, Real.log_pow]
    norm_num
  obtain ⟨hln2_lo, hln2_hi⟩ := log_two_bounds_d17
  have hlo : (57721566490153285 : ℝ) / 10 ^ 17 < emLower 32 := by
    unfold emLower emLowerCorr emUpperCorr
    push_cast
    rw [harmonic_32_eq, hlog32]
    have hcorr :
        (586061125622639 : ℝ) / 144403552893600 -
            5 * ((69314718055994531 : ℝ) / 10 ^ 17) +
            (-1 / (2 * 32) + 1 / (12 * 32 ^ 2) - 1 / (120 * 32 ^ 4) +
              1 / (252 * 32 ^ 6) - 1 / (240 * 32 ^ 8)) >
          (57721566490153285 : ℝ) / 10 ^ 17 := by
      norm_num
    linarith
  have hhi : emUpper 32 < (57721566490153670 : ℝ) / 10 ^ 17 := by
    unfold emUpper emUpperCorr
    push_cast
    rw [harmonic_32_eq, hlog32]
    have hcorr :
        (586061125622639 : ℝ) / 144403552893600 -
            5 * ((69314718055994530 : ℝ) / 10 ^ 17) +
            (-1 / (2 * 32) + 1 / (12 * 32 ^ 2) - 1 / (120 * 32 ^ 4) +
              1 / (252 * 32 ^ 6)) <
          (57721566490153670 : ℝ) / 10 ^ 17 := by
      norm_num
    linarith
  exact ⟨hlo.trans_le hem.1, hem.2.trans_lt hhi⟩

/-- Pure-Mathlib 14-digit certified rational enclosure of `widthTwoMargin`:
`0.21997921744308 < Δ_2 < 0.21997921744309`. -/
theorem widthTwoMargin_bounds_d14 :
    (21997921744308 : ℝ) / 10 ^ 14 < widthTwoMargin ∧
      widthTwoMargin < (21997921744309 : ℝ) / 10 ^ 14 := by
  have hmargin_eq :
      widthTwoMargin =
        Real.sqrt 2 *
          (6 - (2 * Real.log (3 / 2) - Real.log (Real.pi / 3) - Real.eulerMascheroniConstant)) - 8 := by
    unfold widthTwoMargin primeSquareBias2 widthTwoCapClosed
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have hlog32 : Real.log (3 / 2 : ℝ) = Real.log 3 - Real.log 2 :=
      Real.log_div (by norm_num) (by norm_num)
    have hlogpi3 : Real.log (Real.pi / 3) = Real.log Real.pi - Real.log 3 :=
      Real.log_div hpi.ne' (by norm_num)
    rw [hlog32, hlogpi3]
    ring
  rw [hmargin_eq]
  obtain ⟨hs2_lo, hs2_hi⟩ := sqrt_two_bounds_d17
  obtain ⟨hl32_lo, hl32_hi⟩ := log_three_halves_bounds_d17
  obtain ⟨hlpi_lo, hlpi_hi⟩ := log_pi_div_three_bounds_d17
  obtain ⟨hgam_lo, hgam_hi⟩ := eulerMascheroniConstant_bounds_d17
  set factor : ℝ :=
    6 - (2 * Real.log (3 / 2) - Real.log (Real.pi / 3) - Real.eulerMascheroniConstant)
  set fLo : ℝ :=
    6 - (2 * ((40546510810816439 : ℝ) / 10 ^ 17) -
      (4611759718129046 : ℝ) / 10 ^ 17 - (57721566490153285 : ℝ) / 10 ^ 17)
  set fHi : ℝ :=
    6 - (2 * ((40546510810816438 : ℝ) / 10 ^ 17) -
      (4611759718129049 : ℝ) / 10 ^ 17 - (57721566490153670 : ℝ) / 10 ^ 17)
  have hf_lo : fLo < factor := by dsimp [factor, fLo]; linarith
  have hf_hi : factor < fHi := by dsimp [factor, fHi]; linarith
  have hfLo_pos : 0 < fLo := by dsimp [fLo]; norm_num
  have hs2_pos : 0 < Real.sqrt 2 := by positivity
  refine ⟨?_, ?_⟩
  · have hmul : ((141421356237309504 : ℝ) / 10 ^ 17) * fLo < Real.sqrt 2 * factor :=
      mul_lt_mul hs2_lo hf_lo.le hfLo_pos hs2_pos.le
    have hnum :
        (21997921744308 : ℝ) / 10 ^ 14 <
          ((141421356237309504 : ℝ) / 10 ^ 17) * fLo - 8 := by
      dsimp [fLo]; norm_num
    linarith
  · have hmul : Real.sqrt 2 * factor < ((141421356237309505 : ℝ) / 10 ^ 17) * fHi :=
      mul_lt_mul hs2_hi hf_hi.le (hfLo_pos.trans hf_lo) (by positivity)
    have hnum :
        ((141421356237309505 : ℝ) / 10 ^ 17) * fHi - 8 <
          (21997921744309 : ℝ) / 10 ^ 14 := by
      dsimp [fHi]; norm_num
    linarith

/-- Certified 12-digit rational enclosure `0.219979217443 < Δ_2 < 0.219979217444`. -/
theorem widthTwoMargin_bounds :
    (219979217443 : ℝ) / 10 ^ 12 < widthTwoMargin ∧
      widthTwoMargin < (219979217444 : ℝ) / 10 ^ 12 := by
  obtain ⟨hlo, hhi⟩ := widthTwoMargin_bounds_d14
  exact ⟨by linarith, by linarith⟩

alias widthTwoMargin_enclosure_d12 := widthTwoMargin_bounds

/-- Strict improvement over the 512-pair certified lower bound `0.211697`. -/
theorem widthTwoMargin_gt_ladyElinor :
    (211697 : ℝ) / 10 ^ 6 < widthTwoMargin := by
  linarith [widthTwoMargin_bounds.1]

/-- Unconditional 14-digit width-two post-critical-line margin bound from the explicit ramp cap. -/
theorem widthTwo_postCriticalLine_margin_d14 {ι : Type*} {ρ : ι → ℂ}
    (hsum : Summable (fun i => (tentDephased 2 (ρ i)).re))
    (hmass :
      (∑' i, (tentDephased 2 (ρ i)).re) = Real.sqrt 2 * (3 * cZero - 2 * rampTwoExplicit))
    (hoff : ∀ i, (ρ i).re ≠ 1 / 2 →
      ∃ e : ℝ, 0 < e ∧ e ≤ (ρ i).re ∧ e ≤ 1 - (ρ i).re ∧
        6 ≤ |(ρ i).im| ∧ 1 ≤ 6 * Real.log |(ρ i).im| * e) :
    (21997921744308 : ℝ) / 10 ^ 14 <
      primeSquareBias2 - ∑' i, (if (ρ i).re = 1 / 2 then ‖tentKernel 2 (ρ i)‖ else 0) := by
  rw [widthTwoCap_eq_from_rampTwo] at hmass
  have hcap := criticalLine_tent_sum_le_cap (by norm_num : (1 : ℝ) < 2) hsum hmass hoff
  have hlo := widthTwoMargin_bounds_d14.1
  unfold widthTwoMargin at hlo
  linarith

/-- Unconditional width-two post-critical-line margin bound `0.219979217443 < B_2 - ∑_{Re ρ = 1/2} ‖H_2(ρ)‖`
from the explicit single-ramp formula `√2 * (3 C_0 - 2 S(2))`. -/
theorem widthTwo_postCriticalLine_margin_unconditional {ι : Type*} {ρ : ι → ℂ}
    (hsum : Summable (fun i => (tentDephased 2 (ρ i)).re))
    (hmass :
      (∑' i, (tentDephased 2 (ρ i)).re) = Real.sqrt 2 * (3 * cZero - 2 * rampTwoExplicit))
    (hoff : ∀ i, (ρ i).re ≠ 1 / 2 →
      ∃ e : ℝ, 0 < e ∧ e ≤ (ρ i).re ∧ e ≤ 1 - (ρ i).re ∧
        6 ≤ |(ρ i).im| ∧ 1 ≤ 6 * Real.log |(ρ i).im| * e) :
    (219979217443 : ℝ) / 10 ^ 12 <
      primeSquareBias2 - ∑' i, (if (ρ i).re = 1 / 2 then ‖tentKernel 2 (ρ i)‖ else 0) := by
  linarith [widthTwo_postCriticalLine_margin_d14 hsum hmass hoff]

/-- Unconditional width-two post-critical-line margin bound stated directly against `widthTwoCapClosed`. -/
theorem widthTwo_postCriticalLine_margin_from_closedCap {ι : Type*} {ρ : ι → ℂ}
    (hsum : Summable (fun i => (tentDephased 2 (ρ i)).re))
    (hmass : (∑' i, (tentDephased 2 (ρ i)).re) = widthTwoCapClosed)
    (hoff : ∀ i, (ρ i).re ≠ 1 / 2 →
      ∃ e : ℝ, 0 < e ∧ e ≤ (ρ i).re ∧ e ≤ 1 - (ρ i).re ∧
        6 ≤ |(ρ i).im| ∧ 1 ≤ 6 * Real.log |(ρ i).im| * e) :
    (219979217443 : ℝ) / 10 ^ 12 <
      primeSquareBias2 - ∑' i, (if (ρ i).re = 1 / 2 then ‖tentKernel 2 (ρ i)‖ else 0) := by
  rw [← widthTwoCap_eq_from_rampTwo] at hmass
  exact widthTwo_postCriticalLine_margin_unconditional hsum hmass hoff

#print axioms tentDephased_eq_mul_tentKernel
#print axioms tentDephased_re_eq_companionRe
#print axioms tentDephased_criticalLine_eq_norm
#print axioms tentKernel_criticalLine_norm_pos
#print axioms tentDephased_symm
#print axioms criticalLine_tent_sum_le_cap
#print axioms criticalLine_tent_sum_eq_cap_iff
#print axioms rampTwoSeries_tsum
#print axioms widthTwoCap_eq_from_rampTwo
#print axioms eulerMascheroniConstant_bounds_d17
#print axioms widthTwoMargin_bounds_d14
#print axioms widthTwoMargin_bounds
#print axioms widthTwoMargin_gt_ladyElinor
#print axioms widthTwo_postCriticalLine_margin_unconditional

end TentWidthTwoMargin
