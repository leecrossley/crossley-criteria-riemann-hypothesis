import Mathlib
import TentDigamma
import TentComplex
import TentWidthTwoMargin
import ZetaCount.Final
import ZetaCount.Order
import ZetaExplicit.Factor
import ZetaExplicit.Height
import ZetaExplicit.LogDeriv
import ZetaExplicit.Rect
import ZetaStrip.Factor
import ZetaStrip.Final

/-!
# The critical-line mass identity

For `b > 1` let `P_b(s) = √b ((b + 1) - b^s - b^(1-s)) / (s (1 - s))`, which is
`TentZeroBudget.companion` and `TentWidthTwoMargin.tentDephased`. Over the nontrivial zeros of
`ζ`, counted with multiplicity,

  `∑_ρ P_b(ρ) = L_b^* = √b ((b + 1) C_0 - 2 S(b))`,

with `C_0 = 2 + γ - log 4π` (`TentWidthTwoMargin.cZero`) and
`S(b) = b (1 + γ - log b) - log 2π + ∑_{k ≥ 1} b^(-2k) / (2k (2k + 1)) + ∑_{n ≤ b} Λ(n) (b/n - 1)`.

The proof is a contour argument with `Ξ(s) = s (s - 1) Λ(s)`, an entire function whose zeros are
the nontrivial zeros of `ζ` with their multiplicities. The kernel `P_b` is entire and symmetric
under `s ↦ 1 - s`, so the boundary integral of `Ξ'/Ξ · P_b` over `[-1, 2] × [-T, T]` folds onto
the line `re s = 2`. On that line
`Ξ'/Ξ = ζ'/ζ + 1/(s - 1) + κ + ∑_{m ≥ 1} (1/(2(m + 1)) - 1/(s + 2m))`, from the digamma partial
fractions of `TentDigamma`, and each term is integrated by closing the contour to the left or to
the right. The horizontal sides use the good heights of `ZetaStrip` and the zero count of
`ZetaCount`. Mathlib and the project's own modules only.

Main results:
* `hasSum_mass`: the mass identity for the family `zero : ZeroIndex → ℂ`, which lists every
  nontrivial zero `ρ` exactly `mult ρ` times.
* `line_mass_bound_and_equality_zeta`: `∑_{re ρ = 1/2} |H_b(ρ)| ≤ L_b^*`, with equality exactly
  when every nontrivial zero lies on the critical line, under the strip and height condition of
  `TentZeroBudget.line_mass_bound_and_equality` and no other hypothesis.
* `widthTwo_margin_zeta`: `B_2 - ∑_{re ρ = 1/2} |H_2(ρ)| > 0.219979217443` under the classical
  logarithmic strip above height `6`.
-/

noncomputable section

namespace TentMassIdentity

section VerticalLines

open Complex Set Filter Topology MeasureTheory
open ZetaExplicit

/-! ## 1. Integrals along vertical lines -/

lemma abs_im_le_norm_line (c t : ℝ) : |t| ≤ ‖(c : ℂ) + t * I‖ := by
  have h := Complex.abs_im_le_norm ((c : ℂ) + t * I)
  simpa using h

/-- Integrability on a vertical line from continuity and an inverse-square tail bound. -/
theorem integrable_line {F : ℂ → ℂ} {c A R : ℝ} (hA : 0 ≤ A)
    (hcont : Continuous fun t : ℝ => F (c + t * I))
    (hbound : ∀ t : ℝ, R ≤ |t| → ‖F (c + t * I)‖ ≤ A / t ^ 2) :
    Integrable fun t : ℝ => F (c + t * I) := by
  set R' : ℝ := max R 1 with hR'
  have hR'1 : 1 ≤ R' := le_max_right R 1
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -R') (b := R')).exists_bound_of_continuousOn
    hcont.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨by linarith, by linarith⟩)
  set K : ℝ := M * (1 + R' ^ 2) + 2 * A with hK
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul K) hcont.aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  have hpos : 0 < 1 + t ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  have hF0 := norm_nonneg (F (c + t * I))
  by_cases ht : |t| ≤ R'
  · have h1 := hM t ⟨by linarith [(abs_le.mp ht).1], (abs_le.mp ht).2⟩
    have h2 : t ^ 2 ≤ R' ^ 2 := by
      rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg t) ht 2
    nlinarith
  · rw [not_le] at ht
    have h1 : R ≤ |t| := (le_max_left R 1).trans ht.le
    have ht1 : 1 ≤ t ^ 2 := by
      rw [← sq_abs t]; nlinarith
    have h3 : ‖F (c + t * I)‖ * t ^ 2 ≤ A := by
      have h2 := hbound t h1
      rwa [le_div_iff₀ (by positivity)] at h2
    nlinarith

lemma tendsto_six_mul_div {A : ℝ} : Tendsto (fun T : ℝ => 6 * A / T) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop tendsto_id

lemma mul_eq_of_I_mul_eq {x y : ℂ} (h : I * x = 2 * Real.pi * I * y) : x = 2 * Real.pi * y := by
  have hI : I ≠ 0 := I_ne_zero
  apply mul_left_cancel₀ hI
  rw [h]; ring

/-- **Closing to the left.** If `F` is a finite sum of simple poles `H a s / (s - a)` on the
half-plane `re s ≤ c` (poles strictly to the left of the line) and decays like `‖s‖⁻²` there, the
integral along `re s = c` is `2π ∑ H a a`. -/
theorem integral_line_eq_residues {F : ℂ → ℂ} {c : ℝ} (P : Finset ℂ) (H : ℂ → ℂ → ℂ)
    (hH : ∀ a ∈ P, Differentiable ℂ (H a)) (hP : ∀ a ∈ P, a.re < c)
    (hF : ∀ s : ℂ, s.re ≤ c → s ∉ P → F s = ∑ a ∈ P, H a s / (s - a))
    {A R : ℝ} (hA : 0 ≤ A) (hbound : ∀ s : ℂ, s.re ≤ c → R ≤ ‖s‖ → ‖F s‖ ≤ A / ‖s‖ ^ 2)
    (hint : Integrable fun t : ℝ => F (c + t * I)) :
    ∫ t : ℝ, F (c + t * I) = 2 * Real.pi * ∑ a ∈ P, H a a := by
  set B : ℝ := ∑ a ∈ P, ‖a‖ with hB
  have hBa : ∀ a ∈ P, ‖a‖ ≤ B := fun a ha =>
    Finset.single_le_sum (f := fun b => ‖b‖) (fun b _ => norm_nonneg b) ha
  set T₀ : ℝ := max (max R 1) (max (B + 1) (|c| + 1)) with hT₀
  have key : ∀ T : ℝ, T₀ ≤ T →
      ‖I * (∫ y in (-T)..T, F (c + y * I)) - 2 * Real.pi * I * ∑ a ∈ P, H a a‖ ≤ 6 * A / T := by
    intro T hT
    have hT1 : 1 ≤ T := (le_max_right R 1).trans ((le_max_left _ _).trans hT)
    have hTR : R ≤ T := (le_max_left R 1).trans ((le_max_left _ _).trans hT)
    have hTB : B + 1 ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
    have hTc : |c| + 1 ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans hT)
    have hc1 : c ≤ |c| := le_abs_self c
    have hc2 : -|c| ≤ c := neg_abs_le c
    have hT0 : 0 < T := by linarith
    have hxle : -T ≤ c := by linarith
    have hyle : -T ≤ T := by linarith
    have hres := rectInt_eq_sum_residues (x₁ := -T) (x₂ := c) (y₁ := -T) (y₂ := T) hxle hyle
      isOpen_univ (subset_univ _) P H (fun a ha => (hH a ha).differentiableOn) ?_ (F := F) ?_
    · unfold rectInt at hres
      have e : I * (∫ y in (-T)..T, F (c + y * I)) - 2 * Real.pi * I * ∑ a ∈ P, H a a =
          -(∫ x in (-T)..c, F (x + ((-T : ℝ) : ℂ) * I)) + (∫ x in (-T)..c, F (x + (T : ℂ) * I)) +
            I * ∫ y in (-T)..T, F (((-T : ℝ) : ℂ) + y * I) := by
        rw [← hres]; ring
      rw [e]
      have hsq : 0 < T ^ 2 := by positivity
      have hedge : ∀ s : ℂ, s.re ≤ c → T ≤ ‖s‖ → ‖F s‖ ≤ A / T ^ 2 := by
        intro s hs1 hs2
        refine (hbound s hs1 (hTR.trans hs2)).trans ?_
        exact div_le_div_of_nonneg_left hA hsq (pow_le_pow_left₀ hT0.le hs2 2)
      have hb1 : ‖∫ x in (-T)..c, F (x + ((-T : ℝ) : ℂ) * I)‖ ≤ A / T ^ 2 * |c - -T| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
        rw [uIoc_of_le hxle] at hx
        refine hedge _ (by simpa using hx.2) ?_
        have h := abs_im_le_norm_line x (-T)
        rwa [abs_neg, abs_of_pos hT0] at h
      have hb2 : ‖∫ x in (-T)..c, F (x + (T : ℂ) * I)‖ ≤ A / T ^ 2 * |c - -T| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
        rw [uIoc_of_le hxle] at hx
        refine hedge _ (by simpa using hx.2) ?_
        have h := abs_im_le_norm_line x T
        rwa [abs_of_pos hT0] at h
      have hb3 : ‖∫ y in (-T)..T, F (((-T : ℝ) : ℂ) + y * I)‖ ≤ A / T ^ 2 * |T - -T| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun y _ => ?_
        refine hedge _ (by simp; linarith) ?_
        have h := Complex.abs_re_le_norm (((-T : ℝ) : ℂ) + y * I)
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero, abs_neg, abs_of_pos hT0] at h
        exact h
      have habs1 : |c - -T| ≤ 2 * T := by rw [abs_le]; constructor <;> linarith
      have habs2 : |T - -T| = 2 * T := by rw [abs_of_pos (by linarith)]; ring
      calc ‖-(∫ x in (-T)..c, F (x + ((-T : ℝ) : ℂ) * I)) + (∫ x in (-T)..c, F (x + (T : ℂ) * I)) +
            I * ∫ y in (-T)..T, F (((-T : ℝ) : ℂ) + y * I)‖
          ≤ ‖∫ x in (-T)..c, F (x + ((-T : ℝ) : ℂ) * I)‖ + ‖∫ x in (-T)..c, F (x + (T : ℂ) * I)‖ +
              ‖∫ y in (-T)..T, F (((-T : ℝ) : ℂ) + y * I)‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, Complex.norm_I, one_mul]
            gcongr
            refine (norm_add_le _ _).trans ?_
            rw [norm_neg]
        _ ≤ A / T ^ 2 * (2 * T) + A / T ^ 2 * (2 * T) + A / T ^ 2 * (2 * T) := by
            have hAT : 0 ≤ A / T ^ 2 := by positivity
            gcongr
            · exact hb1.trans (mul_le_mul_of_nonneg_left habs1 hAT)
            · exact hb2.trans (mul_le_mul_of_nonneg_left habs1 hAT)
            · rw [← habs2]; exact hb3
        _ = 6 * A / T := by field_simp; ring
    · intro a ha
      have h1 := hBa a ha
      have hre := Complex.abs_re_le_norm a
      have him := Complex.abs_im_le_norm a
      refine ⟨by linarith [(abs_le.mp hre).1], hP a ha, by linarith [(abs_le.mp him).1],
        by linarith [(abs_le.mp him).2]⟩
    · intro s hs
      obtain ⟨h1, h2, h3, h4, h5⟩ := hs
      refine hF s h2 fun hsP => ?_
      have h6 := hBa s hsP
      have hre := Complex.abs_re_le_norm s
      have him := Complex.abs_im_le_norm s
      have h7 := hP s hsP
      rcases h5 with h | h | h | h
      · linarith [(abs_le.mp hre).1]
      · linarith
      · linarith [(abs_le.mp him).1]
      · linarith [(abs_le.mp him).2]
  have hlim1 : Tendsto (fun T : ℝ => I * ∫ y in (-T)..T, F (c + y * I)) atTop
      (𝓝 (I * ∫ t : ℝ, F (c + t * I))) :=
    (intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id).const_mul I
  have hlim2 : Tendsto (fun T : ℝ => I * ∫ y in (-T)..T, F (c + y * I)) atTop
      (𝓝 (2 * Real.pi * I * ∑ a ∈ P, H a a)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _)
      ((eventually_ge_atTop T₀).mono fun T hT => key T hT) tendsto_six_mul_div
  exact mul_eq_of_I_mul_eq (tendsto_nhds_unique hlim1 hlim2)

/-- **Closing to the right.** A function holomorphic on `c ≤ re s` that decays like `‖s‖⁻²` there
has zero integral along `re s = c`. -/
theorem integral_line_eq_zero {F : ℂ → ℂ} {c : ℝ}
    (hd : ∀ s : ℂ, c ≤ s.re → DifferentiableAt ℂ F s)
    {A R : ℝ} (hA : 0 ≤ A) (hbound : ∀ s : ℂ, c ≤ s.re → R ≤ ‖s‖ → ‖F s‖ ≤ A / ‖s‖ ^ 2)
    (hint : Integrable fun t : ℝ => F (c + t * I)) :
    ∫ t : ℝ, F (c + t * I) = 0 := by
  set T₀ : ℝ := max (max R 1) (|c| + 1) with hT₀
  have key : ∀ T : ℝ, T₀ ≤ T → ‖I * (∫ y in (-T)..T, F (c + y * I)) - 2 * Real.pi * I * 0‖ ≤
      6 * A / T := by
    intro T hT
    have hT1 : 1 ≤ T := (le_max_right R 1).trans ((le_max_left _ _).trans hT)
    have hTR : R ≤ T := (le_max_left R 1).trans ((le_max_left _ _).trans hT)
    have hTc : |c| + 1 ≤ T := (le_max_right _ _).trans hT
    have hc1 : c ≤ |c| := le_abs_self c
    have hc2 : -|c| ≤ c := neg_abs_le c
    have hT0 : 0 < T := by linarith
    have hxle : c ≤ T := by linarith
    have hyle : -T ≤ T := by linarith
    have hzero := rectInt_eq_zero (x₁ := c) (x₂ := T) (y₁ := -T) (y₂ := T) hxle hyle (f := F)
      (fun s hs => (hd s hs.1).differentiableWithinAt)
    unfold rectInt at hzero
    have e : I * (∫ y in (-T)..T, F (c + y * I)) - 2 * Real.pi * I * 0 =
        (∫ x in c..T, F (x + ((-T : ℝ) : ℂ) * I)) - (∫ x in c..T, F (x + (T : ℂ) * I)) +
          I * ∫ y in (-T)..T, F ((T : ℂ) + y * I) := by
      rw [mul_zero, sub_zero]; linear_combination -hzero
    rw [e]
    have hsq : 0 < T ^ 2 := by positivity
    have hedge : ∀ s : ℂ, c ≤ s.re → T ≤ ‖s‖ → ‖F s‖ ≤ A / T ^ 2 := by
      intro s hs1 hs2
      refine (hbound s hs1 (hTR.trans hs2)).trans ?_
      exact div_le_div_of_nonneg_left hA hsq (pow_le_pow_left₀ hT0.le hs2 2)
    have hb1 : ‖∫ x in c..T, F (x + ((-T : ℝ) : ℂ) * I)‖ ≤ A / T ^ 2 * |T - c| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
      rw [uIoc_of_le hxle] at hx
      refine hedge _ (by simpa using hx.1.le) ?_
      have h := abs_im_le_norm_line x (-T)
      rwa [abs_neg, abs_of_pos hT0] at h
    have hb2 : ‖∫ x in c..T, F (x + (T : ℂ) * I)‖ ≤ A / T ^ 2 * |T - c| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
      rw [uIoc_of_le hxle] at hx
      refine hedge _ (by simpa using hx.1.le) ?_
      have h := abs_im_le_norm_line x T
      rwa [abs_of_pos hT0] at h
    have hb3 : ‖∫ y in (-T)..T, F ((T : ℂ) + y * I)‖ ≤ A / T ^ 2 * |T - -T| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun y _ => ?_
      refine hedge _ (by simp; linarith) ?_
      have h := Complex.abs_re_le_norm ((T : ℂ) + y * I)
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, abs_of_pos hT0] at h
      exact h
    have habs1 : |T - c| ≤ 2 * T := by rw [abs_le]; constructor <;> linarith
    have habs2 : |T - -T| = 2 * T := by rw [abs_of_pos (by linarith)]; ring
    calc ‖(∫ x in c..T, F (x + ((-T : ℝ) : ℂ) * I)) - (∫ x in c..T, F (x + (T : ℂ) * I)) +
          I * ∫ y in (-T)..T, F ((T : ℂ) + y * I)‖
        ≤ ‖∫ x in c..T, F (x + ((-T : ℝ) : ℂ) * I)‖ + ‖∫ x in c..T, F (x + (T : ℂ) * I)‖ +
            ‖∫ y in (-T)..T, F ((T : ℂ) + y * I)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, Complex.norm_I, one_mul]
          gcongr
          exact norm_sub_le _ _
      _ ≤ A / T ^ 2 * (2 * T) + A / T ^ 2 * (2 * T) + A / T ^ 2 * (2 * T) := by
          have hAT : 0 ≤ A / T ^ 2 := by positivity
          gcongr
          · exact hb1.trans (mul_le_mul_of_nonneg_left habs1 hAT)
          · exact hb2.trans (mul_le_mul_of_nonneg_left habs1 hAT)
          · rw [← habs2]; exact hb3
      _ = 6 * A / T := by field_simp; ring
  have hlim1 : Tendsto (fun T : ℝ => I * ∫ y in (-T)..T, F (c + y * I)) atTop
      (𝓝 (I * ∫ t : ℝ, F (c + t * I))) :=
    (intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id).const_mul I
  have hlim2 : Tendsto (fun T : ℝ => I * ∫ y in (-T)..T, F (c + y * I)) atTop
      (𝓝 (2 * Real.pi * I * 0)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _)
      ((eventually_ge_atTop T₀).mono fun T hT => key T hT) tendsto_six_mul_div
  have h := mul_eq_of_I_mul_eq (tendsto_nhds_unique hlim1 hlim2)
  rw [h, mul_zero]

end VerticalLines

section LineResidues

open Complex Set Filter Topology MeasureTheory
open TentWidthTwoMargin

/-! ## 2. Residues of the kernels on the line `re s = 2` -/

lemma two_add_re (t : ℝ) : ((2 : ℂ) + t * I).re = 2 := by simp

lemma ne_zero_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) : s ≠ 0 := by
  rintro rfl; norm_num at hs

lemma ne_one_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) : s ≠ 1 := by
  rintro rfl; norm_num at hs

lemma half_le_norm_sub {s a : ℂ} (h : 2 * ‖a‖ ≤ ‖s‖) : ‖s‖ / 2 ≤ ‖s - a‖ := by
  have := norm_sub_norm_le s a; linarith

lemma half_le_norm_sub_one {s : ℂ} (hs : 2 ≤ ‖s‖) : ‖s‖ / 2 ≤ ‖s - 1‖ :=
  half_le_norm_sub (by rw [norm_one]; linarith)

lemma norm_sum_div_le (P : Finset ℂ) (κ : ℂ → ℂ) {s : ℂ}
    (hs : 2 * ∑ a ∈ P, ‖a‖ ≤ ‖s‖) (hs0 : 0 < ‖s‖) :
    ‖∑ a ∈ P, κ a / (s - a)‖ ≤ 2 * (∑ a ∈ P, ‖κ a‖) / ‖s‖ := by
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_le_sum fun a ha => ?_
  have ha' : ‖a‖ ≤ ∑ b ∈ P, ‖b‖ :=
    Finset.single_le_sum (f := fun b => ‖b‖) (fun b _ => norm_nonneg b) ha
  have hsa : ‖s‖ / 2 ≤ ‖s - a‖ := half_le_norm_sub (by linarith)
  rw [norm_div]
  calc ‖κ a‖ / ‖s - a‖ ≤ ‖κ a‖ / (‖s‖ / 2) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hsa
    _ = 2 * ‖κ a‖ / ‖s‖ := by field_simp

lemma norm_dslope_le {E : ℂ → ℂ} {M : ℝ} (hEb : ∀ s : ℂ, s.re ≤ 2 → ‖E s‖ ≤ M) {s : ℂ}
    (hs : s.re ≤ 2) (hs2 : 2 ≤ ‖s‖) : ‖dslope E 1 s‖ ≤ 4 * M / ‖s‖ := by
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs2
  have hsub := half_le_norm_sub_one hs2
  have hpos : 0 < ‖s - 1‖ := by linarith
  have h1 : ‖E 1‖ ≤ M := hEb 1 (by norm_num)
  have hM : 0 ≤ M := (norm_nonneg _).trans h1
  rw [dslope_of_ne _ hs1, slope_def_field, norm_div]
  have hnum : ‖E s - E 1‖ ≤ 2 * M := (norm_sub_le _ _).trans (by linarith [hEb s hs])
  calc ‖E s - E 1‖ / ‖s - 1‖ ≤ 2 * M / (‖s‖ / 2) :=
        div_le_div₀ (by positivity) hnum (by linarith) hsub
    _ = 4 * M / ‖s‖ := by field_simp; ring

lemma continuous_line {f : ℂ → ℂ} (hf : ∀ s : ℂ, 2 ≤ s.re → ContinuousAt f s) :
    Continuous fun t : ℝ => f (2 + t * I) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact ContinuousAt.comp (f := fun t : ℝ => (2 : ℂ) + t * I) (hf _ (by simp)) (by fun_prop)

lemma sq_le_norm_line_sq (t : ℝ) : t ^ 2 ≤ ‖(2 : ℂ) + t * I‖ ^ 2 := by
  have h := abs_im_le_norm_line 2 t
  push_cast at h
  rw [← sq_abs t]
  exact pow_le_pow_left₀ (abs_nonneg t) h 2

lemma line_tail {G : ℂ → ℂ} {A R : ℝ} (hA : 0 ≤ A)
    (hG : ∀ s : ℂ, s.re = 2 → R ≤ ‖s‖ → ‖G s‖ ≤ A / ‖s‖ ^ 2) {t : ℝ} (ht : max R 1 ≤ |t|) :
    ‖G (2 + t * I)‖ ≤ A / t ^ 2 := by
  have h1 := abs_im_le_norm_line 2 t
  push_cast at h1
  have ht0 : 0 < t ^ 2 := by
    have : 1 ≤ |t| := (le_max_right R 1).trans ht
    rw [← sq_abs t]; positivity
  refine (hG _ (two_add_re t) ((le_max_left R 1).trans (ht.trans h1))).trans ?_
  exact div_le_div_of_nonneg_left hA ht0 (sq_le_norm_line_sq t)

/-- Residues to the left of the line for `dslope E 1 · ∑ κ a / (s - a)`. -/
theorem integral_dslope_mul {E : ℂ → ℂ} (hE : Differentiable ℂ E) {M : ℝ}
    (hEb : ∀ s : ℂ, s.re ≤ 2 → ‖E s‖ ≤ M) (P : Finset ℂ) (κ : ℂ → ℂ)
    (hP : ∀ a ∈ P, a.re < 2) :
    Integrable (fun t : ℝ => dslope E 1 (2 + t * I) * ∑ a ∈ P, κ a / (2 + t * I - a)) ∧
    ∫ t : ℝ, dslope E 1 (2 + t * I) * ∑ a ∈ P, κ a / (2 + t * I - a) =
      2 * Real.pi * ∑ a ∈ P, κ a * dslope E 1 a := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hEb 1 (by norm_num))
  have hD : Differentiable ℂ (dslope E 1) := by
    have h := (Complex.differentiableOn_dslope (f := E) (c := 1) (s := univ)
      Filter.univ_mem).mpr hE.differentiableOn
    exact fun s => (h s (mem_univ s)).differentiableAt Filter.univ_mem
  set B : ℝ := ∑ a ∈ P, ‖a‖ with hB
  set Kκ : ℝ := ∑ a ∈ P, ‖κ a‖ with hKκ
  have hKκ0 : 0 ≤ Kκ := Finset.sum_nonneg fun a _ => norm_nonneg _
  set A : ℝ := 4 * M * (2 * Kκ) with hA
  have hA0 : 0 ≤ A := by positivity
  set R : ℝ := max 2 (2 * B) with hR
  have hbound : ∀ s : ℂ, s.re ≤ 2 → R ≤ ‖s‖ →
      ‖dslope E 1 s * ∑ a ∈ P, κ a / (s - a)‖ ≤ A / ‖s‖ ^ 2 := by
    intro s hs hsR
    have hs2 : 2 ≤ ‖s‖ := (le_max_left _ _).trans hsR
    have hsB : 2 * B ≤ ‖s‖ := (le_max_right _ _).trans hsR
    have hs0 : 0 < ‖s‖ := by linarith
    rw [norm_mul]
    calc ‖dslope E 1 s‖ * ‖∑ a ∈ P, κ a / (s - a)‖ ≤ (4 * M / ‖s‖) * (2 * Kκ / ‖s‖) :=
          mul_le_mul (norm_dslope_le hEb hs hs2) (norm_sum_div_le P κ hsB hs0) (norm_nonneg _)
            (by positivity)
      _ = A / ‖s‖ ^ 2 := by rw [hA]; ring
  have hcont : Continuous fun t : ℝ => dslope E 1 (2 + t * I) * ∑ a ∈ P, κ a / (2 + t * I - a) := by
    refine continuous_line (f := fun s => dslope E 1 s * ∑ a ∈ P, κ a / (s - a)) fun s hs => ?_
    refine (hD s).continuousAt.mul (tendsto_finsetSum P fun a ha => ?_)
    refine continuousAt_const.div (by fun_prop) (sub_ne_zero.mpr ?_)
    rintro rfl; linarith [hP s ha]
  have hint : Integrable fun t : ℝ => dslope E 1 (2 + t * I) * ∑ a ∈ P, κ a / (2 + t * I - a) := by
    have h := integrable_line (F := fun s => dslope E 1 s * ∑ a ∈ P, κ a / (s - a)) (c := 2)
      (R := max R 1) hA0 (by simpa using hcont) fun t ht => by
        simpa using line_tail (G := fun s => dslope E 1 s * ∑ a ∈ P, κ a / (s - a)) hA0
          (fun s hs hsR => hbound s hs.le hsR) ht
    simpa using h
  refine ⟨hint, ?_⟩
  have h := integral_line_eq_residues (F := fun s => dslope E 1 s * ∑ a ∈ P, κ a / (s - a))
    (c := 2) P (fun a s => κ a * dslope E 1 s) (fun a _ => hD.const_mul _) hP
    (fun s _ _ => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring)
    hA0 hbound (by simpa using hint)
  simpa using h

/-- Cauchy's theorem to the right of the line for `r · N / (s (1 - s))`. -/
theorem integral_right_zero {r N : ℂ → ℂ} (hr : ∀ s : ℂ, 2 ≤ s.re → DifferentiableAt ℂ r s)
    (hN : Differentiable ℂ N) {K₁ K₂ R : ℝ} (hK₁ : 0 ≤ K₁)
    (hrb : ∀ s : ℂ, 2 ≤ s.re → R ≤ ‖s‖ → ‖r s‖ ≤ K₁)
    (hNb : ∀ s : ℂ, 2 ≤ s.re → ‖N s‖ ≤ K₂) :
    Integrable (fun t : ℝ => r (2 + t * I) * (N (2 + t * I) / ((2 + t * I) * (1 - (2 + t * I))))) ∧
    ∫ t : ℝ, r (2 + t * I) * (N (2 + t * I) / ((2 + t * I) * (1 - (2 + t * I)))) = 0 := by
  have hK₂ : 0 ≤ K₂ := (norm_nonneg _).trans (hNb 2 (by norm_num))
  set A : ℝ := 2 * K₁ * K₂ with hA
  have hA0 : 0 ≤ A := by positivity
  set R' : ℝ := max R 2 with hR'
  have hden : ∀ s : ℂ, 2 ≤ s.re → s * (1 - s) ≠ 0 := fun s hs =>
    mul_ne_zero (ne_zero_of_two_le_re hs) (sub_ne_zero.mpr (ne_one_of_two_le_re hs).symm)
  have hd : ∀ s : ℂ, 2 ≤ s.re → DifferentiableAt ℂ (fun s => r s * (N s / (s * (1 - s)))) s :=
    fun s hs => (hr s hs).mul ((hN s).div (by fun_prop) (hden s hs))
  have hbound : ∀ s : ℂ, 2 ≤ s.re → R' ≤ ‖s‖ → ‖r s * (N s / (s * (1 - s)))‖ ≤ A / ‖s‖ ^ 2 := by
    intro s hs hsR
    have hs2 : 2 ≤ ‖s‖ := (le_max_right _ _).trans hsR
    have hsub := half_le_norm_sub_one hs2
    have hs0 : 0 < ‖s‖ := by linarith
    rw [norm_mul, norm_div, norm_mul, norm_sub_rev]
    calc ‖r s‖ * (‖N s‖ / (‖s‖ * ‖s - 1‖)) ≤ K₁ * (K₂ / (‖s‖ * (‖s‖ / 2))) := by
          gcongr
          · exact hrb s hs ((le_max_left _ _).trans hsR)
          · exact hNb s hs
      _ = A / ‖s‖ ^ 2 := by rw [hA]; field_simp
  have hcont : Continuous fun t : ℝ =>
      r (2 + t * I) * (N (2 + t * I) / ((2 + t * I) * (1 - (2 + t * I)))) :=
    continuous_line (f := fun s => r s * (N s / (s * (1 - s)))) fun s hs => (hd s hs).continuousAt
  have hint : Integrable fun t : ℝ =>
      r (2 + t * I) * (N (2 + t * I) / ((2 + t * I) * (1 - (2 + t * I)))) := by
    have h := integrable_line (F := fun s => r s * (N s / (s * (1 - s)))) (c := 2)
      (R := max R' 1) hA0 (by simpa using hcont) fun t ht => by
        simpa using line_tail (G := fun s => r s * (N s / (s * (1 - s)))) hA0
          (fun s hs hsR => hbound s hs.ge hsR) ht
    simpa using h
  refine ⟨hint, ?_⟩
  have h := integral_line_eq_zero (F := fun s => r s * (N s / (s * (1 - s)))) (c := 2)
    (fun s hs => hd s hs) hA0 hbound (by simpa using hint)
  simpa using h

/-- A kernel on the line, split into a left part with poles and a right part without. -/
theorem integral_of_split {G : ℝ → ℂ} {E N r : ℂ → ℂ} (c₀ : ℂ)
    (hE : Differentiable ℂ E) {M : ℝ} (hEb : ∀ s : ℂ, s.re ≤ 2 → ‖E s‖ ≤ M)
    (hN : Differentiable ℂ N) {K₂ : ℝ} (hNb : ∀ s : ℂ, 2 ≤ s.re → ‖N s‖ ≤ K₂)
    (hr : ∀ s : ℂ, 2 ≤ s.re → DifferentiableAt ℂ r s) {K₁ R : ℝ} (hK₁ : 0 ≤ K₁)
    (hrb : ∀ s : ℂ, 2 ≤ s.re → R ≤ ‖s‖ → ‖r s‖ ≤ K₁)
    (P : Finset ℂ) (κ : ℂ → ℂ) (hP : ∀ a ∈ P, a.re < 2)
    (hrq : ∀ s : ℂ, 2 ≤ s.re → r s / s = ∑ a ∈ P, κ a / (s - a))
    (hG : ∀ t : ℝ, G t = c₀ * (dslope E 1 (2 + t * I) * (r (2 + t * I) / (2 + t * I)) +
      r (2 + t * I) * (N (2 + t * I) / ((2 + t * I) * (1 - (2 + t * I)))))) :
    Integrable G ∧ ∫ t : ℝ, G t = c₀ * (2 * Real.pi * ∑ a ∈ P, κ a * dslope E 1 a) := by
  obtain ⟨hi1, he1⟩ := integral_dslope_mul hE hEb P κ hP
  obtain ⟨hi2, he2⟩ := integral_right_zero hr hN hK₁ hrb hNb
  have hG' : G = fun t : ℝ => c₀ * (dslope E 1 (2 + t * I) * ∑ a ∈ P, κ a / (2 + t * I - a) +
      r (2 + t * I) * (N (2 + t * I) / ((2 + t * I) * (1 - (2 + t * I))))) := by
    funext t; rw [hG t, hrq _ (by simp)]
  rw [hG']
  refine ⟨(hi1.add hi2).const_mul c₀, ?_⟩
  rw [integral_const_mul, integral_add hi1 hi2, he1, he2, add_zero]

end LineResidues

section KernelIntegrals

open Complex Set Filter Topology MeasureTheory
open TentWidthTwoMargin

/-! ## 3. The explicit line integrals -/

lemma ofReal_ne_zero_of_pos {y : ℝ} (hy : 0 < y) : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'

lemma differentiable_cpow_ofReal {y : ℝ} (hy : 0 < y) :
    Differentiable ℂ (fun s : ℂ => (y : ℂ) ^ s) :=
  fun _ => differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero_of_pos hy))

lemma norm_cpow_ofReal_le {y : ℝ} (hy : 1 ≤ y) {s : ℂ} {c : ℝ} (hs : s.re ≤ c) :
    ‖(y : ℂ) ^ s‖ ≤ y ^ c := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hy hs

lemma norm_cpow_one_sub_le {b : ℝ} (hb : 1 ≤ b) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖(b : ℂ) ^ (1 - s)‖ ≤ 1 := by
  have h := norm_cpow_ofReal_le hb (s := 1 - s) (c := 0) (by simp; linarith)
  rwa [Real.rpow_zero] at h

lemma norm_inv_natCast_cpow_le {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖((n : ℂ) ^ s)⁻¹‖ ≤ 1 := by
  rw [norm_inv, Complex.norm_natCast_cpow_of_pos (by omega)]
  exact inv_le_one_of_one_le₀ (Real.one_le_rpow (by exact_mod_cast hn) hs)

lemma norm_cpow_mul_inv_natCast_cpow {b : ℝ} (hb : 0 < b) {n : ℕ} (hn : 1 ≤ n) (s : ℂ) :
    ‖(b : ℂ) ^ s * ((n : ℂ) ^ s)⁻¹‖ = (b / n) ^ s.re := by
  rw [norm_mul, norm_inv, Complex.norm_natCast_cpow_of_pos (by omega),
    Complex.norm_cpow_eq_rpow_re_of_pos hb, Real.div_rpow hb.le (Nat.cast_nonneg n), div_eq_mul_inv]

lemma dslope_cpow_zero (y : ℝ) :
    dslope (fun s : ℂ => (y : ℂ) ^ s) 1 0 = y - 1 := by
  rw [dslope_of_ne _ zero_ne_one, slope_def_field, Complex.cpow_zero, Complex.cpow_one]; ring

lemma dslope_cpow_one {y : ℝ} (hy : 0 < y) :
    dslope (fun s : ℂ => (y : ℂ) ^ s) 1 1 = (y : ℂ) * Real.log y := by
  rw [dslope_same]
  have h : HasDerivAt (fun s : ℂ => (y : ℂ) ^ s) ((y : ℂ) ^ (1 : ℂ) * Complex.log y * 1) 1 :=
    (hasDerivAt_id (1 : ℂ)).const_cpow (Or.inl (ofReal_ne_zero_of_pos hy))
  rw [h.deriv, Complex.cpow_one, mul_one, Complex.ofReal_log hy.le]

lemma dslope_cpow_of_ne (y : ℝ) {a : ℂ} (ha : a ≠ 1) :
    dslope (fun s : ℂ => (y : ℂ) ^ s) 1 a = ((y : ℂ) ^ a - y) / (a - 1) := by
  rw [dslope_of_ne _ ha, slope_def_field, Complex.cpow_one]

/-- The common split of the kernel `P_b = tentDephased b` on the line `re s = 2`. -/
lemma tentDephased_split {b : ℝ} {s : ℂ} (hs : 2 ≤ s.re) (r : ℂ) :
    r * tentDephased b s = Real.sqrt b *
      (dslope (fun z : ℂ => (b : ℂ) ^ z) 1 s * (r / s) +
        r * ((1 - (b : ℂ) ^ (1 - s)) / (s * (1 - s)))) := by
  have h0 := ne_zero_of_two_le_re hs
  have h1 := ne_one_of_two_le_re hs
  have h1' : 1 - s ≠ 0 := sub_ne_zero.mpr h1.symm
  have h1'' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  rw [dslope_cpow_of_ne b h1]
  unfold tentDephased
  field_simp
  ring

lemma differentiable_one_sub_cpow {b : ℝ} (hb : 0 < b) :
    Differentiable ℂ (fun s : ℂ => 1 - (b : ℂ) ^ (1 - s)) := by
  intro s
  exact (differentiableAt_const _).sub
    ((differentiableAt_const _).sub differentiableAt_id |>.const_cpow (Or.inl (ofReal_ne_zero_of_pos hb)))

lemma norm_one_sub_cpow_le {b : ℝ} (hb : 1 ≤ b) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖1 - (b : ℂ) ^ (1 - s)‖ ≤ 2 := by
  have h := norm_cpow_one_sub_le hb (s := s) (by linarith)
  calc ‖1 - (b : ℂ) ^ (1 - s)‖ ≤ ‖(1 : ℂ)‖ + ‖(b : ℂ) ^ (1 - s)‖ := norm_sub_le _ _
    _ ≤ 2 := by rw [norm_one]; linarith

lemma norm_cpow_le_sq {b : ℝ} (hb : 1 ≤ b) {s : ℂ} (hs : s.re ≤ 2) :
    ‖(b : ℂ) ^ s‖ ≤ b ^ (2 : ℝ) := norm_cpow_ofReal_le hb hs

/-- `∫ P_b(2 + it) dt = 2π √b (b - 1)`. -/
theorem integral_tentDephased {b : ℝ} (hb : 1 < b) :
    Integrable (fun t : ℝ => tentDephased b (2 + t * I)) ∧
    ∫ t : ℝ, tentDephased b (2 + t * I) = 2 * Real.pi * Real.sqrt b * (b - 1) := by
  have hb0 : 0 < b := by linarith
  have h := integral_of_split (G := fun t : ℝ => tentDephased b (2 + t * I))
    (E := fun z : ℂ => (b : ℂ) ^ z) (N := fun s => 1 - (b : ℂ) ^ (1 - s)) (r := fun _ => 1)
    (Real.sqrt b) (differentiable_cpow_ofReal hb0) (fun s hs => norm_cpow_le_sq hb.le hs)
    (differentiable_one_sub_cpow hb0) (fun s hs => norm_one_sub_cpow_le hb.le hs)
    (fun s _ => differentiableAt_const _) (R := 0) zero_le_one (fun s _ _ => by simp)
    {0} (fun _ => 1) (by simp) (fun s hs => by simp)
    (fun t => by rw [← tentDephased_split (two_add_re t).ge 1, one_mul])
  refine ⟨h.1, ?_⟩
  rw [h.2, Finset.sum_singleton, dslope_cpow_zero, one_mul]
  ring

/-- `∫ P_b(2 + it) / (1 + it) dt = 2π √b (b log b - b + 1)`. -/
theorem integral_inv_sub_one_mul {b : ℝ} (hb : 1 < b) :
    Integrable (fun t : ℝ => (2 + t * I - 1)⁻¹ * tentDephased b (2 + t * I)) ∧
    ∫ t : ℝ, (2 + t * I - 1)⁻¹ * tentDephased b (2 + t * I) =
      2 * Real.pi * Real.sqrt b * (b * Real.log b - b + 1) := by
  have hb0 : 0 < b := by linarith
  have hr : ∀ s : ℂ, 2 ≤ s.re → DifferentiableAt ℂ (fun s : ℂ => (s - 1)⁻¹) s := fun s hs =>
    (differentiableAt_id.sub_const 1).inv (sub_ne_zero.mpr (ne_one_of_two_le_re hs))
  have hrb : ∀ s : ℂ, 2 ≤ s.re → 2 ≤ ‖s‖ → ‖(s - 1)⁻¹‖ ≤ 1 := by
    intro s _ hs2
    have h := half_le_norm_sub_one hs2
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ (by linarith)
  have h := integral_of_split (G := fun t : ℝ => (2 + t * I - 1)⁻¹ * tentDephased b (2 + t * I))
    (E := fun z : ℂ => (b : ℂ) ^ z) (N := fun s => 1 - (b : ℂ) ^ (1 - s))
    (r := fun s => (s - 1)⁻¹)
    (Real.sqrt b) (differentiable_cpow_ofReal hb0) (fun s hs => norm_cpow_le_sq hb.le hs)
    (differentiable_one_sub_cpow hb0) (fun s hs => norm_one_sub_cpow_le hb.le hs)
    hr zero_le_one hrb
    {0, 1} (fun a => if a = 0 then -1 else 1)
    (by intro a ha; simp at ha; rcases ha with rfl | rfl <;> norm_num)
    (fun s hs => by
      have h0 := ne_zero_of_two_le_re hs
      have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr (ne_one_of_two_le_re hs)
      rw [Finset.sum_pair zero_ne_one]
      simp only [if_true, one_ne_zero, if_false, sub_zero]
      field_simp
      ring)
    (fun t => tentDephased_split (two_add_re t).ge _)
  refine ⟨h.1, ?_⟩
  rw [h.2, Finset.sum_pair zero_ne_one]
  simp only [if_true, one_ne_zero, if_false]
  rw [dslope_cpow_zero, dslope_cpow_one hb0]
  ring

/-- The terms `u_m(s) = 1/(2(m+1)) - 1/(s+2m)` of `ψ(s/2)/2 + γ/2`. -/
def uTerm (m : ℕ) (s : ℂ) : ℂ := 1 / (2 * ((m : ℂ) + 1)) - 1 / (s + 2 * m)

lemma add_two_mul_ne_zero {s : ℂ} (hs : 0 < s.re) (m : ℕ) : s + 2 * (m : ℂ) ≠ 0 := by
  intro h
  have h' := congrArg Complex.re h
  simp only [add_re, mul_re, re_ofNat, natCast_re, im_ofNat, natCast_im, mul_zero, sub_zero,
    zero_re] at h'
  linarith [Nat.cast_nonneg (α := ℝ) m]

/-- `∫ u_m(2 + it) P_b(2 + it) dt` for `m ≥ 1`. -/
theorem integral_uTerm_mul {b : ℝ} (hb : 1 < b) {m : ℕ} (hm : 1 ≤ m) :
    Integrable (fun t : ℝ => uTerm m (2 + t * I) * tentDephased b (2 + t * I)) ∧
    ∫ t : ℝ, uTerm m (2 + t * I) * tentDephased b (2 + t * I) =
      2 * Real.pi * Real.sqrt b * ((1 / (2 * ((m : ℂ) + 1)) - 1 / (2 * m)) * (b - 1) +
        dslope (fun z : ℂ => (b : ℂ) ^ z) 1 (-2 * m) / (2 * m)) := by
  have hb0 : 0 < b := by linarith
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hm1 : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hne : (0 : ℂ) ≠ -2 * m := by
    intro h; apply hm0; linear_combination h / 2
  have hr : ∀ s : ℂ, 2 ≤ s.re → DifferentiableAt ℂ (uTerm m) s := fun s hs => by
    unfold uTerm
    exact (differentiableAt_const _).sub ((differentiableAt_const _).div
      (differentiableAt_id.add_const _) (add_two_mul_ne_zero (by linarith) m))
  have hrb : ∀ s : ℂ, 2 ≤ s.re → 0 ≤ ‖s‖ → ‖uTerm m s‖ ≤ 2 := by
    intro s hs _
    have h1 : 1 ≤ ‖s + 2 * (m : ℂ)‖ := by
      refine le_trans ?_ (Complex.re_le_norm _)
      simp only [add_re, mul_re, re_ofNat, natCast_re, im_ofNat, natCast_im, mul_zero, sub_zero]
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have h2 : ‖1 / (2 * ((m : ℂ) + 1))‖ ≤ 1 := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, TentDigamma.norm_natCast_add_one]
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have h3 : ‖1 / (s + 2 * (m : ℂ))‖ ≤ 1 := by
      rw [norm_div, norm_one]; exact div_le_one_of_le₀ h1 (norm_nonneg _)
    unfold uTerm
    calc ‖1 / (2 * ((m : ℂ) + 1)) - 1 / (s + 2 * m)‖ ≤
        ‖1 / (2 * ((m : ℂ) + 1))‖ + ‖1 / (s + 2 * (m : ℂ))‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith
  have h := integral_of_split (G := fun t : ℝ => uTerm m (2 + t * I) * tentDephased b (2 + t * I))
    (E := fun z : ℂ => (b : ℂ) ^ z) (N := fun s => 1 - (b : ℂ) ^ (1 - s)) (r := uTerm m)
    (Real.sqrt b) (differentiable_cpow_ofReal hb0) (fun s hs => norm_cpow_le_sq hb.le hs)
    (differentiable_one_sub_cpow hb0) (fun s hs => norm_one_sub_cpow_le hb.le hs)
    hr (by norm_num) hrb
    ({0, -2 * (m : ℂ)} : Finset ℂ) (fun a => if a = 0 then 1 / (2 * ((m : ℂ) + 1)) - 1 / (2 * m) else 1 / (2 * m))
    (by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · norm_num
      · simp only [mul_re, neg_re, re_ofNat, natCast_re, neg_im, im_ofNat, natCast_im, mul_zero,
          sub_zero, neg_zero]
        linarith [Nat.cast_nonneg (α := ℝ) m])
    (fun s hs => by
      have h0 := ne_zero_of_two_le_re hs
      have h2 := add_two_mul_ne_zero (s := s) (by linarith) m
      rw [Finset.sum_pair hne]
      simp only [if_true, hne.symm, if_false, sub_zero]
      unfold uTerm
      rw [show s - -2 * (m : ℂ) = s + 2 * m by ring]
      field_simp
      ring)
    (fun t => tentDephased_split (two_add_re t).ge _)
  refine ⟨h.1, ?_⟩
  rw [h.2, Finset.sum_pair hne]
  simp only [if_true, hne.symm, if_false]
  rw [dslope_cpow_zero]
  ring

end KernelIntegrals

section PrimePowers

open Complex Set Filter Topology MeasureTheory
open TentWidthTwoMargin

/-! ## 4. Prime powers and the digamma series on the line -/

lemma natCast_ne_zero_of_one_le {n : ℕ} (hn : 1 ≤ n) : (n : ℂ) ≠ 0 := by
  exact_mod_cast (by omega : n ≠ 0)

lemma natCpow_ne_zero {n : ℕ} (hn : 1 ≤ n) (s : ℂ) : (n : ℂ) ^ s ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero (natCast_ne_zero_of_one_le hn)]; exact Complex.exp_ne_zero _

lemma differentiable_natCpow_inv {n : ℕ} (hn : 1 ≤ n) :
    Differentiable ℂ (fun s : ℂ => ((n : ℂ) ^ s)⁻¹) := fun s =>
  (differentiableAt_id.const_cpow (Or.inl (natCast_ne_zero_of_one_le hn))).inv
    (natCpow_ne_zero hn s)

/-- For `1 ≤ n ≤ b`: `∫ n^{-s} P_b(s)` along `re s = 2` is `2π √b (b/n - 1)`. -/
theorem integral_natCpow_inv_mul_of_le {b : ℝ} (hb : 1 < b) {n : ℕ} (hn : 1 ≤ n)
    (hnb : (n : ℝ) ≤ b) :
    Integrable (fun t : ℝ => ((n : ℂ) ^ (2 + t * I))⁻¹ * tentDephased b (2 + t * I)) ∧
    ∫ t : ℝ, ((n : ℂ) ^ (2 + t * I))⁻¹ * tentDephased b (2 + t * I) =
      2 * Real.pi * Real.sqrt b * ((b : ℂ) / n - 1) := by
  have hb0 : 0 < b := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn0' := natCast_ne_zero_of_one_le hn
  have hbn : 1 ≤ b / n := (one_le_div hn0).mpr hnb
  have hE : Differentiable ℂ (fun s : ℂ => (b : ℂ) ^ s * ((n : ℂ) ^ s)⁻¹) :=
    (differentiable_cpow_ofReal hb0).mul (differentiable_natCpow_inv hn)
  have hEb : ∀ s : ℂ, s.re ≤ 2 → ‖(b : ℂ) ^ s * ((n : ℂ) ^ s)⁻¹‖ ≤ (b / n) ^ (2 : ℝ) := by
    intro s hs
    rw [norm_cpow_mul_inv_natCast_cpow hb0 hn]
    exact Real.rpow_le_rpow_of_exponent_le hbn hs
  have hN : Differentiable ℂ (fun s : ℂ => ((b : ℂ) + 1) * ((n : ℂ) ^ s)⁻¹ -
      (b : ℂ) ^ (1 - s) * ((n : ℂ) ^ s)⁻¹ - (b : ℂ) / n) := by
    have h1 := differentiable_natCpow_inv hn
    have h2 : Differentiable ℂ (fun s : ℂ => (b : ℂ) ^ (1 - s)) := fun s =>
      ((differentiableAt_const _).sub differentiableAt_id).const_cpow
        (Or.inl (ofReal_ne_zero_of_pos hb0))
    exact ((h1.const_mul _).sub (h2.mul h1)).sub_const _
  have hNb : ∀ s : ℂ, 2 ≤ s.re → ‖((b : ℂ) + 1) * ((n : ℂ) ^ s)⁻¹ -
      (b : ℂ) ^ (1 - s) * ((n : ℂ) ^ s)⁻¹ - (b : ℂ) / n‖ ≤ (b + 1) + 1 + b := by
    intro s hs
    have h1 := norm_inv_natCast_cpow_le hn (s := s) (by linarith)
    have h2 := norm_cpow_one_sub_le hb.le (s := s) (by linarith)
    have h3 : ‖(b : ℂ) / n‖ ≤ b := by
      rw [norm_div, Complex.norm_real, Complex.norm_natCast, Real.norm_of_nonneg hb0.le]
      exact div_le_self hb0.le (by exact_mod_cast hn)
    have h4 : ‖(b : ℂ) + 1‖ ≤ b + 1 := by
      rw [show (b : ℂ) + 1 = ((b + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
    calc _ ≤ ‖((b : ℂ) + 1) * ((n : ℂ) ^ s)⁻¹‖ + ‖(b : ℂ) ^ (1 - s) * ((n : ℂ) ^ s)⁻¹‖ +
          ‖(b : ℂ) / n‖ := norm_sub_le_of_le (norm_sub_le _ _) le_rfl
      _ ≤ (b + 1) * 1 + 1 * 1 + b := by
          rw [norm_mul, norm_mul]
          gcongr
      _ = (b + 1) + 1 + b := by ring
  have h := integral_of_split
    (G := fun t : ℝ => ((n : ℂ) ^ (2 + t * I))⁻¹ * tentDephased b (2 + t * I))
    (E := fun s : ℂ => (b : ℂ) ^ s * ((n : ℂ) ^ s)⁻¹)
    (N := fun s : ℂ => ((b : ℂ) + 1) * ((n : ℂ) ^ s)⁻¹ - (b : ℂ) ^ (1 - s) * ((n : ℂ) ^ s)⁻¹ -
      (b : ℂ) / n)
    (r := fun _ => 1) (Real.sqrt b) hE hEb hN hNb (fun s _ => differentiableAt_const _)
    (R := 0) zero_le_one (fun s _ _ => by simp) {0} (fun _ => 1) (by simp) (fun s hs => by simp)
    (fun t => by
      have hs := (two_add_re t).ge
      have h0 := ne_zero_of_two_le_re hs
      have h1 := ne_one_of_two_le_re hs
      have h1' : 1 - (2 + t * I) ≠ 0 := sub_ne_zero.mpr h1.symm
      have h1'' : (2 + t * I) - 1 ≠ 0 := sub_ne_zero.mpr h1
      have hpow := natCpow_ne_zero hn (2 + t * I)
      rw [dslope_of_ne _ h1, slope_def_field]
      simp only [Complex.cpow_one]
      unfold tentDephased
      field_simp
      ring)
  refine ⟨h.1, ?_⟩
  rw [h.2, Finset.sum_singleton, dslope_of_ne _ zero_ne_one, slope_def_field]
  simp only [Complex.cpow_zero, Complex.cpow_one, inv_one, mul_one, one_mul]
  field_simp
  ring

/-- For `b < n`: `∫ n^{-s} P_b(s)` along `re s = 2` vanishes. -/
theorem integral_natCpow_inv_mul_of_lt {b : ℝ} (hb : 1 < b) {n : ℕ} (hnb : b < n) :
    Integrable (fun t : ℝ => ((n : ℂ) ^ (2 + t * I))⁻¹ * tentDephased b (2 + t * I)) ∧
    ∫ t : ℝ, ((n : ℂ) ^ (2 + t * I))⁻¹ * tentDephased b (2 + t * I) = 0 := by
  have hb0 : 0 < b := by linarith
  have hn : 1 ≤ n := by
    have : (1 : ℝ) < n := hb.trans hnb
    exact_mod_cast this.le
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hbn : b / n ≤ 1 := (div_le_one hn0).mpr hnb.le
  set N : ℂ → ℂ := fun s => ((n : ℂ) ^ s)⁻¹ * (((b : ℂ) + 1) - (b : ℂ) ^ s - (b : ℂ) ^ (1 - s))
    with hNdef
  have hN : Differentiable ℂ N := by
    have h1 := differentiable_natCpow_inv hn
    have h2 : Differentiable ℂ (fun s : ℂ => (b : ℂ) ^ (1 - s)) := fun s =>
      ((differentiableAt_const _).sub differentiableAt_id).const_cpow
        (Or.inl (ofReal_ne_zero_of_pos hb0))
    exact h1.mul (((differentiable_const _).sub (differentiable_cpow_ofReal hb0)).sub h2)
  have hNb : ∀ s : ℂ, 2 ≤ s.re → ‖N s‖ ≤ (b + 1) + 1 + 1 := by
    intro s hs
    have h1 := norm_inv_natCast_cpow_le hn (s := s) (by linarith)
    have h2 := norm_cpow_one_sub_le hb.le (s := s) (by linarith)
    have h3 : ‖((n : ℂ) ^ s)⁻¹ * (b : ℂ) ^ s‖ ≤ 1 := by
      rw [mul_comm, norm_cpow_mul_inv_natCast_cpow hb0 hn]
      exact Real.rpow_le_one (by positivity) hbn (by linarith)
    have h4 : ‖(b : ℂ) + 1‖ ≤ b + 1 := by
      rw [show (b : ℂ) + 1 = ((b + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
    have e : N s = ((n : ℂ) ^ s)⁻¹ * ((b : ℂ) + 1) - ((n : ℂ) ^ s)⁻¹ * (b : ℂ) ^ s -
        ((n : ℂ) ^ s)⁻¹ * (b : ℂ) ^ (1 - s) := by rw [hNdef]; ring
    rw [e]
    calc _ ≤ ‖((n : ℂ) ^ s)⁻¹ * ((b : ℂ) + 1)‖ + ‖((n : ℂ) ^ s)⁻¹ * (b : ℂ) ^ s‖ +
          ‖((n : ℂ) ^ s)⁻¹ * (b : ℂ) ^ (1 - s)‖ := norm_sub_le_of_le (norm_sub_le _ _) le_rfl
      _ ≤ 1 * (b + 1) + 1 + 1 * 1 := by
          rw [norm_mul ((n : ℂ) ^ s)⁻¹ ((b : ℂ) + 1), norm_mul ((n : ℂ) ^ s)⁻¹ ((b : ℂ) ^ (1 - s))]
          gcongr
      _ = (b + 1) + 1 + 1 := by ring
  have h := integral_right_zero (r := fun _ => (Real.sqrt b : ℂ)) (N := N)
    (fun s _ => differentiableAt_const _) hN (K₁ := Real.sqrt b) (R := 0) (Real.sqrt_nonneg b)
    (fun s _ _ => by rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg b)]) hNb
  have hfun : (fun t : ℝ => ((n : ℂ) ^ (2 + t * I))⁻¹ * tentDephased b (2 + t * I)) =
      fun t : ℝ => (Real.sqrt b : ℂ) * (N (2 + t * I) / ((2 + t * I) * (1 - (2 + t * I)))) := by
    funext t
    rw [hNdef]
    unfold tentDephased
    ring
  rw [hfun]
  exact h

/-! ### The digamma series on the line -/

lemma uTerm_eq_half {s : ℂ} (hs : 0 < s.re) (m : ℕ) :
    uTerm m s = TentDigamma.digammaTerm (s / 2) m / 2 := by
  have h1 := add_two_mul_ne_zero hs m
  have h2 : s / 2 + (m : ℂ) ≠ 0 := by
    intro h; apply h1; linear_combination 2 * h
  have h3 : (m : ℂ) + 1 ≠ 0 := TentDigamma.natCast_add_one_ne_zero m
  unfold uTerm TentDigamma.digammaTerm
  field_simp

lemma norm_uTerm_line_le (m : ℕ) (t : ℝ) :
    ‖uTerm m (2 + t * I)‖ ≤
      Real.sqrt |t| * (1 / (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))) := by
  have hs : (0 : ℝ) < ((2 : ℂ) + t * I).re := by simp
  rw [uTerm_eq_half hs, norm_div, Complex.norm_ofNat]
  have e : (2 + t * I) / 2 = 1 + ((t / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [e]
  have h := TentDigamma.norm_digammaTerm_one_add_le (t / 2) m
  have hm : 0 < ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1) := by positivity
  have hsq : Real.sqrt |t / 2| ≤ Real.sqrt |t| := by
    apply Real.sqrt_le_sqrt
    rw [abs_div, abs_two]
    linarith [abs_nonneg t]
  calc ‖TentDigamma.digammaTerm (1 + ((t / 2 : ℝ) : ℂ) * I) m‖ / 2
      ≤ Real.sqrt |t / 2| / (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1)) / 2 := by gcongr
    _ ≤ Real.sqrt |t| / (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1)) := by
        rw [div_div]
        apply div_le_div₀ (Real.sqrt_nonneg _) hsq hm
        nlinarith
    _ = Real.sqrt |t| * (1 / (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))) := by ring

lemma norm_line_mul_le (t : ℝ) :
    1 + t ^ 2 ≤ ‖(2 : ℂ) + t * I‖ * ‖1 - ((2 : ℂ) + t * I)‖ := by
  have e1 : (2 : ℂ) + t * I = ((2 : ℝ) : ℂ) + t * I := by push_cast; ring
  have e2 : 1 - ((2 : ℂ) + t * I) = ((-1 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by push_cast; ring
  rw [e2, e1, Complex.norm_add_mul_I, Complex.norm_add_mul_I]
  have h1 : Real.sqrt (1 + t ^ 2) ≤ Real.sqrt (2 ^ 2 + t ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  have h2 : Real.sqrt ((-1) ^ 2 + (-t) ^ 2) = Real.sqrt (1 + t ^ 2) := by ring_nf
  rw [h2]
  calc 1 + t ^ 2 = Real.sqrt (1 + t ^ 2) * Real.sqrt (1 + t ^ 2) :=
        (Real.mul_self_sqrt (by positivity)).symm
    _ ≤ Real.sqrt (2 ^ 2 + t ^ 2) * Real.sqrt (1 + t ^ 2) := by gcongr

lemma norm_tentDephased_line_le {b : ℝ} (hb : 1 < b) (t : ℝ) :
    ‖tentDephased b (2 + t * I)‖ ≤ Real.sqrt b * (b + 1 + b ^ (2 : ℝ) + 1) / (1 + t ^ 2) := by
  have hb0 : 0 < b := by linarith
  have hs : (2 : ℝ) ≤ ((2 : ℂ) + t * I).re := by simp
  unfold tentDephased
  rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg b)]
  have hnum : ‖((b : ℂ) + 1) - (b : ℂ) ^ ((2 : ℂ) + t * I) - (b : ℂ) ^ (1 - ((2 : ℂ) + t * I))‖ ≤
      b + 1 + b ^ (2 : ℝ) + 1 := by
    have h1 : ‖(b : ℂ) ^ ((2 : ℂ) + t * I)‖ ≤ b ^ (2 : ℝ) := norm_cpow_le_sq hb.le (by simp)
    have h2 := norm_cpow_one_sub_le hb.le (s := (2 : ℂ) + t * I) (by simp)
    have h3 : ‖(b : ℂ) + 1‖ ≤ b + 1 := by
      rw [show (b : ℂ) + 1 = ((b + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
    calc _ ≤ ‖(b : ℂ) + 1‖ + ‖(b : ℂ) ^ ((2 : ℂ) + t * I)‖ + ‖(b : ℂ) ^ (1 - ((2 : ℂ) + t * I))‖ :=
          norm_sub_le_of_le (norm_sub_le _ _) le_rfl
      _ ≤ b + 1 + b ^ (2 : ℝ) + 1 := by linarith
  have hden := norm_line_mul_le t
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  gcongr

lemma integrable_sqrt_abs_div : Integrable (fun t : ℝ => Real.sqrt |t| / (1 + t ^ 2)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 3 / 2)
    (by simp; norm_num)
  refine h.mono' ((Real.continuous_sqrt.comp continuous_abs).div (by fun_prop)
    (fun t => by positivity)).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have hx : 0 < 1 + t ^ 2 := by positivity
  have h1 : Real.sqrt |t| ≤ (1 + t ^ 2) ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, show (1 / 4 : ℝ) = (1 / 2) * (1 / 2) by norm_num,
      Real.rpow_mul hx.le]
    apply Real.rpow_le_rpow (abs_nonneg t) _ (by norm_num)
    rw [← Real.sqrt_eq_rpow]
    exact Real.abs_le_sqrt (by nlinarith)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_eq_abs, sq_abs]
  calc Real.sqrt |t| / (1 + t ^ 2) ≤ (1 + t ^ 2) ^ (1 / 4 : ℝ) / (1 + t ^ 2) := by gcongr
    _ = (1 + t ^ 2) ^ (-(3 / 2 : ℝ) / 2) := by
        rw [← Real.rpow_sub_one hx.ne']; norm_num

end PrimePowers

section CompletedXi

open Complex Set Filter Topology MeasureTheory
open TentWidthTwoMargin

local notation "γ" => Real.eulerMascheroniConstant

/-! ## 5. The completed function `Ξ(s) = s (s - 1) Λ(s)` -/

/-- `Ξ(s) = s (s - 1) Λ(s) = s (s - 1) Λ₀(s) + 1`, twice Riemann's `ξ`. -/
def Xi (s : ℂ) : ℂ := s * (s - 1) * completedRiemannZeta₀ s + 1

lemma differentiable_Xi : Differentiable ℂ Xi := by
  unfold Xi
  exact ((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1

lemma Xi_one_sub (s : ℂ) : Xi (1 - s) = Xi s := by
  unfold Xi; rw [completedRiemannZeta₀_one_sub]; ring

lemma Xi_one : Xi 1 = 1 := by unfold Xi; ring

lemma Xi_eq_completed {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    Xi s = s * (s - 1) * completedRiemannZeta s := by
  have h1' : 1 - s ≠ 0 := sub_ne_zero.mpr h1.symm
  unfold Xi
  rw [completedRiemannZeta_eq]
  field_simp
  ring

lemma ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : s ≠ 0 := by
  rintro rfl; simp at hs

lemma Xi_eq_zeta {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    Xi s = s * (s - 1) * Gammaℝ s * riemannZeta s := by
  have h0 := ne_zero_of_re_pos hs
  rw [Xi_eq_completed h0 h1, riemannZeta_def_of_ne_zero h0]
  field_simp [Gammaℝ_ne_zero_of_re_pos hs]

lemma Xi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : Xi s ≠ 0 := by
  by_cases h1 : s = 1
  · rw [h1, Xi_one]; exact one_ne_zero
  · rw [Xi_eq_zeta (by linarith) h1]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (ne_zero_of_re_pos (by linarith))
      (sub_ne_zero.mpr h1)) (Gammaℝ_ne_zero_of_re_pos (by linarith)))
      (riemannZeta_ne_zero_of_one_le_re hs)

lemma Xi_ne_zero_of_re_le_zero {s : ℂ} (hs : s.re ≤ 0) : Xi s ≠ 0 := by
  rw [← Xi_one_sub]; exact Xi_ne_zero_of_one_le_re (by simp; linarith)

lemma Xi_eq_zero_iff {s : ℂ} : Xi s = 0 ↔ 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 := by
  constructor
  · intro h
    have h0 : 0 < s.re := by
      by_contra hc; exact Xi_ne_zero_of_re_le_zero (not_lt.mp hc) h
    have h1 : s.re < 1 := by
      by_contra hc; exact Xi_ne_zero_of_one_le_re (not_lt.mp hc) h
    refine ⟨h0, h1, ?_⟩
    have hs1 : s ≠ 1 := by rintro rfl; simp at h1
    rw [Xi_eq_zeta h0 hs1] at h
    rcases mul_eq_zero.mp h with h | h
    · exfalso
      exact mul_ne_zero (mul_ne_zero (ne_zero_of_re_pos h0) (sub_ne_zero.mpr hs1))
        (Gammaℝ_ne_zero_of_re_pos h0) h
    · exact h
  · rintro ⟨h0, h1, hz⟩
    have hs1 : s ≠ 1 := by rintro rfl; simp at h1
    rw [Xi_eq_zeta h0 hs1, hz, mul_zero]

lemma analyticAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Gammaℝ s := by
  have hG := Gammaℝ_ne_zero_of_re_pos hs
  have h := (differentiable_Gammaℝ_inv.analyticAt s).inv (inv_ne_zero hG)
  have e : (fun z => (Gammaℝ z)⁻¹)⁻¹ = Gammaℝ := by funext z; simp
  rwa [e] at h

lemma orderNat_Xi {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    analyticOrderNatAt Xi ρ = ZetaShared.mult ρ := by
  have hρ1 : ρ ≠ 1 := by rintro rfl; simp at h1
  have hev : Xi =ᶠ[𝓝 ρ] (fun s => s * (s - 1) * Gammaℝ s) * riemannZeta := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds h0,
      isOpen_compl_singleton.mem_nhds hρ1] with s hs hs1
    rw [Xi_eq_zeta hs hs1]; rfl
  have hA : AnalyticAt ℂ (fun s => s * (s - 1) * Gammaℝ s) ρ :=
    ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul (analyticAt_Gammaℝ h0))
  have hA0 : ρ * (ρ - 1) * Gammaℝ ρ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ne_zero_of_re_pos h0) (sub_ne_zero.mpr hρ1))
      (Gammaℝ_ne_zero_of_re_pos h0)
  unfold analyticOrderNatAt ZetaShared.mult analyticOrderNatAt
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hA (ZetaCount.analyticAt_zeta hρ1),
    hA.analyticOrderAt_eq_zero.mpr hA0, zero_add]

lemma orderAt_Xi_ne_top (z : ℂ) : analyticOrderAt Xi z ≠ ⊤ :=
  ZetaStrip.analyticOrderAt_ne_top_of_entire differentiable_Xi (c := 1) (by rw [Xi_one]; simp) z

/-- The logarithmic derivative is odd under `s ↦ 1 - s`. -/
lemma logDeriv_Xi_one_sub (s : ℂ) :
    deriv Xi (1 - s) / Xi (1 - s) = -(deriv Xi s / Xi s) := by
  have h : deriv (fun z => Xi (1 - z)) s = deriv Xi s := by
    rw [show (fun z => Xi (1 - z)) = Xi from funext Xi_one_sub]
  rw [deriv_comp_const_sub] at h
  rw [Xi_one_sub, ← h]
  ring

/-- On `0 < re s`, away from `1` and the zeros, `Ξ'/Ξ = 1/s + 1/(s-1) + Γℝ'/Γℝ + ζ'/ζ`. -/
lemma logDeriv_Xi {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    deriv Xi s / Xi s = 1 / s + 1 / (s - 1) + logDeriv Gammaℝ s +
      deriv riemannZeta s / riemannZeta s := by
  have h0 := ne_zero_of_re_pos hs
  have hG := Gammaℝ_ne_zero_of_re_pos hs
  have hev : Xi =ᶠ[𝓝 s] fun z => z * (z - 1) * Gammaℝ z * riemannZeta z := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs,
      isOpen_compl_singleton.mem_nhds h1] with z hz' hz1
    exact Xi_eq_zeta hz' hz1
  have e1 : deriv Xi s / Xi s = logDeriv (fun z => z * (z - 1) * Gammaℝ z * riemannZeta z) s := by
    rw [← logDeriv_apply]; exact (logDeriv_congr_nhds hev).eq_of_nhds
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have dA : DifferentiableAt ℂ (fun z : ℂ => z) s := differentiableAt_id
  have dB : DifferentiableAt ℂ (fun z : ℂ => z - 1) s := differentiableAt_id.sub_const 1
  have dG : DifferentiableAt ℂ Gammaℝ s := (analyticAt_Gammaℝ hs).differentiableAt
  have dZ : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta h1
  rw [e1, logDeriv_mul (f := fun z => z * (z - 1) * Gammaℝ z) (g := riemannZeta) s
      (mul_ne_zero (mul_ne_zero h0 hs1) hG) hz ((dA.mul dB).mul dG) dZ,
    logDeriv_mul (f := fun z => z * (z - 1)) (g := Gammaℝ) s (mul_ne_zero h0 hs1) hG
      (dA.mul dB) dG,
    logDeriv_mul (f := fun z : ℂ => z) (g := fun z : ℂ => z - 1) s h0 hs1 dA dB,
    logDeriv_apply riemannZeta]
  have hb : logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
    rw [logDeriv_apply]; simp
  rw [hb, logDeriv_id']

/-- `κ = (1 - γ - log π)/2`. -/
def kappa : ℂ := (1 - γ - Real.log Real.pi) / 2

/-- On `2 ≤ re s`: `Ξ'/Ξ = ζ'/ζ + 1/(s-1) + κ + ∑_{m ≥ 0} u_{m+1}(s)`. -/
theorem hasSum_logDeriv_Xi {s : ℂ} (hs : 2 ≤ s.re) :
    HasSum (fun m : ℕ => uTerm (m + 1) s)
      (deriv Xi s / Xi s - deriv riemannZeta s / riemannZeta s - (s - 1)⁻¹ - kappa) := by
  have hs0 : 0 < s.re := by linarith
  have h0 := ne_zero_of_re_pos hs0
  have h1 := ne_one_of_two_le_re hs
  have hz := riemannZeta_ne_zero_of_one_le_re (s := s) (by linarith)
  have hre : 0 < (s / 2).re := by simp; linarith
  have hsum : HasSum (fun m => uTerm m s) ((Complex.digamma (s / 2) + γ) / 2) := by
    have h := (TentDigamma.hasSum_digammaTerm hre).div_const 2
    exact h.congr_fun fun m => uTerm_eq_half hs0 m
  have hshift := (hasSum_nat_add_iff' 1).mpr hsum
  simp only [Finset.range_one, Finset.sum_singleton] at hshift
  have hval : deriv Xi s / Xi s - deriv riemannZeta s / riemannZeta s - (s - 1)⁻¹ - kappa =
      (Complex.digamma (s / 2) + γ) / 2 - uTerm 0 s := by
    rw [logDeriv_Xi hs0 h1 hz, TentDigamma.logDeriv_Gammaℝ hs0]
    unfold kappa uTerm
    simp only [Nat.cast_zero, mul_zero, add_zero, zero_add]
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
    field_simp
    ring
  rw [hval]
  exact hshift

end CompletedXi

section Rectangle

open Complex Set Filter Topology MeasureTheory
open TentWidthTwoMargin ZetaExplicit ZetaShared

/-! ## 6. The rectangle `[-1, 2] × [-T, T]` -/

/-- The numerator `(b + 1) - b^s - b^{1-s}` of `P_b`. -/
def tentNum (b : ℝ) (s : ℂ) : ℂ := ((b : ℂ) + 1) - (b : ℂ) ^ s - (b : ℂ) ^ (1 - s)

lemma differentiable_tentNum {b : ℝ} (hb : 0 < b) : Differentiable ℂ (tentNum b) := by
  have h2 : Differentiable ℂ (fun s : ℂ => (b : ℂ) ^ (1 - s)) := fun s =>
    ((differentiableAt_const _).sub differentiableAt_id).const_cpow
      (Or.inl (ofReal_ne_zero_of_pos hb))
  exact ((differentiable_const _).sub (differentiable_cpow_ofReal hb)).sub h2

lemma tentNum_zero (b : ℝ) : tentNum b 0 = 0 := by
  unfold tentNum; rw [Complex.cpow_zero, sub_zero, Complex.cpow_one]; ring

lemma tentNum_one (b : ℝ) : tentNum b 1 = 0 := by
  unfold tentNum; rw [sub_self, Complex.cpow_zero, Complex.cpow_one]; ring

/-- `P_b` with its removable singularities at `0` and `1` filled in; an entire function. -/
def Pent (b : ℝ) (s : ℂ) : ℂ :=
  Real.sqrt b * (dslope (tentNum b) 0 s - dslope (tentNum b) 1 s)

lemma differentiable_dslope_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) :
    Differentiable ℂ (dslope f c) := by
  have h := (Complex.differentiableOn_dslope (f := f) (c := c) (s := univ)
    Filter.univ_mem).mpr hf.differentiableOn
  exact fun s => (h s (mem_univ s)).differentiableAt Filter.univ_mem

lemma differentiable_Pent {b : ℝ} (hb : 0 < b) : Differentiable ℂ (Pent b) := by
  have h0 := differentiable_dslope_of_entire (differentiable_tentNum hb) 0
  have h1 := differentiable_dslope_of_entire (differentiable_tentNum hb) 1
  exact (h0.sub h1).const_mul _

lemma Pent_eq {b : ℝ} {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : Pent b s = tentDephased b s := by
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have h1'' : 1 - s ≠ 0 := sub_ne_zero.mpr h1.symm
  unfold Pent tentDephased
  rw [dslope_of_ne _ h0, dslope_of_ne _ h1, slope_def_field, slope_def_field, tentNum_zero,
    tentNum_one]
  unfold tentNum
  field_simp
  ring

/-- **Residues of `Ξ'/Ξ · P_b`.** If `Ξ` does not vanish on the horizontal sides, the boundary
integral over `[-1, 2] × [-T, T]` is `2πi ∑_{|γ| < T} m_ρ P_b(ρ)`. -/
theorem rect_residues {b : ℝ} (hb : 1 < b) {T : ℝ} (hT : 0 < T)
    (hedge : ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → |s.im| = T → Xi s ≠ 0) :
    rectInt (fun s => deriv Xi s / Xi s * Pent b s) (-1) 2 (-T) T =
      2 * Real.pi * I * ∑ ρ ∈ (zerosBelow_finite T).toFinset,
        (mult ρ : ℂ) * tentDephased b ρ := by
  classical
  have hb0 : 0 < b := by linarith
  set S : Finset ℂ := (zerosBelow_finite T).toFinset with hS
  have hmemS : ∀ ρ, ρ ∈ S ↔ ρ ∈ zerosBelow T := fun ρ => by rw [hS, Set.Finite.mem_toFinset]
  obtain ⟨g, hg, hfac, hgS⟩ := exists_factor differentiable_Xi orderAt_Xi_ne_top S
  set U : Set ℂ := {s | g s ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne_fun hg.continuous continuous_const
  have hXi : ∀ s ∈ rectClosed (-1) 2 (-T) T, s ∉ S → Xi s ≠ 0 := by
    intro s hs hsS hX
    obtain ⟨h1, h2, h3, h4⟩ := hs
    obtain ⟨hre0, hre1, hz⟩ := Xi_eq_zero_iff.mp hX
    have him : |s.im| < T := by
      rcases lt_or_eq_of_le (abs_le.mpr ⟨h3, h4⟩) with h | h
      · exact h
      · exact absurd hX (hedge s h1 h2 h)
    exact hsS ((hmemS s).mpr ⟨hre0, hre1, him, hz⟩)
  have hsub : rectClosed (-1) 2 (-T) T ⊆ U := by
    intro s hs
    by_cases hsS : s ∈ S
    · exact hgS s hsS
    · intro h0
      apply hXi s hs hsS
      rw [hfac s, show g s = 0 from h0, mul_zero]
  set K : ℂ → ℂ := fun s => deriv g s / g s with hK
  have hKd : DifferentiableOn ℂ K U := fun s hs =>
    (((hg.analyticAt s).deriv.differentiableAt).div (hg s) hs).differentiableWithinAt
  set a₀ : ℂ := 3 / 2 with ha₀
  have ha₀S : a₀ ∉ S := fun h => by
    have := ((hmemS a₀).mp h).2.1
    rw [ha₀] at this; norm_num at this
  set H : ℂ → ℂ → ℂ := fun a => if a = a₀ then (fun s => (s - a₀) * K s * Pent b s)
    else fun s => (analyticOrderNatAt Xi a : ℂ) * Pent b s with hH
  have hPd := differentiable_Pent hb0
  have hres := rectInt_eq_sum_residues (x₁ := -1) (x₂ := 2) (y₁ := -T) (y₂ := T) (by norm_num)
    (by linarith) hUo hsub (insert a₀ S) H ?_ ?_ (F := fun s => deriv Xi s / Xi s * Pent b s) ?_
  · rw [hres, Finset.sum_insert ha₀S]
    simp only [hH, if_true, sub_self, zero_mul, zero_add]
    congr 1
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    have hρa : ρ ≠ a₀ := fun h => ha₀S (h ▸ hρ)
    rw [if_neg hρa]
    obtain ⟨h0, h1, -, -⟩ := (hmemS ρ).mp hρ
    rw [orderNat_Xi h0 h1, Pent_eq (ne_zero_of_re_pos h0) (by rintro rfl; simp at h1)]
  · intro a ha
    by_cases h : a = a₀
    · simp only [hH, h, if_true]
      exact ((differentiableOn_id.sub_const _).mul hKd).mul hPd.differentiableOn
    · simp only [hH, h, if_false]
      exact (hPd.const_mul _).differentiableOn
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · rw [ha₀]; refine ⟨by norm_num, by norm_num, by simp; linarith, by simp; linarith⟩
    · obtain ⟨h0, h1, h2, -⟩ := (hmemS a).mp ha
      rw [abs_lt] at h2
      exact ⟨by linarith, by linarith, h2.1, h2.2⟩
  · intro s hs
    have hsc := rectBdry_subset_closed hs
    have hsS : s ∉ S := by
      intro h
      obtain ⟨h0, h1, h2, -⟩ := (hmemS s).mp h
      rw [abs_lt] at h2
      obtain ⟨-, -, -, -, h' | h' | h' | h'⟩ := hs <;> linarith
    have hsa : s ≠ a₀ := by
      rintro rfl
      obtain ⟨-, -, -, -, h' | h' | h' | h'⟩ := hs <;> simp [ha₀] at h' <;> linarith
    have hgs : g s ≠ 0 := hsub hsc
    have hlog := logDeriv_of_factor hg hfac hsS hgs
    rw [Finset.sum_insert ha₀S]
    simp only [hH, if_true]
    rw [hlog, add_mul, Finset.sum_mul]
    have hsa' : s - a₀ ≠ 0 := sub_ne_zero.mpr hsa
    rw [mul_assoc, mul_div_cancel_left₀ _ hsa', add_comm]
    congr 1
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    have hρa : ρ ≠ a₀ := fun h => ha₀S (h ▸ hρ)
    simp only [hρa, if_false]
    ring

/-- The integrand on the left side is minus the integrand on the right side, reflected. -/
lemma integrand_reflect (b : ℝ) (y : ℝ) :
    deriv Xi (((-1 : ℝ) : ℂ) + y * I) / Xi (((-1 : ℝ) : ℂ) + y * I) *
        Pent b (((-1 : ℝ) : ℂ) + y * I) =
      -(deriv Xi (((2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) / Xi (((2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) *
        Pent b (((2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I)) := by
  have e : ((2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I = 1 - (((-1 : ℝ) : ℂ) + y * I) := by
    push_cast; ring
  have hl0 : ((-1 : ℝ) : ℂ) + y * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have hl1 : ((-1 : ℝ) : ℂ) + y * I ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hr0 : 1 - (((-1 : ℝ) : ℂ) + y * I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have hr1 : 1 - (((-1 : ℝ) : ℂ) + y * I) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this
  rw [e, logDeriv_Xi_one_sub, Pent_eq hl0 hl1, Pent_eq hr0 hr1, tentDephased_one_sub]
  ring

/-- Folding the two vertical sides with `s ↦ 1 - s`. -/
lemma rectInt_fold (b : ℝ) (T : ℝ) :
    rectInt (fun s => deriv Xi s / Xi s * Pent b s) (-1) 2 (-T) T =
      (∫ x in (-1 : ℝ)..2, deriv Xi (x + ((-T : ℝ) : ℂ) * I) / Xi (x + ((-T : ℝ) : ℂ) * I) *
          Pent b (x + ((-T : ℝ) : ℂ) * I)) -
        (∫ x in (-1 : ℝ)..2, deriv Xi (x + (T : ℂ) * I) / Xi (x + (T : ℂ) * I) *
          Pent b (x + (T : ℂ) * I)) +
        2 * I * ∫ y in (-T)..T, deriv Xi (((2 : ℝ) : ℂ) + y * I) / Xi (((2 : ℝ) : ℂ) + y * I) *
          Pent b (((2 : ℝ) : ℂ) + y * I) := by
  unfold rectInt
  have hleft : (∫ y in (-T)..T, deriv Xi (((-1 : ℝ) : ℂ) + y * I) / Xi (((-1 : ℝ) : ℂ) + y * I) *
      Pent b (((-1 : ℝ) : ℂ) + y * I)) =
      -∫ y in (-T)..T, deriv Xi (((2 : ℝ) : ℂ) + y * I) / Xi (((2 : ℝ) : ℂ) + y * I) *
        Pent b (((2 : ℝ) : ℂ) + y * I) := by
    rw [intervalIntegral.integral_congr (g := fun y : ℝ =>
      -(deriv Xi (((2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) / Xi (((2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) *
        Pent b (((2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I))) (fun y _ => integrand_reflect b y),
      intervalIntegral.integral_neg]
    congr 1
    have h := intervalIntegral.integral_comp_neg (a := -T) (b := T) (fun y : ℝ =>
      deriv Xi (((2 : ℝ) : ℂ) + (y : ℂ) * I) / Xi (((2 : ℝ) : ℂ) + (y : ℂ) * I) *
        Pent b (((2 : ℝ) : ℂ) + (y : ℂ) * I))
    simp only [neg_neg] at h
    rw [← h]
  rw [hleft]
  ring

end Rectangle

section GoodHeights

open Complex Set Filter Topology MeasureTheory ComplexConjugate
open TentWidthTwoMargin ZetaExplicit ZetaShared

local notation "γ" => Real.eulerMascheroniConstant

/-! ## 7. Horizontal sides at good heights -/

/-- `∑_{m ≥ 0} 1/(m+1)^2`. -/
def sumInvSq : ℝ := ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2

lemma sumInvSq_nonneg : 0 ≤ sumInvSq := tsum_nonneg fun m => by positivity

lemma norm_logDeriv_Gammaℝ_le {z : ℂ} (h1 : 1 / 2 ≤ z.re) :
    ‖logDeriv Gammaℝ z‖ ≤ Real.log Real.pi / 2 + γ / 2 + 2 * sumInvSq * (‖z‖ / 2 + 1) := by
  rw [TentDigamma.logDeriv_Gammaℝ (by linarith)]
  have hre : 1 / 4 ≤ (z / 2).re := by simp; linarith
  have hψ := TentDigamma.norm_digamma_add_le (δ := 1 / 4) (by norm_num) (by norm_num) hre
  have hz2 : ‖z / 2 - 1‖ ≤ ‖z‖ / 2 + 1 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_div, Complex.norm_ofNat, norm_one]
  have hlogpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hγ : 0 ≤ γ := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hS := sumInvSq_nonneg
  have h1' : ‖-(Real.log Real.pi : ℂ) / 2‖ = Real.log Real.pi / 2 := by
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_of_nonneg hlogpi, Complex.norm_ofNat]
  have h2' : ‖Complex.digamma (z / 2)‖ ≤ ‖Complex.digamma (z / 2) + γ‖ + γ := by
    have := norm_sub_le (Complex.digamma (z / 2) + γ) (γ : ℂ)
    rw [add_sub_cancel_right, Complex.norm_real, Real.norm_of_nonneg hγ] at this
    exact this
  calc ‖-(Real.log Real.pi : ℂ) / 2 + Complex.digamma (z / 2) / 2‖
      ≤ ‖-(Real.log Real.pi : ℂ) / 2‖ + ‖Complex.digamma (z / 2) / 2‖ := norm_add_le _ _
    _ ≤ Real.log Real.pi / 2 + (‖z / 2 - 1‖ / (1 / 4) * sumInvSq + γ) / 2 := by
        rw [h1', norm_div, Complex.norm_ofNat]
        gcongr
        exact h2'.trans (by unfold sumInvSq; linarith)
    _ ≤ Real.log Real.pi / 2 + γ / 2 + 2 * sumInvSq * (‖z‖ / 2 + 1) := by
        have : ‖z / 2 - 1‖ / (1 / 4) * sumInvSq ≤ 4 * sumInvSq * (‖z‖ / 2 + 1) := by
          rw [div_eq_mul_inv, show ((1 : ℝ) / 4)⁻¹ = 4 by norm_num]
          nlinarith
        linarith

lemma norm_logDeriv_Xi_le {z : ℂ} (h1 : 1 / 2 ≤ z.re) (h2 : z.re ≤ 2) (him : 2 ≤ |z.im|)
    (hz : riemannZeta z ≠ 0) :
    ‖deriv Xi z / Xi z‖ ≤ ‖deriv riemannZeta z / riemannZeta z‖ + 1 + Real.log Real.pi / 2 +
      γ / 2 + 2 * sumInvSq * (‖z‖ / 2 + 1) := by
  have hz1 : z ≠ 1 := by rintro rfl; simp at him; linarith
  have hn : 2 ≤ ‖z‖ := him.trans (Complex.abs_im_le_norm z)
  have hn1 : 2 ≤ ‖z - 1‖ := by
    have := Complex.abs_im_le_norm (z - 1); simp at this; linarith
  rw [logDeriv_Xi (by linarith) hz1 hz]
  have e1 : ‖1 / z‖ ≤ 1 / 2 := by
    rw [norm_div, norm_one]; exact div_le_div_of_nonneg_left zero_le_one two_pos hn
  have e2 : ‖1 / (z - 1)‖ ≤ 1 / 2 := by
    rw [norm_div, norm_one]; exact div_le_div_of_nonneg_left zero_le_one two_pos hn1
  have e3 := norm_logDeriv_Gammaℝ_le h1
  calc ‖1 / z + 1 / (z - 1) + logDeriv Gammaℝ z + deriv riemannZeta z / riemannZeta z‖
      ≤ ‖1 / z‖ + ‖1 / (z - 1)‖ + ‖logDeriv Gammaℝ z‖ + ‖deriv riemannZeta z / riemannZeta z‖ :=
        norm_add₄_le
    _ ≤ _ := by linarith

/-- Good heights for `ζ'/ζ`, on both sides of the real axis. -/
lemma good_heights : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧
    ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → |z.im| = T' →
      riemannZeta z ≠ 0 ∧ ‖deriv riemannZeta z / riemannZeta z‖ ≤ C * Real.log (T + 2) ^ 2 := by
  obtain ⟨C, hC, -, -, hhor⟩ := ZetaStrip.stripLogDerivStatement
  refine ⟨C, hC, fun T hT => ?_⟩
  obtain ⟨T', hTT', hT'1, hT'⟩ := hhor T hT
  have hT'0 : 0 < T' := by linarith
  refine ⟨T', hTT', hT'1, fun z h1 h2 him => ?_⟩
  rcases abs_eq hT'0.le |>.mp him with h | h
  · have hz : z = (z.re : ℂ) + (T' : ℂ) * I := by
      apply Complex.ext <;> simp [h]
    rw [hz]
    exact hT' z.re (by linarith) h2
  · have hz : conj z = (z.re : ℂ) + (T' : ℂ) * I := by
      apply Complex.ext <;> simp [h]
    obtain ⟨hne, hb⟩ := hT' z.re (by linarith) h2
    rw [← hz] at hne hb
    refine ⟨?_, by rwa [norm_logDeriv_conj] at hb⟩
    have h' := zeta_conj_ne_zero hne
    rwa [Complex.conj_conj] at h'

end GoodHeights

section HorizontalSides

open Complex Set Filter Topology MeasureTheory ComplexConjugate
open TentWidthTwoMargin ZetaExplicit ZetaShared

local notation "γ" => Real.eulerMascheroniConstant

/-! ## 8. Estimates on the horizontal sides -/

lemma norm_tentNum_le {b : ℝ} (hb : 1 ≤ b) {s : ℂ} {c : ℝ} (h1 : s.re ≤ c) (h2 : 1 - s.re ≤ c) :
    ‖tentNum b s‖ ≤ b + 1 + b ^ c + b ^ c := by
  have hb0 : 0 < b := by linarith
  unfold tentNum
  have e1 : ‖(b : ℂ) ^ s‖ ≤ b ^ c := norm_cpow_ofReal_le hb h1
  have e2 : ‖(b : ℂ) ^ (1 - s)‖ ≤ b ^ c := norm_cpow_ofReal_le hb (by simp; linarith)
  have e3 : ‖(b : ℂ) + 1‖ ≤ b + 1 := by
    rw [show (b : ℂ) + 1 = ((b + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  calc _ ≤ ‖(b : ℂ) + 1‖ + ‖(b : ℂ) ^ s‖ + ‖(b : ℂ) ^ (1 - s)‖ :=
        norm_sub_le_of_le (norm_sub_le _ _) le_rfl
    _ ≤ _ := by linarith

lemma tentDephased_eq_num (b : ℝ) (s : ℂ) :
    tentDephased b s = Real.sqrt b * tentNum b s / (s * (1 - s)) := by
  unfold tentDephased tentNum; ring

lemma norm_tentDephased_le {b : ℝ} (hb : 1 ≤ b) {s : ℂ} {c : ℝ} (h1 : s.re ≤ c) (h2 : 1 - s.re ≤ c)
    {A : ℝ} (hA : 0 < A) (hA' : A ≤ ‖s‖ * ‖1 - s‖) :
    ‖tentDephased b s‖ ≤ Real.sqrt b * (b + 1 + b ^ c + b ^ c) / A := by
  rw [tentDephased_eq_num, norm_div, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg b)]
  gcongr
  exact norm_tentNum_le hb h1 h2

lemma norm_Pent_edge_le {b : ℝ} (hb : 1 < b) {s : ℂ} (h1 : -1 ≤ s.re) (h2 : s.re ≤ 2) {T : ℝ}
    (hT : 0 < T) (him : |s.im| = T) :
    ‖Pent b s‖ ≤ Real.sqrt b * (b + 1 + b ^ (2 : ℝ) + b ^ (2 : ℝ)) / T ^ 2 := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at him; linarith
  have hs1 : s ≠ 1 := by rintro rfl; simp at him; linarith
  rw [Pent_eq hs0 hs1]
  refine norm_tentDephased_le hb.le h2 (by linarith) (by positivity) ?_
  have e1 : T ≤ ‖s‖ := him ▸ Complex.abs_im_le_norm s
  have e2 : T ≤ ‖1 - s‖ := by
    have := Complex.abs_im_le_norm (1 - s)
    simp only [sub_im, one_im, zero_sub, abs_neg] at this
    linarith
  nlinarith

/-- The constant part of the bound for `Ξ'/Ξ` on the horizontal sides. -/
def edgeConst (T : ℝ) : ℝ := 1 + Real.log Real.pi / 2 + γ / 2 + 2 * sumInvSq * ((T + 2) / 2 + 1)

lemma logDeriv_Xi_edge {T Q : ℝ} (hT : 2 ≤ T)
    (hgood : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → |z.im| = T →
      riemannZeta z ≠ 0 ∧ ‖deriv riemannZeta z / riemannZeta z‖ ≤ Q)
    {s : ℂ} (h1 : -1 ≤ s.re) (h2 : s.re ≤ 2) (him : |s.im| = T) :
    Xi s ≠ 0 ∧ ‖deriv Xi s / Xi s‖ ≤ Q + edgeConst T := by
  have key : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → |z.im| = T → ‖z‖ ≤ T + 2 →
      Xi z ≠ 0 ∧ ‖deriv Xi z / Xi z‖ ≤ Q + edgeConst T := by
    intro z hz1 hz2 hzim hzn
    obtain ⟨hz, hzb⟩ := hgood z hz1 hz2 hzim
    have hz1' : z ≠ 1 := by rintro rfl; simp at hzim; linarith
    have hS := sumInvSq_nonneg
    refine ⟨?_, ?_⟩
    · rw [Xi_eq_zeta (by linarith) hz1']
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (ne_zero_of_re_pos (by linarith))
        (sub_ne_zero.mpr hz1')) (Gammaℝ_ne_zero_of_re_pos (by linarith))) hz
    · refine (norm_logDeriv_Xi_le hz1 hz2 (by rw [hzim]; exact hT) hz).trans ?_
      unfold edgeConst
      nlinarith
  have hnorm : ∀ z : ℂ, |z.re| ≤ 2 → |z.im| = T → ‖z‖ ≤ T + 2 := by
    intro z hre hzim
    have := Complex.norm_le_abs_re_add_abs_im z
    linarith
  rcases le_or_gt (1 / 2) s.re with hs | hs
  · exact key s hs h2 him (hnorm s (abs_le.mpr ⟨by linarith, h2⟩) him)
  · have hz1 : 1 / 2 ≤ (1 - s).re := by simp; linarith
    have hz2 : (1 - s).re ≤ 2 := by simp; linarith
    have hzim : |(1 - s).im| = T := by simp [him]
    obtain ⟨hne, hb⟩ := key (1 - s) hz1 hz2 hzim
      (hnorm (1 - s) (abs_le.mpr ⟨by simp; linarith, hz2⟩) hzim)
    refine ⟨?_, ?_⟩
    · have := Xi_one_sub s; rw [this] at hne; exact hne
    · have h := logDeriv_Xi_one_sub s
      rw [h, norm_neg] at hb
      exact hb

/-- Bound for the two horizontal sides of the rectangle at a good height. -/
lemma norm_horizontal_le {b : ℝ} (hb : 1 < b) {T Q : ℝ} (hT : 2 ≤ T) (hQ : 0 ≤ Q)
    (hgood : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → |z.im| = T →
      riemannZeta z ≠ 0 ∧ ‖deriv riemannZeta z / riemannZeta z‖ ≤ Q) :
    ‖(∫ x in (-1 : ℝ)..2, deriv Xi (x + ((-T : ℝ) : ℂ) * I) / Xi (x + ((-T : ℝ) : ℂ) * I) *
          Pent b (x + ((-T : ℝ) : ℂ) * I)) -
        (∫ x in (-1 : ℝ)..2, deriv Xi (x + (T : ℂ) * I) / Xi (x + (T : ℂ) * I) *
          Pent b (x + (T : ℂ) * I))‖ ≤
      6 * ((Q + edgeConst T) * (Real.sqrt b * (b + 1 + b ^ (2 : ℝ) + b ^ (2 : ℝ)) / T ^ 2)) := by
  have hT0 : 0 < T := by linarith
  set B : ℝ := (Q + edgeConst T) * (Real.sqrt b * (b + 1 + b ^ (2 : ℝ) + b ^ (2 : ℝ)) / T ^ 2)
    with hB
  have hpt : ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → |s.im| = T →
      ‖deriv Xi s / Xi s * Pent b s‖ ≤ B := by
    intro s h1 h2 him
    rw [norm_mul]
    exact mul_le_mul (logDeriv_Xi_edge hT hgood h1 h2 him).2
      (norm_Pent_edge_le hb h1 h2 hT0 him) (norm_nonneg _)
      (by have := sumInvSq_nonneg; unfold edgeConst;
          have : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
          have : 0 ≤ γ := by linarith [Real.one_half_lt_eulerMascheroniConstant]
          positivity)
  have hlen : |(2 : ℝ) - -1| = 3 := by norm_num
  have i1 : ‖∫ x in (-1 : ℝ)..2, deriv Xi (x + ((-T : ℝ) : ℂ) * I) / Xi (x + ((-T : ℝ) : ℂ) * I) *
      Pent b (x + ((-T : ℝ) : ℂ) * I)‖ ≤ B * 3 := by
    rw [← hlen]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [uIoc_of_le (by norm_num)] at hx
    exact hpt _ (by simp; linarith [hx.1]) (by simp; linarith [hx.2])
      (by simp [abs_of_pos hT0])
  have i2 : ‖∫ x in (-1 : ℝ)..2, deriv Xi (x + (T : ℂ) * I) / Xi (x + (T : ℂ) * I) *
      Pent b (x + (T : ℂ) * I)‖ ≤ B * 3 := by
    rw [← hlen]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [uIoc_of_le (by norm_num)] at hx
    exact hpt _ (by simp; linarith [hx.1]) (by simp; linarith [hx.2])
      (by simp [abs_of_pos hT0])
  calc _ ≤ B * 3 + B * 3 := (norm_sub_le _ _).trans (add_le_add i1 i2)
    _ = 6 * B := by ring

lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
  rw [Real.log_sqrt hx.le] at h
  linarith [Real.sqrt_nonneg x]

lemma log_sq_le {x : ℝ} (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 4 * x := by
  have h0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 := log_le_two_sqrt (by linarith : 0 < x)
  calc Real.log x ^ 2 ≤ (2 * Real.sqrt x) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = 4 * x := by rw [mul_pow, Real.sq_sqrt (by linarith)]; norm_num

lemma tendsto_edge_bound (C K : ℝ) :
    Tendsto (fun k : ℕ => 6 * ((C * Real.log ((k : ℝ) + 2 + 2) ^ 2 + edgeConst ((k : ℝ) + 2 + 1)) *
      (K / ((k : ℝ) + 2) ^ 2))) atTop (𝓝 0) := by
  set c₁ : ℝ := 1 + Real.log Real.pi / 2 + γ / 2 with hc₁
  have hlim : Tendsto (fun x : ℝ => 6 * ((C * Real.log (x + 2) ^ 2 + edgeConst (x + 1)) *
      (K / x ^ 2))) atTop (𝓝 0) := by
    have hA : Tendsto (fun x : ℝ => Real.log (x + 2) ^ 2 / x ^ 2) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun x => by positivity) ?_
        (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun x : ℝ => 12 / x) atTop (𝓝 0))
      filter_upwards [eventually_ge_atTop 1] with x hx
      have h1 := log_sq_le (x := x + 2) (by linarith)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hB : Tendsto (fun x : ℝ => edgeConst (x + 1) / x ^ 2) atTop (𝓝 0) := by
      have e : (fun x : ℝ => edgeConst (x + 1) / x ^ 2) =
          fun x => (c₁ + 2 * sumInvSq * 2.5) * (x ^ 2)⁻¹ + sumInvSq * x⁻¹ := by
        funext x
        unfold edgeConst
        rcases eq_or_ne x 0 with rfl | hx
        · simp
        · field_simp; ring
      rw [e]
      have h2 : Tendsto (fun x : ℝ => (x ^ 2)⁻¹) atTop (𝓝 0) :=
        (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).inv_tendsto_atTop
      simpa using (h2.const_mul _).add (tendsto_inv_atTop_zero.const_mul sumInvSq)
    have h := ((hA.const_mul C).add hB).const_mul (6 * K)
    simp only [mul_zero, zero_add] at h
    refine h.congr' (Eventually.of_forall fun x => ?_)
    ring
  have hk : Tendsto (fun k : ℕ => (k : ℝ) + 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  refine (hlim.comp hk).congr' (Eventually.of_forall fun k => ?_)
  simp only [Function.comp_apply]

end HorizontalSides

section ZeroSums

open Complex Set Filter Topology MeasureTheory
open TentWidthTwoMargin ZetaExplicit ZetaShared

/-! ## 9. Summing over the zeros -/

/-- The nontrivial zeros of `ζ`. -/
def zeros : Set ℂ := {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0}

lemma summable_count_weights (C : ℝ) :
    Summable (fun k : ℕ => 2 * C * Real.log ((k : ℝ) + 2) / (1 + (k : ℝ) ^ 2)) := by
  refine Summable.of_norm_bounded
    ((TentDigamma.summable_inv_mul_sqrt).mul_left (8 * Real.sqrt 2 * |C|)) fun k => ?_
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  set r : ℝ := Real.sqrt ((k : ℝ) + 1) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hk1
  have hlog0 : 0 ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hlog : Real.log ((k : ℝ) + 2) ≤ 2 * Real.sqrt 2 * r := by
    calc Real.log ((k : ℝ) + 2) ≤ 2 * Real.sqrt ((k : ℝ) + 2) := log_le_two_sqrt (by positivity)
      _ ≤ 2 * (Real.sqrt 2 * r) := by
          rw [hr, ← Real.sqrt_mul (by norm_num)]; gcongr; linarith
      _ = 2 * Real.sqrt 2 * r := by ring
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_of_nonneg hlog0, abs_two,
    abs_of_pos (by positivity : (0 : ℝ) < 1 + k ^ 2), mul_one_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : (0 : ℝ) ≤ Real.sqrt 2 * |C| := by positivity
  calc 2 * |C| * Real.log ((k : ℝ) + 2) * (((k : ℝ) + 1) * r)
      ≤ 2 * |C| * (2 * Real.sqrt 2 * r) * (((k : ℝ) + 1) * r) := by gcongr
    _ = 4 * (Real.sqrt 2 * |C|) * ((k : ℝ) + 1) * (r * r) := by ring
    _ = 4 * (Real.sqrt 2 * |C|) * ((k : ℝ) + 1) * ((k : ℝ) + 1) := by
        rw [hr, Real.mul_self_sqrt hk1.le]
    _ ≤ 8 * Real.sqrt 2 * |C| * (1 + (k : ℝ) ^ 2) := by
        nlinarith [mul_nonneg h2 (sq_nonneg ((k : ℝ) - 1))]

lemma finsum_weight_le {C : ℝ} (hcount : ∀ t : ℝ, (zerosNear t).Finite ∧
      ∑ᶠ ρ ∈ zerosNear t, (mult ρ : ℝ) ≤ C * Real.log (|t| + 2)) (K : ℕ) :
    ∑ᶠ ρ ∈ zerosBelow (K : ℝ), (mult ρ : ℝ) / (1 + ρ.im ^ 2) ≤
      ∑ k ∈ Finset.range K, 2 * C * Real.log ((k : ℝ) + 2) / (1 + (k : ℝ) ^ 2) := by
  induction K with
  | zero =>
    have h : zerosBelow ((0 : ℕ) : ℝ) = ∅ :=
      Set.eq_empty_of_forall_notMem fun ρ hρ => absurd hρ.2.2.1 (by simp)
    rw [h, finsum_mem_empty, Finset.range_zero, Finset.sum_empty]
  | succ K ih =>
    set D : Set ℂ := zerosBelow ((K + 1 : ℕ) : ℝ) \ zerosBelow (K : ℝ) with hD
    have hDfin : D.Finite := (zerosBelow_finite _).subset sdiff_subset
    have hmono : zerosBelow (K : ℝ) ⊆ zerosBelow ((K + 1 : ℕ) : ℝ) :=
      zerosBelow_mono (by push_cast; linarith)
    have hsplit : ∑ᶠ ρ ∈ zerosBelow ((K + 1 : ℕ) : ℝ), (mult ρ : ℝ) / (1 + ρ.im ^ 2) =
        ∑ᶠ ρ ∈ zerosBelow (K : ℝ), (mult ρ : ℝ) / (1 + ρ.im ^ 2) +
          ∑ᶠ ρ ∈ D, (mult ρ : ℝ) / (1 + ρ.im ^ 2) := by
      rw [← finsum_mem_union disjoint_sdiff_right (zerosBelow_finite _) hDfin,
        union_sdiff_cancel hmono]
    rw [hsplit, Finset.sum_range_succ]
    refine add_le_add ih ?_
    have hDsub := diff_subset_near (T := (K : ℝ)) (T' := ((K + 1 : ℕ) : ℝ)) (by push_cast; linarith)
    have hnear : (zerosNear (K : ℝ) ∪ zerosNear (-(K : ℝ))).Finite :=
      (hcount K).1.union (hcount (-K)).1
    have hmultD : ∑ᶠ ρ ∈ D, (mult ρ : ℝ) ≤ 2 * C * Real.log ((K : ℝ) + 2) := by
      have h1 : ∑ᶠ ρ ∈ D, (mult ρ : ℝ) ≤
          ∑ᶠ ρ ∈ zerosNear (K : ℝ) ∪ zerosNear (-(K : ℝ)), (mult ρ : ℝ) :=
        ZetaCount.finsum_mem_le_of_subset_of_nonneg hDsub hnear fun _ => Nat.cast_nonneg _
      have h2 := finsum_mem_union_inter (f := fun ρ : ℂ => (mult ρ : ℝ)) (hcount K).1
        (hcount (-K)).1
      have h3 : 0 ≤ ∑ᶠ ρ ∈ zerosNear (K : ℝ) ∩ zerosNear (-(K : ℝ)), (mult ρ : ℝ) :=
        finsum_nonneg fun ρ => finsum_nonneg fun _ => Nat.cast_nonneg _
      have h4 := (hcount K).2
      have h5 := (hcount (-K)).2
      rw [abs_neg] at h5
      rw [abs_of_nonneg (Nat.cast_nonneg K)] at h4 h5
      linarith
    calc ∑ᶠ ρ ∈ D, (mult ρ : ℝ) / (1 + ρ.im ^ 2) ≤
          ∑ᶠ ρ ∈ D, (mult ρ : ℝ) / (1 + (K : ℝ) ^ 2) := by
          rw [finsum_mem_eq_finite_toFinset_sum _ hDfin, finsum_mem_eq_finite_toFinset_sum _ hDfin]
          refine Finset.sum_le_sum fun ρ hρ => ?_
          rw [Set.Finite.mem_toFinset] at hρ
          obtain ⟨⟨h0, h1, h2, hz⟩, hn⟩ := hρ
          have hge : (K : ℝ) ≤ |ρ.im| := by
            by_contra h
            exact hn ⟨h0, h1, not_le.mp h, hz⟩
          have hsq : (K : ℝ) ^ 2 ≤ ρ.im ^ 2 := by
            rw [← sq_abs ρ.im]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) hge 2
          exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) (by linarith)
      _ = (∑ᶠ ρ ∈ D, (mult ρ : ℝ)) / (1 + (K : ℝ) ^ 2) := by
          rw [finsum_mem_eq_finite_toFinset_sum _ hDfin, finsum_mem_eq_finite_toFinset_sum _ hDfin,
            Finset.sum_div]
      _ ≤ 2 * C * Real.log ((K : ℝ) + 2) / (1 + (K : ℝ) ^ 2) := by gcongr

theorem summable_mult_weight :
    Summable (fun ρ : zeros => (mult (ρ : ℂ) : ℝ) / (1 + (ρ : ℂ).im ^ 2)) := by
  obtain ⟨C, hC, hcount⟩ := ZetaCount.zeroCountStatement
  have ha0 : ∀ k : ℕ, 0 ≤ 2 * C * Real.log ((k : ℝ) + 2) / (1 + (k : ℝ) ^ 2) := fun k => by
    have : 0 ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k])
    positivity
  refine summable_of_sum_le
    (c := ∑' k : ℕ, 2 * C * Real.log ((k : ℝ) + 2) / (1 + (k : ℝ) ^ 2))
    (fun ρ => by positivity) fun u => ?_
  set K : ℕ := ⌈∑ ρ ∈ u, |(ρ : ℂ).im|⌉₊ + 1 with hK
  have hKu : ∀ ρ ∈ u, |(ρ : ℂ).im| < K := by
    intro ρ hρ
    have h1 : |(ρ : ℂ).im| ≤ ∑ ρ ∈ u, |(ρ : ℂ).im| :=
      Finset.single_le_sum (f := fun ρ : zeros => |(ρ : ℂ).im|) (fun _ _ => abs_nonneg _) hρ
    have h2 : ∑ ρ ∈ u, |(ρ : ℂ).im| ≤ ⌈∑ ρ ∈ u, |(ρ : ℂ).im|⌉₊ := Nat.le_ceil _
    rw [hK]; push_cast; linarith
  calc ∑ ρ ∈ u, (mult (ρ : ℂ) : ℝ) / (1 + (ρ : ℂ).im ^ 2)
      = ∑ z ∈ u.map (Function.Embedding.subtype _), (mult z : ℝ) / (1 + z.im ^ 2) := by
        rw [Finset.sum_map]; rfl
    _ ≤ ∑ᶠ z ∈ zerosBelow (K : ℝ), (mult z : ℝ) / (1 + z.im ^ 2) := by
        rw [finsum_mem_eq_finite_toFinset_sum _ (zerosBelow_finite _)]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
        intro z hz
        rw [Finset.mem_map] at hz
        obtain ⟨ρ, hρ, rfl⟩ := hz
        rw [Set.Finite.mem_toFinset]
        exact ⟨ρ.2.1, ρ.2.2.1, hKu ρ hρ, ρ.2.2.2⟩
    _ ≤ ∑ k ∈ Finset.range K, 2 * C * Real.log ((k : ℝ) + 2) / (1 + (k : ℝ) ^ 2) :=
        finsum_weight_le hcount K
    _ ≤ _ := (summable_count_weights C).sum_le_tsum _ (fun k _ => ha0 k)

theorem summable_mult_norm {b : ℝ} (hb : 1 < b) :
    Summable (fun ρ : zeros => (mult (ρ : ℂ) : ℝ) * ‖tentDephased b ρ‖) := by
  classical
  set Kb : ℝ := Real.sqrt b * (b + 1 + b ^ (1 : ℝ) + b ^ (1 : ℝ)) with hKb
  have hKb0 : 0 ≤ Kb := by
    have : 0 ≤ b ^ (1 : ℝ) := Real.rpow_nonneg (by linarith) _
    positivity
  have hfin : {ρ : zeros | |(ρ : ℂ).im| < 1}.Finite := by
    have h := (zerosBelow_finite 1).preimage (f := (Subtype.val : zeros → ℂ))
      Subtype.val_injective.injOn
    exact h.subset fun ρ hρ => ⟨ρ.2.1, ρ.2.2.1, hρ, ρ.2.2.2⟩
  have h1 : Summable (fun ρ : zeros =>
      if |(ρ : ℂ).im| < 1 then (mult (ρ : ℂ) : ℝ) * ‖tentDephased b ρ‖ else 0) := by
    apply summable_of_hasFiniteSupport
    refine hfin.subset fun ρ hρ => ?_
    by_contra h
    exact hρ (if_neg h)
  have h2 : Summable (fun ρ : zeros =>
      if |(ρ : ℂ).im| < 1 then 0 else (mult (ρ : ℂ) : ℝ) * ‖tentDephased b ρ‖) := by
    refine Summable.of_nonneg_of_le (fun ρ => by split_ifs <;> positivity) (fun ρ => ?_)
      (summable_mult_weight.mul_left (2 * Kb))
    split_ifs with h
    · have : 0 ≤ (mult (ρ : ℂ) : ℝ) / (1 + (ρ : ℂ).im ^ 2) := by positivity
      positivity
    · rw [not_lt] at h
      obtain ⟨h0, h1, -⟩ := ρ.2
      have hsq : 1 ≤ (ρ : ℂ).im ^ 2 := by rw [← sq_abs]; nlinarith
      have hA : (ρ : ℂ).im ^ 2 ≤ ‖(ρ : ℂ)‖ * ‖1 - (ρ : ℂ)‖ := by
        have e1 := Complex.abs_im_le_norm (ρ : ℂ)
        have e2 := Complex.abs_im_le_norm (1 - (ρ : ℂ))
        simp only [sub_im, one_im, zero_sub, abs_neg] at e2
        rw [← sq_abs]
        nlinarith [abs_nonneg (ρ : ℂ).im]
      have hP := norm_tentDephased_le hb.le (s := (ρ : ℂ)) (c := 1) h1.le (by linarith)
        (by positivity) hA
      have hP' : ‖tentDephased b ρ‖ ≤ 2 * Kb / (1 + (ρ : ℂ).im ^ 2) := by
        refine hP.trans ?_
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      calc (mult (ρ : ℂ) : ℝ) * ‖tentDephased b ρ‖ ≤
          (mult (ρ : ℂ) : ℝ) * (2 * Kb / (1 + (ρ : ℂ).im ^ 2)) :=
            mul_le_mul_of_nonneg_left hP' (Nat.cast_nonneg _)
        _ = 2 * Kb * ((mult (ρ : ℂ) : ℝ) / (1 + (ρ : ℂ).im ^ 2)) := by ring
  exact (h1.add h2).congr fun ρ => by split_ifs <;> simp

end ZeroSums

section Limit

open Complex Set Filter Topology MeasureTheory
open TentWidthTwoMargin ZetaExplicit ZetaShared

/-! ## 10. From the rectangles to the line -/

lemma edgeConst_mono {T T' : ℝ} (h : T ≤ T') : edgeConst T ≤ edgeConst T' := by
  unfold edgeConst
  have := sumInvSq_nonneg
  nlinarith

/-- **The sum over the zeros as a line integral.** Given integrability on `re s = 2`,
`∑_ρ m_ρ P_b(ρ) = (1/π) ∫ Ξ'/Ξ(2 + it) P_b(2 + it) dt`. -/
theorem hasSum_zeros_eq_line {b : ℝ} (hb : 1 < b)
    (hint : Integrable fun t : ℝ =>
      deriv Xi (2 + t * I) / Xi (2 + t * I) * tentDephased b (2 + t * I)) :
    HasSum (fun ρ : zeros => (mult (ρ : ℂ) : ℂ) * tentDephased b ρ)
      ((∫ t : ℝ, deriv Xi (2 + t * I) / Xi (2 + t * I) * tentDephased b (2 + t * I)) /
        Real.pi) := by
  classical
  have hb0 : 0 < b := by linarith
  set F : ℝ → ℂ := fun t => deriv Xi (2 + t * I) / Xi (2 + t * I) * tentDephased b (2 + t * I)
    with hF
  set f : zeros → ℂ := fun ρ => (mult (ρ : ℂ) : ℂ) * tentDephased b ρ with hf
  have hsum : Summable f := by
    refine Summable.of_norm ((summable_mult_norm hb).congr fun ρ => ?_)
    rw [hf, norm_mul, Complex.norm_natCast]
  obtain ⟨Z, hZ⟩ := hsum
  obtain ⟨C, hC, hgood⟩ := good_heights
  have hT : ∀ k : ℕ, (2 : ℝ) ≤ (k : ℝ) + 2 := fun k => by linarith [Nat.cast_nonneg (α := ℝ) k]
  choose T' hT'1 hT'2 hT'3 using fun k : ℕ => hgood ((k : ℝ) + 2) (hT k)
  have hT'2le : ∀ k, (2 : ℝ) ≤ T' k := fun k => (hT k).trans (hT'1 k)
  have hT'pos : ∀ k, 0 < T' k := fun k => by linarith [hT'2le k]
  set S : ℕ → Finset ℂ := fun k => (zerosBelow_finite (T' k)).toFinset with hS
  set H : ℕ → ℂ := fun k =>
    (∫ x in (-1 : ℝ)..2, deriv Xi (x + ((-T' k : ℝ) : ℂ) * I) / Xi (x + ((-T' k : ℝ) : ℂ) * I) *
        Pent b (x + ((-T' k : ℝ) : ℂ) * I)) -
      (∫ x in (-1 : ℝ)..2, deriv Xi (x + (T' k : ℂ) * I) / Xi (x + (T' k : ℂ) * I) *
        Pent b (x + (T' k : ℂ) * I)) with hH
  -- the identity at each good height
  have hid : ∀ k, 2 * Real.pi * I * ∑ ρ ∈ S k, (mult ρ : ℂ) * tentDephased b ρ =
      H k + 2 * I * ∫ y in (-T' k)..(T' k), F y := by
    intro k
    have hedge : ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → |s.im| = T' k → Xi s ≠ 0 :=
      fun s h1 h2 him => (logDeriv_Xi_edge (hT'2le k) (hT'3 k) h1 h2 him).1
    rw [← rect_residues hb (hT'pos k) hedge, rectInt_fold]
    congr 2
    refine intervalIntegral.integral_congr fun y _ => ?_
    have h0 : ((2 : ℝ) : ℂ) + y * I ≠ 0 := ne_zero_of_two_le_re (by simp)
    have h1 : ((2 : ℝ) : ℂ) + y * I ≠ 1 := ne_one_of_two_le_re (by simp)
    simp only [hF]
    rw [Pent_eq h0 h1]
    norm_num
  -- the finite sums tend to the full sum
  set u : ℕ → Finset zeros := fun k => (S k).subtype (· ∈ zeros) with hu
  have hSu : ∀ k, ∑ ρ ∈ S k, (mult ρ : ℂ) * tentDephased b ρ = ∑ x ∈ u k, f x := by
    intro k
    rw [hu, hf]
    simp only
    rw [Finset.sum_subtype_of_mem (f := fun ρ : ℂ => (mult ρ : ℂ) * tentDephased b ρ)]
    intro x hx
    rw [hS, Set.Finite.mem_toFinset] at hx
    exact ⟨hx.1, hx.2.1, hx.2.2.2⟩
  have hmem : ∀ k (x : zeros), x ∈ u k ↔ |(x : ℂ).im| < T' k := by
    intro k x
    rw [hu, Finset.mem_subtype, hS, Set.Finite.mem_toFinset]
    exact ⟨fun h => h.2.2.1, fun h => ⟨x.2.1, x.2.2.1, h, x.2.2.2⟩⟩
  have hmono : Monotone u := by
    refine monotone_nat_of_le_succ fun k x hx => ?_
    rw [hmem] at hx ⊢
    have : T' k ≤ T' (k + 1) := by
      have h1 := hT'2 k
      have h2 := hT'1 (k + 1)
      push_cast at h2
      linarith
    linarith
  have hexh : ∀ x : zeros, ∃ k, x ∈ u k := by
    intro x
    obtain ⟨k, hk⟩ := exists_nat_gt |(x : ℂ).im|
    refine ⟨k, (hmem k x).mpr ?_⟩
    linarith [hT'1 k]
  have hlimS : Tendsto (fun k => 2 * Real.pi * I * ∑ ρ ∈ S k, (mult ρ : ℂ) * tentDephased b ρ)
      atTop (𝓝 (2 * Real.pi * I * Z)) := by
    simp only [hSu]
    exact (hZ.comp (tendsto_atTop_finset_of_monotone hmono hexh)).const_mul _
  -- the line integrals
  have hTinf : Tendsto T' atTop atTop :=
    tendsto_atTop_mono hT'1 (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hlimI : Tendsto (fun k => ∫ y in (-T' k)..(T' k), F y) atTop (𝓝 (∫ y, F y)) :=
    intervalIntegral_tendsto_integral hint (tendsto_neg_atTop_atBot.comp hTinf) hTinf
  -- the horizontal sides
  set Kb : ℝ := Real.sqrt b * (b + 1 + b ^ (2 : ℝ) + b ^ (2 : ℝ)) with hKb
  have hKb0 : 0 ≤ Kb := by
    have : 0 ≤ b ^ (2 : ℝ) := Real.rpow_nonneg hb0.le _
    positivity
  have hHb : ∀ k, ‖H k‖ ≤ 6 * ((C * Real.log ((k : ℝ) + 2 + 2) ^ 2 +
      edgeConst ((k : ℝ) + 2 + 1)) * (Kb / ((k : ℝ) + 2) ^ 2)) := by
    intro k
    have hQ : 0 ≤ C * Real.log ((k : ℝ) + 2 + 2) ^ 2 := by positivity
    refine (norm_horizontal_le hb (hT'2le k) hQ (hT'3 k)).trans ?_
    have he : edgeConst (T' k) ≤ edgeConst ((k : ℝ) + 2 + 1) := edgeConst_mono (hT'2 k)
    have he0 : 0 ≤ edgeConst (T' k) := by
      unfold edgeConst
      have := sumInvSq_nonneg
      have : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
      have : 0 ≤ Real.eulerMascheroniConstant := by
        linarith [Real.one_half_lt_eulerMascheroniConstant]
      have := hT'pos k
      positivity
    have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by linarith [hT k]
    have hd : Kb / T' k ^ 2 ≤ Kb / ((k : ℝ) + 2) ^ 2 :=
      div_le_div_of_nonneg_left hKb0 (by positivity) (pow_le_pow_left₀ hk2.le (hT'1 k) 2)
    have hstep : (C * Real.log ((k : ℝ) + 2 + 2) ^ 2 + edgeConst (T' k)) * (Kb / T' k ^ 2) ≤
        (C * Real.log ((k : ℝ) + 2 + 2) ^ 2 + edgeConst ((k : ℝ) + 2 + 1)) *
          (Kb / ((k : ℝ) + 2) ^ 2) :=
      mul_le_mul (by linarith) hd (by positivity) (by linarith)
    linarith
  have hlimH : Tendsto H atTop (𝓝 0) :=
    squeeze_zero_norm hHb (tendsto_edge_bound C Kb)
  have hlimR : Tendsto (fun k => H k + 2 * I * ∫ y in (-T' k)..(T' k), F y) atTop
      (𝓝 (0 + 2 * I * ∫ y, F y)) := hlimH.add (hlimI.const_mul _)
  have heq : 2 * Real.pi * I * Z = 0 + 2 * I * ∫ y, F y :=
    tendsto_nhds_unique hlimS (hlimR.congr fun k => (hid k).symm)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hZv : Z = (∫ y, F y) / Real.pi := by
    rw [zero_add] at heq
    have h2I : (2 * I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
    have h' : (2 * I) * (Real.pi * Z) = (2 * I) * ∫ y, F y := by linear_combination heq
    rw [eq_div_iff hpi, mul_comm]
    exact mul_left_cancel₀ h2I h'
  rw [← hZv]
  exact hZ

end Limit

section ClosedForms

open Complex Set Filter Topology MeasureTheory
open scoped ArithmeticFunction.vonMangoldt LSeries.notation
open TentWidthTwoMargin ZetaExplicit ZetaShared

local notation "γ" => Real.eulerMascheroniConstant

/-! ## 11. The line integral in closed form -/

lemma continuousAt_tentDephased {b : ℝ} (hb : 0 < b) {s : ℂ} (hs : 2 ≤ s.re) :
    ContinuousAt (tentDephased b) s := by
  have h0 := ne_zero_of_two_le_re hs
  have h1 := ne_one_of_two_le_re hs
  have e : tentDephased b = fun z => Real.sqrt b * tentNum b z / (z * (1 - z)) :=
    funext (tentDephased_eq_num b)
  rw [e]
  exact (continuousAt_const.mul (differentiable_tentNum hb).continuous.continuousAt).div
    (continuousAt_id.mul (continuousAt_const.sub continuousAt_id))
    (mul_ne_zero h0 (sub_ne_zero.mpr h1.symm))

lemma continuous_tentDephased_line {b : ℝ} (hb : 0 < b) :
    Continuous fun t : ℝ => tentDephased b (2 + t * I) :=
  continuous_line fun _ hs => continuousAt_tentDephased hb hs

lemma continuousAt_logDeriv_zeta {s : ℂ} (hs : 2 ≤ s.re) :
    ContinuousAt (fun z => deriv riemannZeta z / riemannZeta z) s := by
  have h1 := ne_one_of_two_le_re hs
  have hA := ZetaCount.analyticAt_zeta h1
  exact hA.deriv.continuousAt.div hA.continuousAt
    (riemannZeta_ne_zero_of_one_le_re (by linarith))

lemma continuousAt_logDeriv_Xi {s : ℂ} (hs : 2 ≤ s.re) :
    ContinuousAt (fun z => deriv Xi z / Xi z) s := by
  have hA := differentiable_Xi.analyticAt s
  exact hA.deriv.continuousAt.div hA.continuousAt (Xi_ne_zero_of_one_le_re (by linarith))

/-! ### The primes -/

lemma logDeriv_zeta_eq_neg_tsum {s : ℂ} (hs : 1 < s.re) :
    deriv riemannZeta s / riemannZeta s = -∑' n : ℕ, LSeries.term ↗Λ s n := by
  have h := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  rw [LSeries] at h
  rw [h]; ring

lemma integral_term_mul {b : ℝ} (hb : 1 < b) (n : ℕ) :
    Integrable (fun t : ℝ => LSeries.term ↗Λ (2 + t * I) n * tentDephased b (2 + t * I)) ∧
    ∫ t : ℝ, LSeries.term ↗Λ (2 + t * I) n * tentDephased b (2 + t * I) =
      2 * Real.pi * Real.sqrt b *
        (if n ≤ ⌊b⌋₊ then (Λ n : ℂ) * ((b : ℂ) / n - 1) else 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn1 : 1 ≤ n := hn
  have hne : n ≠ 0 := by omega
  have hfun : (fun t : ℝ => LSeries.term ↗Λ (2 + t * I) n * tentDephased b (2 + t * I)) =
      fun t : ℝ => (Λ n : ℂ) * (((n : ℂ) ^ (2 + t * I))⁻¹ * tentDephased b (2 + t * I)) := by
    funext t
    rw [LSeries.term_of_ne_zero hne, div_eq_mul_inv]
    ring
  rw [hfun]
  by_cases hnb : n ≤ ⌊b⌋₊
  · have hnb' : (n : ℝ) ≤ b := (Nat.le_floor_iff (by linarith)).mp hnb
    obtain ⟨hi, he⟩ := integral_natCpow_inv_mul_of_le hb hn1 hnb'
    refine ⟨hi.const_mul _, ?_⟩
    rw [integral_const_mul, he, if_pos hnb]
    ring
  · have hnb' : b < n := by
      by_contra h
      exact hnb ((Nat.le_floor_iff (by linarith)).mpr (not_lt.mp h))
    obtain ⟨hi, he⟩ := integral_natCpow_inv_mul_of_lt hb hnb'
    refine ⟨hi.const_mul _, ?_⟩
    rw [integral_const_mul, he, if_neg hnb]
    ring

/-- The prime-power ramp `∑_{n ≤ b} Λ(n) (b/n - 1)`. -/
def primeRamp (b : ℝ) : ℝ := ∑ n ∈ Finset.range (⌊b⌋₊ + 1), Λ n * (b / n - 1)

theorem integral_logDeriv_zeta_mul {b : ℝ} (hb : 1 < b) :
    Integrable (fun t : ℝ => deriv riemannZeta (2 + t * I) / riemannZeta (2 + t * I) *
      tentDephased b (2 + t * I)) ∧
    ∫ t : ℝ, deriv riemannZeta (2 + t * I) / riemannZeta (2 + t * I) * tentDephased b (2 + t * I) =
      -(2 * Real.pi * Real.sqrt b * (primeRamp b : ℂ)) := by
  have hb0 : 0 < b := by linarith
  obtain ⟨hP, -⟩ := integral_tentDephased hb
  have hre : ∀ t : ℝ, 1 < ((2 : ℂ) + t * I).re := fun t => by simp
  -- integrability: bounded times integrable
  have hbound : ∀ t : ℝ, ‖deriv riemannZeta (2 + t * I) / riemannZeta (2 + t * I)‖ ≤
      ‖deriv riemannZeta 2 / riemannZeta 2‖ := by
    intro t
    have h := norm_logDeriv_le_real (hre t)
    simpa using h
  have hcont : Continuous fun t : ℝ => deriv riemannZeta (2 + t * I) / riemannZeta (2 + t * I) *
      tentDephased b (2 + t * I) :=
    (continuous_line fun s hs => continuousAt_logDeriv_zeta hs).mul
      (continuous_tentDephased_line hb0)
  have hint : Integrable fun t : ℝ => deriv riemannZeta (2 + t * I) / riemannZeta (2 + t * I) *
      tentDephased b (2 + t * I) := by
    refine Integrable.mono' (hP.norm.const_mul ‖deriv riemannZeta 2 / riemannZeta 2‖)
      hcont.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _)
  refine ⟨hint, ?_⟩
  -- Fubini over the Dirichlet series
  set G : ℕ → ℝ → ℂ := fun n t => LSeries.term ↗Λ (2 + t * I) n * tentDephased b (2 + t * I)
    with hG
  have hGint : ∀ n, Integrable (G n) := fun n => (integral_term_mul hb n).1
  have hnorm : ∀ n (t : ℝ), ‖G n t‖ = ‖LSeries.term ↗Λ 2 n‖ * ‖tentDephased b (2 + t * I)‖ := by
    intro n t
    rw [hG, norm_mul, LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp
  have hsumm : Summable fun n => ∫ t, ‖G n t‖ := by
    have hs := (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := 2) (by norm_num)).norm
    refine (hs.mul_right (∫ t : ℝ, ‖tentDephased b (2 + t * I)‖)).congr fun n => ?_
    simp only [hnorm]
    rw [integral_const_mul]
  have hF := integral_tsum_of_summable_integral_norm hGint hsumm
  have hline : (fun t : ℝ => deriv riemannZeta (2 + t * I) / riemannZeta (2 + t * I) *
      tentDephased b (2 + t * I)) = fun t => -∑' n, G n t := by
    funext t
    rw [logDeriv_zeta_eq_neg_tsum (hre t), hG, neg_mul, tsum_mul_right]
  rw [hline, integral_neg, ← hF]
  congr 1
  have hval : ∀ n, ∫ t, G n t = 2 * Real.pi * Real.sqrt b *
      (if n ≤ ⌊b⌋₊ then (Λ n : ℂ) * ((b : ℂ) / n - 1) else 0) := fun n => (integral_term_mul hb n).2
  rw [tsum_congr hval, tsum_mul_left, tsum_eq_sum (s := Finset.range (⌊b⌋₊ + 1))]
  · unfold primeRamp
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))]
  · intro n hn
    rw [if_neg]
    intro h
    exact hn (Finset.mem_range.mpr (Nat.lt_succ_of_le h))

/-! ### The digamma series -/

lemma hasSum_telescope {f : ℕ → ℝ} (hf : Antitone f) (hlim : Tendsto f atTop (𝓝 0)) :
    HasSum (fun m => f m - f (m + 1)) (f 0) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun m => sub_nonneg.mpr (hf (Nat.le_succ m)))]
  have e : (fun n => ∑ i ∈ Finset.range n, (f i - f (i + 1))) = fun n => f 0 - f n := by
    funext n; exact Finset.sum_range_sub' f n
  rw [e]
  have h := (tendsto_const_nhds (x := f 0)).sub hlim
  rwa [sub_zero] at h

lemma tendsto_inv_linear (a c : ℝ) (ha : 0 < a) :
    Tendsto (fun m : ℕ => 1 / (a * (m : ℝ) + c)) atTop (𝓝 0) := by
  have h : Tendsto (fun m : ℕ => a * (m : ℝ) + c) atTop atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop ha).atTop_add tendsto_const_nhds
  refine Tendsto.congr (fun m => ?_) h.inv_tendsto_atTop
  simp [one_div]

/-- `∑_{m ≥ 0} (1/(2(m+2)) - 1/(2(m+1))) = -1/2`. -/
lemma hasSum_alpha :
    HasSum (fun m : ℕ => 1 / (2 * ((m : ℝ) + 1 + 1)) - 1 / (2 * ((m : ℝ) + 1))) (-1 / 2) := by
  have h := hasSum_telescope (f := fun m : ℕ => 1 / (2 * (m : ℝ) + 2))
    (fun m n hmn => by
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      exact one_div_le_one_div_of_le (by positivity) (by linarith))
    (tendsto_inv_linear 2 2 two_pos)
  have e : (-1 / 2 : ℝ) = -(1 / (2 * ((0 : ℕ) : ℝ) + 2)) := by norm_num
  rw [e]
  exact h.neg.congr_fun fun m => by push_cast; ring

/-- `∑_{m ≥ 0} 1/((2(m+1))(2(m+1)+1)) = 1 - log 2`. -/
lemma hasSum_beta :
    HasSum (fun m : ℕ => 1 / (2 * ((m : ℝ) + 1) * (2 * ((m : ℝ) + 1) + 1))) (1 - Real.log 2) := by
  have h1 := hasSum_telescope (f := fun m : ℕ => 1 / (2 * (m : ℝ) + 1))
    (fun m n hmn => by
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      exact one_div_le_one_div_of_le (by positivity) (by linarith))
    (tendsto_inv_linear 2 1 two_pos)
  have h2 := h1.sub TentDigamma.hasSum_log_two
  have e : (1 - Real.log 2 : ℝ) = 1 / (2 * ((0 : ℕ) : ℝ) + 1) - Real.log 2 := by norm_num
  rw [e]
  refine h2.congr_fun fun m => ?_
  have hm1 : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
  have hm2 : (0 : ℝ) < 2 * (m : ℝ) + 2 := by positivity
  have hm3 : (0 : ℝ) < 2 * (m : ℝ) + 3 := by positivity
  push_cast
  field_simp
  ring

/-- The trivial-zero series `∑_{k ≥ 0} b^{-2(k+1)}/((2(k+1))(2(k+1)+1))`. -/
def trivialSum (b : ℝ) : ℝ :=
  ∑' k : ℕ, (1 : ℝ) / ((b ^ 2) ^ (k + 1) * (2 * (k + 1)) * (2 * (k + 1) + 1))

lemma summable_trivial {b : ℝ} (hb : 1 ≤ b) :
    Summable fun k : ℕ => (1 : ℝ) / ((b ^ 2) ^ (k + 1) * (2 * (k + 1)) * (2 * (k + 1) + 1)) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hasSum_beta.summable
  have h1 : (1 : ℝ) ≤ (b ^ 2) ^ (k + 1) := one_le_pow₀ (by nlinarith)
  have h2 : (0 : ℝ) < 2 * ((k : ℝ) + 1) * (2 * ((k : ℝ) + 1) + 1) := by positivity
  rw [mul_assoc]
  calc (1 : ℝ) / ((b ^ 2) ^ (k + 1) * (2 * ((k : ℝ) + 1) * (2 * ((k : ℝ) + 1) + 1)))
      ≤ 1 / (1 * (2 * ((k : ℝ) + 1) * (2 * ((k : ℝ) + 1) + 1))) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact mul_le_mul_of_nonneg_right h1 h2.le
    _ = 1 / (2 * ((k : ℝ) + 1) * (2 * ((k : ℝ) + 1) + 1)) := by rw [one_mul]

lemma cpow_neg_two_mul_nat (b : ℝ) (n : ℕ) :
    (b : ℂ) ^ (-2 * (n : ℂ)) = (((b ^ 2) ^ n : ℝ) : ℂ)⁻¹ := by
  rw [show -2 * (n : ℂ) = -((2 * n : ℕ) : ℂ) by push_cast; ring, Complex.cpow_neg,
    Complex.cpow_natCast]
  push_cast
  rw [← pow_mul]

/-- The value of `∫ u_{m+1} P_b` as a real number times `2π √b`. -/
lemma integral_uTerm_succ_mul {b : ℝ} (hb : 1 < b) (m : ℕ) :
    ∫ t : ℝ, uTerm (m + 1) (2 + t * I) * tentDephased b (2 + t * I) =
      2 * Real.pi * Real.sqrt b *
        (((b - 1) * (1 / (2 * ((m : ℝ) + 1 + 1)) - 1 / (2 * ((m : ℝ) + 1))) +
          b * (1 / (2 * ((m : ℝ) + 1) * (2 * ((m : ℝ) + 1) + 1))) -
          (1 : ℝ) / ((b ^ 2) ^ (m + 1) * (2 * ((m : ℝ) + 1)) * (2 * ((m : ℝ) + 1) + 1)) : ℝ) : ℂ) := by
  have hb0 : 0 < b := by linarith
  rw [(integral_uTerm_mul hb (m := m + 1) (by omega)).2]
  congr 1
  have hne : (-2 * ((m + 1 : ℕ) : ℂ)) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [Nat.cast_nonneg (α := ℝ) m]
  rw [dslope_cpow_of_ne b hne, cpow_neg_two_mul_nat b]
  push_cast
  generalize hX : ((b : ℂ) ^ 2) ^ (m + 1) = X
  have hX0 : X ≠ 0 := by rw [← hX]; exact pow_ne_zero _ (pow_ne_zero _ (ofReal_ne_zero_of_pos hb0))
  have hm1 : ((m : ℂ) + 1) ≠ 0 := TentDigamma.natCast_add_one_ne_zero m
  have hm2 : (2 * ((m : ℂ) + 1) + 1) ≠ 0 := by
    rw [show (2 : ℂ) * ((m : ℂ) + 1) + 1 = ((2 * ((m : ℝ) + 1) + 1 : ℝ) : ℂ) by push_cast; ring]
    exact ofReal_ne_zero_of_pos (by positivity)
  have hm3 : ((m : ℂ) + 1 + 1) ≠ 0 := by
    rw [show (m : ℂ) + 1 + 1 = (((m : ℝ) + 1 + 1 : ℝ) : ℂ) by push_cast; ring]
    exact ofReal_ne_zero_of_pos (by positivity)
  have hden : (-2 * ((m : ℂ) + 1) - 1) ≠ 0 := by
    have hpos : (0 : ℝ) < 2 * ((m : ℝ) + 1) + 1 := by positivity
    rw [show -2 * ((m : ℂ) + 1) - 1 = ((-(2 * ((m : ℝ) + 1) + 1) : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  rw [show (X⁻¹ - (b : ℂ)) / (-2 * ((m : ℂ) + 1) - 1) = ((b : ℂ) - X⁻¹) / (2 * ((m : ℂ) + 1) + 1) by
    rw [div_eq_div_iff hden hm2]; ring]
  field_simp
  ring

/-- `∑_{m ≥ 0} ∫ u_{m+1} P_b = 2π √b (-(b - 1)/2 + b (1 - log 2) - T(b))`. -/
lemma hasSum_integral_uTerm {b : ℝ} (hb : 1 < b) :
    HasSum (fun m : ℕ => ∫ t : ℝ, uTerm (m + 1) (2 + t * I) * tentDephased b (2 + t * I))
      (2 * Real.pi * Real.sqrt b * (((b - 1) * (-1 / 2) + b * (1 - Real.log 2) - trivialSum b : ℝ) : ℂ)) := by
  have h := ((hasSum_alpha.mul_left (b - 1)).add (hasSum_beta.mul_left b)).sub
    (summable_trivial hb.le).hasSum
  have hc := (Complex.hasSum_ofReal.mpr h).mul_left (2 * Real.pi * Real.sqrt b : ℂ)
  refine hc.congr_fun fun m => ?_
  rw [integral_uTerm_succ_mul hb m]

end ClosedForms

section MassIdentity

open Complex Set Filter Topology MeasureTheory
open scoped ArithmeticFunction.vonMangoldt
open TentWidthTwoMargin ZetaExplicit ZetaShared

local notation "γ" => Real.eulerMascheroniConstant

/-! ## 12. The mass identity -/

/-- `(Ξ'/Ξ - ζ'/ζ - 1/(s-1) - κ) P_b` on the line `s = 2 + it`. -/
def lineRest (b : ℝ) (t : ℝ) : ℂ :=
  (deriv Xi (2 + t * I) / Xi (2 + t * I) - deriv riemannZeta (2 + t * I) / riemannZeta (2 + t * I) -
    (2 + t * I - 1)⁻¹ - kappa) * tentDephased b (2 + t * I)

theorem integral_lineRest {b : ℝ} (hb : 1 < b) :
    Integrable (lineRest b) ∧
    ∫ t : ℝ, lineRest b t =
      2 * Real.pi * Real.sqrt b * (((b - 1) * (-1 / 2) + b * (1 - Real.log 2) - trivialSum b : ℝ) : ℂ) := by
  have hb0 : 0 < b := by linarith
  set G : ℕ → ℝ → ℂ := fun m t => uTerm (m + 1) (2 + t * I) * tentDephased b (2 + t * I) with hGdef
  have hG : ∀ t : ℝ, HasSum (fun m => G m t) (lineRest b t) := fun t =>
    (hasSum_logDeriv_Xi (s := 2 + t * I) (by simp)).mul_right _
  have hGint : ∀ m, Integrable (G m) := fun m => (integral_uTerm_mul hb (m := m + 1) (by omega)).1
  set a : ℕ → ℝ := fun m => 1 / ((((m + 1 : ℕ) : ℝ) + 1) * Real.sqrt (((m + 1 : ℕ) : ℝ) + 1))
    with ha
  have ha0 : ∀ m, 0 ≤ a m := fun m => by positivity
  have hasum : Summable a := (summable_nat_add_iff 1).mpr TentDigamma.summable_inv_mul_sqrt
  set Kb : ℝ := Real.sqrt b * (b + 1 + b ^ (2 : ℝ) + 1) with hKb
  have hKb0 : 0 ≤ Kb := by have : 0 ≤ b ^ (2 : ℝ) := Real.rpow_nonneg hb0.le _; positivity
  set Q : ℝ → ℝ := fun t => Real.sqrt |t| * ‖tentDephased b (2 + t * I)‖ with hQ
  have hQcont : Continuous Q :=
    (Real.continuous_sqrt.comp continuous_abs).mul (continuous_tentDephased_line hb0).norm
  have hQint : Integrable Q := by
    refine Integrable.mono' (TentMassIdentity.integrable_sqrt_abs_div.const_mul Kb)
      hQcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have h := norm_tentDephased_line_le hb t
    calc Real.sqrt |t| * ‖tentDephased b (2 + t * I)‖ ≤ Real.sqrt |t| * (Kb / (1 + t ^ 2)) :=
          mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
      _ = Kb * (Real.sqrt |t| / (1 + t ^ 2)) := by ring
  have hGb : ∀ m (t : ℝ), ‖G m t‖ ≤ a m * Q t := by
    intro m t
    rw [hGdef, norm_mul]
    have h := norm_uTerm_line_le (m + 1) t
    calc ‖uTerm (m + 1) (2 + t * I)‖ * ‖tentDephased b (2 + t * I)‖ ≤
        (Real.sqrt |t| * a m) * ‖tentDephased b (2 + t * I)‖ :=
          mul_le_mul_of_nonneg_right h (norm_nonneg _)
      _ = a m * Q t := by rw [hQ]; ring
  have hsumm : Summable fun m => ∫ t, ‖G m t‖ := by
    refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun t => norm_nonneg _)
      (fun m => ?_) (hasum.mul_right (∫ t, Q t))
    rw [← integral_const_mul]
    exact integral_mono (hGint m).norm (hQint.const_mul _) fun t => hGb m t
  have hcont : Continuous (lineRest b) := by
    refine continuous_line (f := fun s => (deriv Xi s / Xi s - deriv riemannZeta s / riemannZeta s -
      (s - 1)⁻¹ - kappa) * tentDephased b s) fun s hs => ?_
    exact ((((continuousAt_logDeriv_Xi hs).sub (continuousAt_logDeriv_zeta hs)).sub
      ((continuousAt_id.sub continuousAt_const).inv₀
        (sub_ne_zero.mpr (ne_one_of_two_le_re hs)))).sub continuousAt_const).mul
      (continuousAt_tentDephased hb0 hs)
  have hint : Integrable (lineRest b) := by
    refine Integrable.mono' (hQint.const_mul (∑' m, a m)) hcont.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    have hgs : HasSum (fun m => a m * Q t) ((∑' m, a m) * Q t) := hasum.hasSum.mul_right (Q t)
    exact (hG t).norm_le_of_bounded hgs fun m => hGb m t
  refine ⟨hint, ?_⟩
  have h1 := hasSum_integral_of_summable_integral_norm hGint hsumm
  have h2 : (fun t => ∑' m, G m t) = lineRest b := funext fun t => (hG t).tsum_eq
  rw [h2] at h1
  exact h1.unique (hasSum_integral_uTerm hb)

/-- The line integral of `Ξ'/Ξ · P_b` along `re s = 2`. -/
theorem integral_line {b : ℝ} (hb : 1 < b) :
    Integrable (fun t : ℝ => deriv Xi (2 + t * I) / Xi (2 + t * I) * tentDephased b (2 + t * I)) ∧
    ∫ t : ℝ, deriv Xi (2 + t * I) / Xi (2 + t * I) * tentDephased b (2 + t * I) =
      2 * Real.pi * Real.sqrt b * (-(primeRamp b : ℂ) + (b * Real.log b - b + 1) + kappa * (b - 1) +
        (((b - 1) * (-1 / 2) + b * (1 - Real.log 2) - trivialSum b : ℝ) : ℂ)) := by
  obtain ⟨i1, e1⟩ := integral_logDeriv_zeta_mul hb
  obtain ⟨i2, e2⟩ := integral_inv_sub_one_mul hb
  obtain ⟨i3, e3⟩ := integral_tentDephased hb
  obtain ⟨i4, e4⟩ := integral_lineRest hb
  have hfun : (fun t : ℝ => deriv Xi (2 + t * I) / Xi (2 + t * I) * tentDephased b (2 + t * I)) =
      fun t : ℝ => ((deriv riemannZeta (2 + t * I) / riemannZeta (2 + t * I) * tentDephased b (2 + t * I) +
        (2 + t * I - 1)⁻¹ * tentDephased b (2 + t * I)) + kappa * tentDephased b (2 + t * I)) +
          lineRest b t := by
    funext t; unfold lineRest; ring
  rw [hfun]
  have hA : Integrable (fun t : ℝ =>
      deriv riemannZeta (2 + t * I) / riemannZeta (2 + t * I) * tentDephased b (2 + t * I) +
        (2 + t * I - 1)⁻¹ * tentDephased b (2 + t * I)) := i1.add i2
  have hB : Integrable (fun t : ℝ =>
      (deriv riemannZeta (2 + t * I) / riemannZeta (2 + t * I) * tentDephased b (2 + t * I) +
        (2 + t * I - 1)⁻¹ * tentDephased b (2 + t * I)) + kappa * tentDephased b (2 + t * I)) :=
    hA.add (i3.const_mul kappa)
  refine ⟨hB.add i4, ?_⟩
  rw [integral_add hB i4, integral_add hA (i3.const_mul kappa), integral_add i1 i2,
    integral_const_mul, e1, e2, e3, e4]
  ring

/-- `S(b) = ∑_ρ b^ρ/(ρ(1-ρ))` in closed form, through the explicit formula. -/
def rampSum (b : ℝ) : ℝ :=
  b * (1 + γ - Real.log b) - Real.log (2 * Real.pi) + trivialSum b + primeRamp b

/-- The cap `L_b^* = √b ((b + 1) C_0 - 2 S(b))`. -/
def massCap (b : ℝ) : ℝ := Real.sqrt b * ((b + 1) * cZero - 2 * rampSum b)

lemma massCap_eq {b : ℝ} :
    massCap b = 2 * Real.sqrt b * (-primeRamp b + (b * Real.log b - b + 1) +
      (1 - γ - Real.log Real.pi) / 2 * (b - 1) +
        ((b - 1) * (-1 / 2) + b * (1 - Real.log 2) - trivialSum b)) := by
  unfold massCap rampSum cZero
  rw [Real.log_mul (by norm_num) Real.pi_pos.ne', Real.log_mul (by norm_num) Real.pi_pos.ne']
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [h4]
  ring

/-- **The critical-line mass identity, over the zeros.** For `b > 1`,
`∑_ρ m_ρ P_b(ρ) = L_b^*`, the sum running over the nontrivial zeros of `ζ`. -/
theorem hasSum_zeros_tentDephased {b : ℝ} (hb : 1 < b) :
    HasSum (fun ρ : zeros => (mult (ρ : ℂ) : ℂ) * tentDephased b ρ) (massCap b) := by
  obtain ⟨hint, hval⟩ := integral_line hb
  have h := hasSum_zeros_eq_line hb hint
  rw [hval] at h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e : (massCap b : ℂ) = 2 * Real.pi * Real.sqrt b * (-(primeRamp b : ℂ) +
      (b * Real.log b - b + 1) + kappa * (b - 1) +
        (((b - 1) * (-1 / 2) + b * (1 - Real.log 2) - trivialSum b : ℝ) : ℂ)) / Real.pi := by
    rw [massCap_eq]
    unfold kappa
    push_cast
    field_simp
  rw [e]
  exact h

/-! ## 13. The zeros as a family with multiplicity -/

/-- Each nontrivial zero `ρ` of `ζ`, repeated `mult ρ` times. -/
def ZeroIndex : Type := Σ ρ : zeros, Fin (mult (ρ : ℂ))

/-- The zero indexed by `i`. -/
def zero (i : ZeroIndex) : ℂ := (i.1 : ℂ)

lemma zero_mem (i : ZeroIndex) : 0 < (zero i).re ∧ (zero i).re < 1 ∧ riemannZeta (zero i) = 0 :=
  i.1.2

lemma tsum_fin_const (n : ℕ) (c : ℝ) : ∑' _ : Fin n, c = n * c := by
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma hasSum_fin_const (n : ℕ) (c : ℝ) : HasSum (fun _ : Fin n => c) (n * c) := by
  have h := hasSum_fintype (fun _ : Fin n => c)
  rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h

lemma summable_norm_zero {b : ℝ} (hb : 1 < b) :
    Summable fun i : ZeroIndex => ‖tentDephased b (zero i)‖ := by
  refine (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr ⟨fun ρ => ?_, ?_⟩
  · exact (hasSum_fintype _).summable
  · refine (summable_mult_norm hb).congr fun ρ => ?_
    exact (tsum_fin_const _ _).symm

/-- **The critical-line mass identity.** For `b > 1`, over the nontrivial zeros of `ζ` counted
with multiplicity, `∑ Re P_b(ρ) = L_b^* = √b ((b + 1) C_0 - 2 S(b))`. -/
theorem hasSum_mass {b : ℝ} (hb : 1 < b) :
    HasSum (fun i : ZeroIndex => (TentZeroBudget.companion b (zero i)).re) (massCap b) := by
  have hc := Complex.hasSum_re (hasSum_zeros_tentDephased hb)
  rw [Complex.ofReal_re] at hc
  refine HasSum.sigma_of_hasSum hc (fun ρ => ?_) ?_
  · have e : ((mult (ρ : ℂ) : ℂ) * tentDephased b ρ).re = mult (ρ : ℂ) * (tentDephased b ρ).re := by
      simp
    rw [e]
    exact hasSum_fin_const _ _
  · refine Summable.of_norm_bounded (summable_norm_zero hb) fun i => ?_
    rw [Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _

theorem summable_mass {b : ℝ} (hb : 1 < b) :
    Summable fun i : ZeroIndex => (TentZeroBudget.companion b (zero i)).re :=
  (hasSum_mass hb).summable

theorem tsum_mass {b : ℝ} (hb : 1 < b) :
    ∑' i : ZeroIndex, (TentZeroBudget.companion b (zero i)).re = massCap b :=
  (hasSum_mass hb).tsum_eq

/-- **Critical-line zero mass for the zeros of `ζ`.** For every `b > 1`, under the strip and
height condition on the off-line zeros, `∑_{Re ρ = 1/2} |H_b(ρ)| ≤ L_b^*`, with equality if and
only if every nontrivial zero lies on the critical line. Summability and the mass identity are
proved, not assumed. -/
theorem line_mass_bound_and_equality_zeta {b : ℝ} (hb : 1 < b)
    (off : ∀ i, (zero i).re ≠ 1 / 2 →
      ∃ e : ℝ, 0 < e ∧ e ≤ (zero i).re ∧ e ≤ 1 - (zero i).re ∧ 1 ≤ e * (zero i).im ^ 2) :
    (∑' i, TentZeroBudget.lineMass b (zero i)) ≤ massCap b ∧
    ((∑' i, TentZeroBudget.lineMass b (zero i)) = massCap b ↔ ∀ i, (zero i).re = 1 / 2) := by
  have h := TentZeroBudget.line_mass_bound_and_equality hb zero off (summable_mass hb)
  rwa [tsum_mass hb] at h

lemma primeRamp_two : primeRamp 2 = 0 := by
  have hfl : ⌊(2 : ℝ)⌋₊ = 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Nat.floor_natCast]
  unfold primeRamp
  rw [hfl, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp [ArithmeticFunction.vonMangoldt_apply_one]

lemma rampSum_two : rampSum 2 = rampTwoExplicit := by
  unfold rampSum rampTwoExplicit trivialSum
  rw [primeRamp_two]
  norm_num

lemma massCap_two : massCap 2 = Real.sqrt 2 * (3 * cZero - 2 * rampTwoExplicit) := by
  unfold massCap
  rw [rampSum_two]
  norm_num

/-- **Width-two margin for the zeros of `ζ`.** Under the classical logarithmic strip above
height `6`, `B_2 - ∑_{Re ρ = 1/2} |H_2(ρ)| > 0.219979217443`, with no summability or mass
hypothesis. -/
theorem widthTwo_margin_zeta
    (hoff : ∀ i, (zero i).re ≠ 1 / 2 →
      ∃ e : ℝ, 0 < e ∧ e ≤ (zero i).re ∧ e ≤ 1 - (zero i).re ∧
        6 ≤ |(zero i).im| ∧ 1 ≤ 6 * Real.log |(zero i).im| * e) :
    (219979217443 : ℝ) / 10 ^ 12 <
      primeSquareBias2 - ∑' i, (if (zero i).re = 1 / 2 then ‖tentKernel 2 (zero i)‖ else 0) := by
  have hb : (1 : ℝ) < 2 := by norm_num
  exact widthTwo_postCriticalLine_margin_unconditional (summable_mass hb)
    ((tsum_mass hb).trans massCap_two) hoff

end MassIdentity

end TentMassIdentity

#print axioms TentMassIdentity.integral_line_eq_residues
#print axioms TentMassIdentity.rect_residues
#print axioms TentMassIdentity.hasSum_zeros_eq_line
#print axioms TentMassIdentity.integral_line
#print axioms TentMassIdentity.hasSum_zeros_tentDephased
#print axioms TentMassIdentity.hasSum_mass
#print axioms TentMassIdentity.line_mass_bound_and_equality_zeta
#print axioms TentMassIdentity.widthTwo_margin_zeta
