import PrimeBand
import DivisorBand
import CenteredRampDensity
import Compat.Explicit
import Compat.PsiBound
import ZetaShared.Statements
import TentMassIdentity
import TentWidthTwoMargin
import ZetaWindowMass
import Crossley.WindowCriterion

/-!
# The converse of Crossley's window criterion

Under RH, the tent-weighted sum over ordinary primes stays strictly below its main term at every
sufficiently large scale, `primeSum y < 2 y log 2`. So the hypothesis of
`Crossley.window_criterion` holds, and the criterion is equivalent to RH.

* The prime powers. `D (4y) = 2y log 2 - primePowerSum y` is an integral of `ψ(u) - u` over
  `[y, 4y]`. The truncated explicit formula, truncated at height `y`, turns it into
  `Re ∑ m_ρ H₂(ρ) y^ρ` up to `O(log² y)`. Under RH each term has size `√y ‖H₂(ρ)‖`, and the
  critical-line zero mass `TentMassIdentity.widthTwo_margin_zeta` bounds their total by
  `(B₂ - 0.219979…) √y`.
* The prime squares. Their contribution `primePowerSum y - primeSum y` is at least `(3/10) √y`
  for large `y`, from a six-band minorant of the tent and the prime number theorem
  `Compat.psi_sub_id_eventually`. Since `3/10 > B₂ - 0.219979…`, the deficit is positive.

Mathlib only, through the release modules imported above.
-/

open Complex Set Filter MeasureTheory
open scoped Interval ArithmeticFunction.vonMangoldt

noncomputable section

namespace Crossley.WindowConverse

open RiemannReduction

/-- The certified width-two margin of `TentMassIdentity.widthTwo_margin_zeta`. -/
def margin : ℝ := 219979217443 / 10 ^ 12

/-! ## 1. The zero mass under RH -/

lemma strip_re_half (rh : RiemannHypothesis) {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hz : riemannZeta ρ = 0) : ρ.re = 1 / 2 :=
  ZetaWindow.re_of_rh rh ⟨h0, h1, hz⟩

/-- On the critical line the tent kernel and its dephased companion have the same norm. -/
lemma norm_kernel_eq_dephased {s : ℂ} (hs : s.re = 1 / 2) :
    ‖TentWidthTwoMargin.tentKernel 2 s‖ = ‖TentWidthTwoMargin.tentDephased 2 s‖ := by
  rw [← TentWidthTwoMargin.tentDephased_eq_mul_tentKernel (by norm_num : (1 : ℝ) < 2) s,
    norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h : ((1 / 2 : ℂ) - s).re = 0 := by
    rw [Complex.sub_re, hs]
    norm_num
  rw [h, Real.rpow_zero, one_mul]

/-- Under RH, the critical-line zero mass of any finite set of nontrivial zeros, counted with
multiplicity, is at most `B₂ - margin`. -/
theorem finite_mass_le (rh : RiemannHypothesis) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0) :
    ∑ ρ ∈ S, (ZetaShared.mult ρ : ℝ) * ‖TentWidthTwoMargin.tentKernel 2 ρ‖ ≤
      TentWidthTwoMargin.primeSquareBias2 - margin := by
  classical
  let F : TentMassIdentity.ZeroIndex → ℝ := fun i =>
    if (TentMassIdentity.zero i).re = 1 / 2 then
      ‖TentWidthTwoMargin.tentKernel 2 (TentMassIdentity.zero i)‖ else 0
  have hF0 : ∀ i, 0 ≤ F i := fun i => by
    dsimp only [F]
    split_ifs <;> positivity
  have hFsum : Summable F := by
    refine Summable.of_nonneg_of_le hF0 (fun i => ?_)
      (TentMassIdentity.summable_norm_zero (by norm_num : (1 : ℝ) < 2))
    dsimp only [F]
    split_ifs with h
    · exact (norm_kernel_eq_dephased h).le
    · exact norm_nonneg _
  have hmargin := TentMassIdentity.widthTwo_margin_zeta (fun i hi =>
    absurd (strip_re_half rh (TentMassIdentity.zero_mem i).1 (TentMassIdentity.zero_mem i).2.1
      (TentMassIdentity.zero_mem i).2.2) hi)
  let S' : Finset TentMassIdentity.zeros := S.subtype (fun ρ => ρ ∈ TentMassIdentity.zeros)
  let T : Finset TentMassIdentity.ZeroIndex := S'.sigma (fun _ => Finset.univ)
  have hT : ∑ i ∈ T, F i =
      ∑ ρ ∈ S, (ZetaShared.mult ρ : ℝ) * ‖TentWidthTwoMargin.tentKernel 2 ρ‖ := by
    rw [show T = S'.sigma (fun _ => Finset.univ) from rfl]
    erw [Finset.sum_sigma]
    have inner : ∀ ρ ∈ S', ∑ k ∈ (Finset.univ : Finset (Fin (ZetaShared.mult (ρ : ℂ)))),
        F ⟨ρ, k⟩ = (ZetaShared.mult (ρ : ℂ) : ℝ) * ‖TentWidthTwoMargin.tentKernel 2 ρ‖ := by
      intro ρ _
      have hre : (ρ : ℂ).re = 1 / 2 := strip_re_half rh ρ.2.1 ρ.2.2.1 ρ.2.2.2
      simp only [F, TentMassIdentity.zero, hre, if_true, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_congr rfl inner]
    exact Finset.sum_subtype_of_mem
      (fun ρ : ℂ => (ZetaShared.mult ρ : ℝ) * ‖TentWidthTwoMargin.tentKernel 2 ρ‖)
      (fun ρ hρ => hS ρ hρ)
  have hle : ∑ i ∈ T, F i ≤ ∑' i, F i := hFsum.sum_le_tsum T (fun i _ => hF0 i)
  have hmargin' : ∑' i, F i < TentWidthTwoMargin.primeSquareBias2 - margin := by
    unfold margin
    linarith [hmargin]
  rw [← hT]
  linarith

/-! ## 2. The explicit formula integrated against the tent -/

lemma integral_term {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ u in a..b, ((u : ℂ) ^ ρ / ρ) / (u : ℂ) ^ 2 =
      ((b : ℂ) ^ (ρ - 1) - (a : ℂ) ^ (ρ - 1)) / (ρ * (ρ - 1)) := by
  have key : EqOn (fun u : ℝ => ((u : ℂ) ^ ρ / ρ) / (u : ℂ) ^ 2)
      (fun u : ℝ => ρ⁻¹ * (u : ℂ) ^ (ρ - 2)) [[a, b]] := by
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ha.trans_le hu.1).ne'
    simp only
    rw [Complex.cpow_sub _ _ hu0, Complex.cpow_two]
    field_simp
  have h0 : (0 : ℝ) ∉ [[a, b]] := by
    rw [Set.uIcc_of_le hab]
    exact fun h => lt_irrefl _ (ha.trans_le h.1)
  have hr : ρ - 2 ≠ -1 := by
    intro h
    exact hρ1 (by linear_combination h)
  rw [intervalIntegral.integral_congr key, intervalIntegral.integral_const_mul,
    integral_cpow (Or.inr ⟨hr, h0⟩)]
  have e : ρ - 2 + 1 = ρ - 1 := by ring
  rw [e]
  have h1 : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  field_simp

lemma term_continuousOn (ρ : ℂ) (c : ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun u : ℝ => c * ((u : ℂ) ^ ρ / ρ) / (u : ℂ) ^ 2) [[a, b]] := by
  intro u hu
  rw [Set.uIcc_of_le hab] at hu
  have hu0 : 0 < u := ha.trans_le hu.1
  have hslit : (u : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr hu0
  have hne : (u : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hu0.ne')
  have h1 : ContinuousAt (fun x : ℝ => (x : ℂ) ^ ρ) u :=
    (Complex.continuous_ofReal.continuousAt).cpow continuousAt_const hslit
  have h2 : ContinuousAt (fun x : ℝ => (x : ℂ) ^ 2) u :=
    (Complex.continuous_ofReal.continuousAt).pow 2
  exact ((continuousAt_const.mul (h1.div_const ρ)).div h2 hne).continuousWithinAt

lemma integral_zeroSum (S : Finset ℂ) (hS : ∀ ρ ∈ S, ρ ≠ 0 ∧ ρ ≠ 1) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    ∫ u in a..b, (∑ ρ ∈ S, (ZetaShared.mult ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)) / (u : ℂ) ^ 2 =
      ∑ ρ ∈ S, (ZetaShared.mult ρ : ℂ) *
        (((b : ℂ) ^ (ρ - 1) - (a : ℂ) ^ (ρ - 1)) / (ρ * (ρ - 1))) := by
  simp only [Finset.sum_div]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro ρ hρ
    have e : (fun u : ℝ => (ZetaShared.mult ρ : ℂ) * ((u : ℂ) ^ ρ / ρ) / (u : ℂ) ^ 2) =
        fun u : ℝ => (ZetaShared.mult ρ : ℂ) * (((u : ℂ) ^ ρ / ρ) / (u : ℂ) ^ 2) := by
      funext u
      ring
    rw [e, intervalIntegral.integral_const_mul, integral_term (hS ρ hρ).1 (hS ρ hρ).2 ha hab]
  · intro ρ _
    exact (term_continuousOn ρ _ ha hab).intervalIntegrable

/-- The two zero integrals combine into the width-two tent kernel. -/
lemma kernel_identity (ρ : ℂ) {y : ℝ} (hy : 0 < y) :
    -((2 * y : ℝ) : ℂ) * ((((2 * y : ℝ) : ℂ) ^ (ρ - 1) - ((y : ℝ) : ℂ) ^ (ρ - 1)) /
        (ρ * (ρ - 1))) +
      ((4 * y : ℝ) : ℂ) * ((((4 * y : ℝ) : ℂ) ^ (ρ - 1) - ((2 * y : ℝ) : ℂ) ^ (ρ - 1)) /
        (ρ * (ρ - 1))) =
      (y : ℂ) ^ ρ * TentWidthTwoMargin.tentKernel 2 ρ := by
  have step : ∀ x : ℝ, 0 < x → (x : ℂ) * (x : ℂ) ^ (ρ - 1) = (x : ℂ) ^ ρ := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    rw [Complex.cpow_sub _ _ hx0, Complex.cpow_one]
    field_simp
  have h2 : ((2 * y : ℝ) : ℂ) ^ ρ = ((2 : ℝ) : ℂ) ^ ρ * (y : ℂ) ^ ρ := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by norm_num) hy.le]
  have h4 : ((4 * y : ℝ) : ℂ) ^ ρ = ((2 : ℝ) : ℂ) ^ ρ * ((2 : ℝ) : ℂ) ^ ρ * (y : ℂ) ^ ρ := by
    rw [show (4 * y : ℝ) = 2 * (2 * y) by ring, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity), h2]
    ring
  have a1 : ((2 * y : ℝ) : ℂ) * ((2 * y : ℝ) : ℂ) ^ (ρ - 1) = ((2 * y : ℝ) : ℂ) ^ ρ :=
    step _ (by positivity)
  have a2 : ((2 * y : ℝ) : ℂ) * ((y : ℝ) : ℂ) ^ (ρ - 1) = 2 * (y : ℂ) ^ ρ := by
    rw [Complex.ofReal_mul, mul_assoc, step y hy]
    push_cast
    ring
  have a3 : ((4 * y : ℝ) : ℂ) * ((4 * y : ℝ) : ℂ) ^ (ρ - 1) = ((4 * y : ℝ) : ℂ) ^ ρ :=
    step _ (by positivity)
  have a4 : ((4 * y : ℝ) : ℂ) * ((2 * y : ℝ) : ℂ) ^ (ρ - 1) = 2 * ((2 * y : ℝ) : ℂ) ^ ρ := by
    rw [show (4 * y : ℝ) = 2 * (2 * y) by ring, Complex.ofReal_mul, mul_assoc,
      step (2 * y) (by positivity)]
    push_cast
    ring
  have lhs : -((2 * y : ℝ) : ℂ) * ((((2 * y : ℝ) : ℂ) ^ (ρ - 1) - ((y : ℝ) : ℂ) ^ (ρ - 1)) /
        (ρ * (ρ - 1))) +
      ((4 * y : ℝ) : ℂ) * ((((4 * y : ℝ) : ℂ) ^ (ρ - 1) - ((2 * y : ℝ) : ℂ) ^ (ρ - 1)) /
        (ρ * (ρ - 1))) =
      (((4 * y : ℝ) : ℂ) ^ ρ - 3 * ((2 * y : ℝ) : ℂ) ^ ρ + 2 * (y : ℂ) ^ ρ) /
        (ρ * (ρ - 1)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (-(ρ * (ρ - 1))⁻¹) * a1 + (ρ * (ρ - 1))⁻¹ * a2 +
      (ρ * (ρ - 1))⁻¹ * a3 - (ρ * (ρ - 1))⁻¹ * a4
  rw [lhs, h4, h2]
  unfold TentWidthTwoMargin.tentKernel
  push_cast
  ring

/-! ## 3. The prime-power deficit -/

/-- The prime-power deficit equals the critical zero sum up to `O(log² y)`. Unconditional. -/
theorem deficit_near_zero_sum : ∃ C : ℝ, 0 < C ∧ ∃ L : ℝ, ∀ y : ℝ, 2 ≤ y →
    ∃ S : Finset ℂ, (∀ ρ ∈ S, 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0) ∧
      |DivisorBand.D (4 * y) -
          (∑ ρ ∈ S, (ZetaShared.mult ρ : ℂ) *
            ((y : ℂ) ^ ρ * TentWidthTwoMargin.tentKernel 2 ρ)).re|
        ≤ 4 * (C * (4 * Real.log (4 * y ^ 2) ^ 2 + Real.log (4 * y) + L)) := by
  classical
  obtain ⟨C, hC, trunc⟩ := Compat.truncated_explicit_formula_zeta
  let L : ℝ := ∑ᶠ ρ ∈ ZetaShared.zerosBelow 1, (ZetaShared.mult ρ : ℝ) / ‖ρ‖
  refine ⟨C, hC, L, fun y hy => ?_⟩
  have yp : 0 < y := by linarith
  have fin : (ZetaShared.zerosBelow y).Finite := (trunc y y hy le_rfl).1
  let S := fin.toFinset
  have hS : ∀ ρ ∈ S, 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 := by
    intro ρ hρ
    have h := fin.mem_toFinset.mp hρ
    exact ⟨h.1, h.2.1, h.2.2.2⟩
  refine ⟨S, hS, ?_⟩
  have hS01 : ∀ ρ ∈ S, ρ ≠ 0 ∧ ρ ≠ 1 := by
    intro ρ hρ
    obtain ⟨h0, h1, _⟩ := hS ρ hρ
    constructor
    · intro h
      rw [h, Complex.zero_re] at h0
      exact lt_irrefl _ h0
    · intro h
      rw [h, Complex.one_re] at h1
      exact lt_irrefl _ h1
  let Z : ℝ → ℂ := fun u => ∑ ρ ∈ S, (ZetaShared.mult ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)
  set ε : ℝ := C * (4 * Real.log (4 * y ^ 2) ^ 2 + Real.log (4 * y) + L) with hε
  -- pointwise explicit formula on [y, 4y]
  have pointwise : ∀ u : ℝ, y ≤ u → u ≤ 4 * y →
      |(Chebyshev.psi u - u) + (Z u).re| ≤ ε := by
    intro u lo hi
    have est := (trunc u y hy lo).2
    rw [finsum_mem_eq_finite_toFinset_sum _ fin] at est
    have hre : (Chebyshev.psi u - u) + (Z u).re =
        (((Chebyshev.psi u - u : ℝ) : ℂ) + Z u).re := by
      simp [Z]
    rw [hre]
    refine (Complex.abs_re_le_norm _).trans (est.trans ?_)
    apply mul_le_mul_of_nonneg_left _ hC.le
    have up : 0 < u := yp.trans_le lo
    have h4 : 4 ≤ u * y := by nlinarith
    have hlog0 : 0 ≤ Real.log (u * y) := Real.log_nonneg (by linarith)
    have hlog1 : Real.log (u * y) ≤ Real.log (4 * y ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith)
    have hsq : Real.log (u * y) ^ 2 ≤ Real.log (4 * y ^ 2) ^ 2 :=
      pow_le_pow_left₀ hlog0 hlog1 2
    have hfrac : u * Real.log (u * y) ^ 2 / y ≤ 4 * Real.log (4 * y ^ 2) ^ 2 := by
      rw [div_le_iff₀ yp]
      have : u * Real.log (u * y) ^ 2 ≤ 4 * y * Real.log (4 * y ^ 2) ^ 2 :=
        mul_le_mul hi hsq (sq_nonneg _) (by positivity)
      linarith
    have hlu : Real.log u ≤ Real.log (4 * y) := Real.log_le_log up hi
    linarith
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (pointwise y le_rfl (by linarith))
  -- integrated remainders
  have rem : ∀ a b : ℝ, y ≤ a → a ≤ b → b ≤ 4 * y →
      |(∫ u in a..b, DivisorBand.density u) + (∫ u in a..b, Z u / (u : ℂ) ^ 2).re| ≤
        ε / a ^ 2 * (b - a) := by
    intro a b ya ab b4
    have ap : 0 < a := yp.trans_le ya
    have bp : 0 < b := ap.trans_le ab
    have hcont : ContinuousOn (fun u : ℝ => Z u / (u : ℂ) ^ 2) [[a, b]] := by
      have e : (fun u : ℝ => Z u / (u : ℂ) ^ 2) = fun u : ℝ =>
          ∑ ρ ∈ S, (ZetaShared.mult ρ : ℂ) * ((u : ℂ) ^ ρ / ρ) / (u : ℂ) ^ 2 := by
        funext u
        simp only [Z, Finset.sum_div]
      rw [e]
      exact continuousOn_finsetSum _ fun ρ _ => term_continuousOn ρ _ ap ab
    have hZint : IntervalIntegrable (fun u : ℝ => Z u / (u : ℂ) ^ 2) volume a b :=
      hcont.intervalIntegrable
    have hre : (∫ u in a..b, Z u / (u : ℂ) ^ 2).re = ∫ u in a..b, (Z u).re / u ^ 2 := by
      rw [← Complex.reCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hZint]
      apply intervalIntegral.integral_congr
      intro u _
      simp only [Complex.reCLM_apply]
      rw [show ((u : ℂ) ^ 2) = ((u ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_re]
    have hreInt : IntervalIntegrable (fun u : ℝ => (Z u).re / u ^ 2) volume a b := by
      have : ContinuousOn (fun u : ℝ => (Z u).re / u ^ 2) [[a, b]] := by
        have e : (fun u : ℝ => (Z u).re / u ^ 2) =
            fun u : ℝ => Complex.re (Z u / (u : ℂ) ^ 2) := by
          funext u
          rw [show ((u : ℂ) ^ 2) = ((u ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_re]
        rw [e]
        exact Complex.continuous_re.comp_continuousOn hcont
      exact this.intervalIntegrable
    rw [hre, ← intervalIntegral.integral_add (DivisorBand.density_integrable ap bp) hreInt]
    have bound : ∀ u ∈ Ι a b, ‖DivisorBand.density u + (Z u).re / u ^ 2‖ ≤ ε / a ^ 2 := by
      intro u hu
      rw [Set.uIoc_of_le ab] at hu
      have up : 0 < u := ap.trans hu.1
      have hpt := pointwise u (ya.trans hu.1.le) (hu.2.trans b4)
      have e : DivisorBand.density u + (Z u).re / u ^ 2 =
          ((Chebyshev.psi u - u) + (Z u).re) / u ^ 2 := by
        unfold DivisorBand.density
        ring
      rw [e, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < u ^ 2)]
      have hau : a ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ ap.le hu.1.le 2
      calc |(Chebyshev.psi u - u) + (Z u).re| / u ^ 2 ≤ ε / u ^ 2 :=
            div_le_div_of_nonneg_right hpt (by positivity)
        _ ≤ ε / a ^ 2 := div_le_div_of_nonneg_left hε0 (by positivity) hau
    have h := intervalIntegral.norm_integral_le_of_norm_le_const bound
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ab)] at h
    exact h
  -- assemble the deficit
  have hD := DivisorBand.deficit_eq_centered_integrals (by linarith : (1 : ℝ) ≤ y)
  have hB1 := integral_zeroSum S hS01 yp (by linarith : y ≤ 2 * y)
  have hB2 := integral_zeroSum S hS01 (by linarith : (0 : ℝ) < 2 * y)
    (by linarith : 2 * y ≤ 4 * y)
  have hsum : (∑ ρ ∈ S, (ZetaShared.mult ρ : ℂ) *
      ((y : ℂ) ^ ρ * TentWidthTwoMargin.tentKernel 2 ρ)) =
      ((-(2 * y) : ℝ) : ℂ) * (∫ u in y..2 * y, Z u / (u : ℂ) ^ 2) +
        ((4 * y : ℝ) : ℂ) * (∫ u in 2 * y..4 * y, Z u / (u : ℂ) ^ 2) := by
    simp only [Z]
    rw [hB1, hB2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ρ _
    rw [← kernel_identity ρ yp]
    push_cast
    ring
  have r1 := rem y (2 * y) le_rfl (by linarith) (by linarith)
  have r2 := rem (2 * y) (4 * y) (by linarith) (by linarith) le_rfl
  rw [hsum, hD, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have e1 : ε / y ^ 2 * (2 * y - y) = ε / y := by
    field_simp
    ring
  have e2 : ε / (2 * y) ^ 2 * (4 * y - 2 * y) = ε / (2 * y) := by
    field_simp
    ring
  rw [e1] at r1
  rw [e2] at r2
  have k1 : |2 * y * ((∫ u in y..2 * y, DivisorBand.density u) +
      (∫ u in y..2 * y, Z u / (u : ℂ) ^ 2).re)| ≤ 2 * ε := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * y)]
    calc 2 * y * |_| ≤ 2 * y * (ε / y) := mul_le_mul_of_nonneg_left r1 (by positivity)
      _ = 2 * ε := by field_simp
  have k2 : |4 * y * ((∫ u in 2 * y..4 * y, DivisorBand.density u) +
      (∫ u in 2 * y..4 * y, Z u / (u : ℂ) ^ 2).re)| ≤ 2 * ε := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * y)]
    calc 4 * y * |_| ≤ 4 * y * (ε / (2 * y)) := mul_le_mul_of_nonneg_left r2 (by positivity)
      _ = 2 * ε := by field_simp; ring
  have eq : 2 * y * (∫ u in y..2 * y, DivisorBand.density u) -
      4 * y * (∫ u in 2 * y..4 * y, DivisorBand.density u) -
      (-(2 * y) * (∫ u in y..2 * y, Z u / (u : ℂ) ^ 2).re +
        4 * y * (∫ u in 2 * y..4 * y, Z u / (u : ℂ) ^ 2).re) =
      2 * y * ((∫ u in y..2 * y, DivisorBand.density u) +
        (∫ u in y..2 * y, Z u / (u : ℂ) ^ 2).re) -
      4 * y * ((∫ u in 2 * y..4 * y, DivisorBand.density u) +
        (∫ u in 2 * y..4 * y, Z u / (u : ℂ) ^ 2).re) := by ring
  rw [eq]
  calc _ ≤ |2 * y * ((∫ u in y..2 * y, DivisorBand.density u) +
        (∫ u in y..2 * y, Z u / (u : ℂ) ^ 2).re)| +
      |4 * y * ((∫ u in 2 * y..4 * y, DivisorBand.density u) +
        (∫ u in 2 * y..4 * y, Z u / (u : ℂ) ^ 2).re)| := abs_sub _ _
    _ ≤ 2 * ε + 2 * ε := add_le_add k1 k2
    _ = 4 * ε := by ring

/-- Under RH the prime-power deficit is at least `-(B₂ - margin) √y` up to `O(log² y)`. -/
theorem deficit_lower (rh : RiemannHypothesis) : ∃ C : ℝ, 0 < C ∧ ∃ L : ℝ, ∀ y : ℝ, 2 ≤ y →
    -(TentWidthTwoMargin.primeSquareBias2 - margin) * Real.sqrt y -
        4 * (C * (4 * Real.log (4 * y ^ 2) ^ 2 + Real.log (4 * y) + L)) ≤
      DivisorBand.D (4 * y) := by
  obtain ⟨C, hC, L, h⟩ := deficit_near_zero_sum
  refine ⟨C, hC, L, fun y hy => ?_⟩
  obtain ⟨S, hS, hbound⟩ := h y hy
  have yp : 0 < y := by linarith
  have hmass := finite_mass_le rh S hS
  have hnorm : ∀ ρ ∈ S, ‖(ZetaShared.mult ρ : ℂ) *
      ((y : ℂ) ^ ρ * TentWidthTwoMargin.tentKernel 2 ρ)‖ =
      Real.sqrt y * ((ZetaShared.mult ρ : ℝ) * ‖TentWidthTwoMargin.tentKernel 2 ρ‖) := by
    intro ρ hρ
    obtain ⟨h0, h1, hz⟩ := hS ρ hρ
    have hre := strip_re_half rh h0 h1 hz
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos yp, hre, Complex.norm_natCast,
      ← Real.sqrt_eq_rpow]
    ring
  have hsum : |(∑ ρ ∈ S, (ZetaShared.mult ρ : ℂ) *
      ((y : ℂ) ^ ρ * TentWidthTwoMargin.tentKernel 2 ρ)).re| ≤
      Real.sqrt y * (TentWidthTwoMargin.primeSquareBias2 - margin) := by
    refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
    rw [Finset.sum_congr rfl hnorm, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hmass (Real.sqrt_nonneg _)
  have := abs_le.mp hbound
  have := abs_le.mp hsum
  nlinarith

/-! ## 4. The prime squares -/

lemma tent_ge_of_mem {t lo hi : ℝ} (h1 : 1 / 4 ≤ lo) (hlo : lo ≤ t) (hhi : t ≤ hi)
    (h2 : hi < 1) : min (4 * lo - 1) (2 * (1 - hi)) ≤ ThetaTransfer.tent t := by
  rw [ThetaTransfer.tent_pieces]
  split_ifs with ha hb hc
  · exfalso
    linarith
  · exact (min_le_right _ _).trans (by linarith)
  · exact (min_le_left _ _).trans (by linarith)
  · exfalso
    linarith

/-- The tent at `y/p²` on a band `α √y < p ≤ β √y`. -/
lemma band_weight {y α β : ℝ} (hy : 0 < y) (hα : 1 < α) (hβ : β ≤ 2) {p : ℕ}
    (lo : α * Real.sqrt y < p) (hi : (p : ℝ) ≤ β * Real.sqrt y) :
    min (4 * (1 / β ^ 2) - 1) (2 * (1 - 1 / α ^ 2)) ≤ ThetaTransfer.tent (y / (p : ℝ) ^ 2) := by
  have sy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have ssq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
  have pp : 0 < (p : ℝ) := lt_trans (by positivity) lo
  have hβ0 : 0 < β := by
    have : α * Real.sqrt y < β * Real.sqrt y := lo.trans_le hi
    nlinarith
  have lo2 : α ^ 2 * y < (p : ℝ) ^ 2 := by
    have := mul_self_lt_mul_self (by positivity) lo
    nlinarith
  have hi2 : (p : ℝ) ^ 2 ≤ β ^ 2 * y := by
    have := mul_self_le_mul_self pp.le hi
    nlinarith
  apply tent_ge_of_mem
  · rw [le_div_iff₀ (by positivity)]
    nlinarith
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · rw [div_lt_one (by positivity)]
    nlinarith

lemma squares_le_gap {y : ℝ} (hy : 0 < y) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ (p : ℝ) ≤ 2 * Real.sqrt y) :
    ∑ p ∈ S, Real.log p * ThetaTransfer.tent (y / (p : ℝ) ^ 2) ≤
      ThetaTransfer.primePowerSum y - ThetaTransfer.primeSum y := by
  classical
  let T := Finset.range (⌊4 * y⌋₊ + 1)
  let f (n : ℕ) := Λ n * ThetaTransfer.tent (y / n)
  have incl : S.image (fun p : ℕ => p ^ 2) ⊆ T.filter (fun n => ¬n.Prime) := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨_, h⟩ := hS p hp
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range_succ_iff.mpr
      apply (Nat.le_floor_iff (by positivity)).mpr
      push_cast
      have h2 : (p : ℝ) ^ 2 ≤ (2 * Real.sqrt y) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) h 2
      rw [mul_pow, Real.sq_sqrt hy.le] at h2
      linarith
    · exact Nat.Prime.not_prime_pow le_rfl
  have square : (∑ p ∈ S, f (p ^ 2)) ≤ ∑ n ∈ T.filter (fun n => ¬n.Prime), f n := by
    rw [← Finset.sum_image (f := fun n => f n) (g := fun p : ℕ => p ^ 2)
      (by intro a _ b _ h; exact Nat.pow_left_injective (by decide : 2 ≠ 0) h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg incl fun n _ _ =>
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (ThetaTransfer.tent_nonneg _)
  have ordinary : ThetaTransfer.primeSum y = ∑ n ∈ T.filter Nat.Prime, f n := by
    rw [ThetaTransfer.primeSum]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [f, ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2]
  rw [ordinary, ThetaTransfer.primePowerSum]
  change _ ≤ (∑ n ∈ T, f n) - ∑ n ∈ T.filter Nat.Prime, f n
  rw [← Finset.sum_filter_add_sum_filter_not T Nat.Prime f, add_sub_cancel_left]
  refine le_trans (le_of_eq ?_) square
  apply Finset.sum_congr rfl
  intro p hp
  have pr := (hS p hp).1
  simp only [f, ArithmeticFunction.vonMangoldt_apply_pow (by decide : 2 ≠ 0),
    ArithmeticFunction.vonMangoldt_apply_prime pr]
  push_cast
  ring

/-- Six bands covering `(9/8, 15/8]` in units of `√y`. -/
def bandLo : Fin 6 → ℝ := ![9/8, 5/4, 11/8, 3/2, 13/8, 7/4]
/-- Upper ends of the bands. -/
def bandHi : Fin 6 → ℝ := ![5/4, 11/8, 3/2, 13/8, 7/4, 15/8]
/-- A lower bound for the tent on each band. -/
def bandH : Fin 6 → ℝ := ![34/81, 18/25, 7/9, 87/169, 15/49, 31/225]

lemma band_facts (j : Fin 6) : 1 < bandLo j ∧ bandLo j < bandHi j ∧ bandHi j ≤ 2 ∧
    0 ≤ bandH j ∧
    bandH j ≤ min (4 * (1 / bandHi j ^ 2) - 1) (2 * (1 - 1 / bandLo j ^ 2)) := by
  fin_cases j <;> simp [bandLo, bandHi, bandH] <;> norm_num

lemma band_disjoint {i j : Fin 6} (h : i ≠ j) : bandHi i ≤ bandLo j ∨ bandHi j ≤ bandLo i := by
  fin_cases i <;> fin_cases j <;> simp_all [bandLo, bandHi] <;> norm_num

lemma band_numeric : (31 / 100 : ℝ) ≤
    ∑ j, bandH j * ((999 / 1000) * bandHi j - (1001 / 1000) * bandLo j) := by
  simp [Fin.sum_univ_six, bandLo, bandHi, bandH]
  norm_num

lemma band_total : ∑ j, bandH j ≤ 3 := by
  simp [Fin.sum_univ_six, bandH]
  norm_num

/-- The prime squares give at least `(3/10) √y` once `y` is large. Unconditional. -/
theorem square_gap_lower : ∀ᶠ y : ℝ in atTop,
    (3 / 10) * Real.sqrt y ≤ ThetaTransfer.primePowerSum y - ThetaTransfer.primeSum y := by
  classical
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp
    (Compat.psi_sub_id_eventually (by norm_num : (0 : ℝ) < 1 / 1000))
  obtain ⟨C₀, hC₀⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let A : ℝ := 180000 * C₀ ^ 2 + 1
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_sqrt_atTop.eventually_ge_atTop (max X₀ A)] with y hy1 hyX
  have yp : 0 < y := by linarith
  set s := Real.sqrt y with hs
  have sp : 0 < s := Real.sqrt_pos.mpr yp
  have sX : X₀ ≤ s := (le_max_left _ _).trans hyX
  have sA : A ≤ s := (le_max_right _ _).trans hyX
  -- the band prime sets
  let B : Fin 6 → Finset ℕ := fun j =>
    Nat.primesLE ⌊bandHi j * s⌋₊ \ Nat.primesLE ⌊bandLo j * s⌋₊
  have memB : ∀ j, ∀ p ∈ B j, p.Prime ∧ bandLo j * s < p ∧ (p : ℝ) ≤ bandHi j * s := by
    intro j p hp
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨ph, pr⟩ := Nat.mem_primesLE.mp h1
    have hpos : 0 ≤ bandHi j * s := by
      have hb := band_facts j
      exact mul_nonneg (by linarith [hb.1, hb.2.1]) sp.le
    refine ⟨pr, ?_, (Nat.le_floor_iff hpos).mp ph⟩
    have hlo : 0 ≤ bandLo j * s := by
      have hb := band_facts j
      exact mul_nonneg (by linarith [hb.1]) sp.le
    exact lt_of_not_ge fun h => h2 (Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hlo).mpr h, pr⟩)
  have thetaB : ∀ j, Chebyshev.theta (bandHi j * s) - Chebyshev.theta (bandLo j * s) =
      ∑ p ∈ B j, Real.log p := by
    intro j
    rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
    have hle : bandLo j * s ≤ bandHi j * s := by
      have := band_facts j
      nlinarith
    exact (Finset.sum_sdiff_eq_sub (Nat.primesLE_mono (Nat.floor_le_floor hle))).symm
  have disj : (Set.PairwiseDisjoint ↑(Finset.univ : Finset (Fin 6)) B) := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro p hpi hpj
    obtain ⟨_, li, ui⟩ := memB i p hpi
    obtain ⟨_, lj, uj⟩ := memB j p hpj
    rcases band_disjoint hij with h | h
    · have : bandHi i * s ≤ bandLo j * s := mul_le_mul_of_nonneg_right h sp.le
      linarith
    · have : bandHi j * s ≤ bandLo i * s := mul_le_mul_of_nonneg_right h sp.le
      linarith
  have hSq : ∀ p ∈ (Finset.univ : Finset (Fin 6)).biUnion B,
      p.Prime ∧ (p : ℝ) ≤ 2 * Real.sqrt y := by
    intro p hp
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨pr, _, u⟩ := memB j p hj
    refine ⟨pr, u.trans ?_⟩
    have := (band_facts j).2.2.1
    rw [← hs]
    exact mul_le_mul_of_nonneg_right this sp.le
  have gap := squares_le_gap yp _ hSq
  rw [Finset.sum_biUnion disj] at gap
  -- each band contributes at least its weight times the theta difference
  have per : ∀ j, bandH j * (Chebyshev.theta (bandHi j * s) - Chebyshev.theta (bandLo j * s)) ≤
      ∑ p ∈ B j, Real.log p * ThetaTransfer.tent (y / (p : ℝ) ^ 2) := by
    intro j
    rw [thetaB j, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨_, l, u⟩ := memB j p hp
    obtain ⟨f1, _, f3, _, f5⟩ := band_facts j
    have w := band_weight yp f1 f3 l u
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (f5.trans w) (Real.log_natCast_nonneg p)
  -- the prime number theorem on each band
  have pnt : ∀ j, (999 / 1000) * (bandHi j * s) - (1001 / 1000) * (bandLo j * s) -
      |C₀| * Real.sqrt (2 * s) ≤
      Chebyshev.theta (bandHi j * s) - Chebyshev.theta (bandLo j * s) := by
    intro j
    obtain ⟨f1, f2, f3, _, _⟩ := band_facts j
    have hlo : X₀ ≤ bandLo j * s := by nlinarith
    have hhi : X₀ ≤ bandHi j * s := by nlinarith
    have plo := abs_le.mp (hX₀ _ hlo)
    have phi := abs_le.mp (hX₀ _ hhi)
    have tlo := Chebyshev.theta_le_psi (bandLo j * s)
    have thi := hC₀ (bandHi j * s)
    have hsq : C₀ * Real.sqrt (bandHi j * s) ≤ |C₀| * Real.sqrt (2 * s) := by
      have h1 : Real.sqrt (bandHi j * s) ≤ Real.sqrt (2 * s) :=
        Real.sqrt_le_sqrt (by nlinarith)
      calc C₀ * Real.sqrt (bandHi j * s) ≤ |C₀| * Real.sqrt (bandHi j * s) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)
        _ ≤ |C₀| * Real.sqrt (2 * s) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    nlinarith
  have total : ∑ j, bandH j * ((999 / 1000) * bandHi j - (1001 / 1000) * bandLo j) * s -
      (∑ j, bandH j) * (|C₀| * Real.sqrt (2 * s)) ≤
      ThetaTransfer.primePowerSum y - ThetaTransfer.primeSum y := by
    refine le_trans ?_ gap
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro j _
    refine le_trans ?_ (per j)
    have h0 := (band_facts j).2.2.2.1
    have := mul_le_mul_of_nonneg_left (pnt j) h0
    linarith
  -- the square-root error is below s/100 once s ≥ A
  have small : 3 * (|C₀| * Real.sqrt (2 * s)) ≤ s / 100 := by
    have key : (3 * |C₀|) ^ 2 * (2 * s) ≤ (s / 100) ^ 2 := by
      have hA : 180000 * C₀ ^ 2 ≤ s := by linarith
      have : (3 * |C₀|) ^ 2 * (2 * s) = 18 * C₀ ^ 2 * s := by rw [mul_pow, sq_abs]; ring
      rw [this]
      nlinarith
    have lhs : 3 * (|C₀| * Real.sqrt (2 * s)) = Real.sqrt ((3 * |C₀|) ^ 2 * (2 * s)) := by
      rw [Real.sqrt_mul (sq_nonneg (3 * |C₀|)) (2 * s), Real.sqrt_sq (by positivity)]
      ring
    rw [lhs]
    calc Real.sqrt ((3 * |C₀|) ^ 2 * (2 * s)) ≤ Real.sqrt ((s / 100) ^ 2) :=
          Real.sqrt_le_sqrt key
      _ = s / 100 := Real.sqrt_sq (by positivity)
  have hnum := band_numeric
  have htot := band_total
  have herr : (∑ j, bandH j) * (|C₀| * Real.sqrt (2 * s)) ≤ 3 * (|C₀| * Real.sqrt (2 * s)) :=
    mul_le_mul_of_nonneg_right htot (by positivity)
  have hmain : (31 / 100) * s ≤
      ∑ j, bandH j * ((999 / 1000) * bandHi j - (1001 / 1000) * bandLo j) * s := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hnum sp.le
  linarith

/-! ## 5. The converse -/

lemma sqrt_two_lt : Real.sqrt 2 < 1414214 / 1000000 := by
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

lemma margin_pos : (1 / 50 : ℝ) < 3 / 10 - (TentWidthTwoMargin.primeSquareBias2 - margin) := by
  unfold TentWidthTwoMargin.primeSquareBias2 margin
  have := sqrt_two_lt
  linarith

lemma log_sq_small (A B : ℝ) : ∀ᶠ y : ℝ in atTop,
    A * Real.log y ^ 2 + B ≤ (1 / 100) * Real.sqrt y := by
  have hlo := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (show (0 : ℝ) < 1 / (200 * (|A| + 1)) by positivity)
  filter_upwards [hlo, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_sqrt_atTop.eventually_ge_atTop (200 * |B|)] with y h1 hy hsq
  have hl : 0 ≤ Real.log y := Real.log_nonneg hy
  have e1 : ‖Real.log y ^ (2 : ℝ)‖ = Real.log y ^ 2 := by
    rw [Real.rpow_two, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have e2 : ‖y ^ (1 / 2 : ℝ)‖ = Real.sqrt y := by
    rw [← Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [e1, e2] at h1
  set c : ℝ := 1 / (200 * (|A| + 1)) with hc
  have hAc : |A| * c ≤ 1 / 200 := by
    rw [hc, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg A]
  have hA : A * Real.log y ^ 2 ≤ (1 / 200) * Real.sqrt y := by
    calc A * Real.log y ^ 2 ≤ |A| * Real.log y ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self A) (sq_nonneg _)
      _ ≤ |A| * (c * Real.sqrt y) := mul_le_mul_of_nonneg_left h1 (abs_nonneg A)
      _ = (|A| * c) * Real.sqrt y := by ring
      _ ≤ (1 / 200) * Real.sqrt y := mul_le_mul_of_nonneg_right hAc (Real.sqrt_nonneg _)
  have hB : B ≤ (1 / 200) * Real.sqrt y := by
    have := le_abs_self B
    linarith
  linarith

/-- **Converse of the window criterion.** Under RH, the ordinary-prime tent sum is strictly
below its main term at every sufficiently large scale. -/
theorem primeSum_lt_eventually (rh : RiemannHypothesis) :
    ∀ᶠ y : ℝ in atTop, ThetaTransfer.primeSum y < 2 * y * Real.log 2 := by
  obtain ⟨C, hC, L, hD⟩ := deficit_lower rh
  have hsq := square_gap_lower
  have hlog := log_sq_small (4 * C * 39) (4 * C * (|L| + 3))
  filter_upwards [hsq, hlog, eventually_ge_atTop (4 : ℝ)] with y hgap hl hy
  have yp : 0 < y := by linarith
  have hd := hD y (by linarith)
  have hDdef : DivisorBand.D (4 * y) = 2 * y * Real.log 2 - ThetaTransfer.primePowerSum y := by
    unfold DivisorBand.D DivisorBand.c
    rw [show 4 * y / 4 = y by ring]
    ring
  rw [hDdef] at hd
  -- the logarithmic remainder is below √y / 100
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have l4 : Real.log 4 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have e1 : Real.log (4 * y ^ 2) = Real.log 4 + 2 * Real.log y := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  have e2 : Real.log (4 * y) = Real.log 4 + Real.log y := Real.log_mul (by norm_num) yp.ne'
  have hL : L ≤ |L| := le_abs_self L
  have hsqb : Real.log (4 * y ^ 2) ^ 2 ≤ 9 * Real.log y ^ 2 := by
    rw [e1]
    nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]
  have hlin : Real.log (4 * y) ≤ 3 * Real.log y ^ 2 + 3 := by
    rw [e2]
    nlinarith
  have hrem : 4 * (C * (4 * Real.log (4 * y ^ 2) ^ 2 + Real.log (4 * y) + L)) ≤
      4 * C * 39 * Real.log y ^ 2 + 4 * C * (|L| + 3) := by
    have : 4 * Real.log (4 * y ^ 2) ^ 2 + Real.log (4 * y) + L ≤
        39 * Real.log y ^ 2 + (|L| + 3) := by linarith
    nlinarith
  have hm := margin_pos
  have hs := Real.sqrt_nonneg y
  have hspos : 0 < Real.sqrt y := Real.sqrt_pos.mpr yp
  nlinarith

/-- **The window criterion's converse.** Under RH, the hypothesis of
`Crossley.window_criterion` holds on every sufficiently late window, at every width. -/
theorem window_of_rh (rh : RiemannHypothesis) (δ : ℝ) :
    ∀ X₀ : ℝ, ∃ X ≥ X₀, ∀ x ∈ Icc X (X ^ (1 + δ)),
      ThetaTransfer.primeSum (x / 4) ≤ (x / 2) * Real.log 2 := by
  obtain ⟨Y, hY⟩ := eventually_atTop.mp (primeSum_lt_eventually rh)
  intro X₀
  refine ⟨max X₀ (4 * Y), le_max_left _ _, fun x hx => ?_⟩
  have hx : 4 * Y ≤ x := (le_max_right _ _).trans hx.1
  have := hY (x / 4) (by linarith)
  have e : 2 * (x / 4) * Real.log 2 = (x / 2) * Real.log 2 := by ring
  linarith

end Crossley.WindowConverse

namespace Crossley

/-- **Crossley's window criterion is equivalent to RH.** For every width `δ > 0`, the
tent-weighted ordinary-prime sum stays at or below its main term throughout arbitrarily late
windows `[X, X^(1+δ)]` if and only if the Riemann hypothesis holds. -/
theorem window_criterion_iff {δ : ℝ} (hδ : 0 < δ) :
    (∀ X₀ : ℝ, ∃ X ≥ X₀, ∀ x ∈ Icc X (X ^ (1 + δ)),
      ThetaTransfer.primeSum (x / 4) ≤ (x / 2) * Real.log 2) ↔ RiemannHypothesis :=
  ⟨window_criterion hδ, fun rh => WindowConverse.window_of_rh rh δ⟩

end Crossley

#print axioms Crossley.WindowConverse.finite_mass_le
#print axioms Crossley.WindowConverse.deficit_near_zero_sum
#print axioms Crossley.WindowConverse.square_gap_lower
#print axioms Crossley.WindowConverse.primeSum_lt_eventually
#print axioms Crossley.window_criterion_iff
