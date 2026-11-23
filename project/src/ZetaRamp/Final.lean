import Mathlib
import ZetaShared.Statements
import ZetaRamp.Contour

/-! The prime number theorem for the centred ramp with the classical error term, from a
zero-free region with a bound for the logarithmic derivative. -/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace ZetaRamp

open IndependentLandau ZetaShared

/-- The bound for `u ≥ 1`, with the height `T = exp (√u) - 1`. -/
lemma abs_rampG_exp_le_of_one_le {c C B : ℝ} (h : RegionData c C) (hc : c ≤ 1 / 4) (hB0 : 0 ≤ B)
    (hB : ∀ s ∈ region c, s.re ≤ 2 → ‖psi s‖ ≤ B * (1 + |s.im|) ^ (-(3 / 2) : ℝ))
    {u : ℝ} (hu : 1 ≤ u) :
    |rampG (Real.exp u)| ≤ (B * ((J (5 / 4) + 4) * Real.exp 1 + J (3 / 2)) + 2) * Real.exp u
      * Real.exp (-(c / 2) * Real.sqrt u) := by
  have hc0 := h.c_pos
  set r := Real.sqrt u with hr
  have hr1 : 1 ≤ r := by rw [hr]; exact Real.one_le_sqrt.mpr hu
  have hrr : r * r = u := Real.mul_self_sqrt (by linarith)
  have hE : 2 ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
  set T := Real.exp r - 1 with hTdef
  have hT : 0 ≤ T := by rw [hTdef]; linarith
  have hbound := rampH_bound h hc hB0 hB hu hT
  have e1 : (1 + T) ^ (-(1 / 4) : ℝ) = Real.exp (-(1 / 4) * r) := by
    rw [hTdef, add_sub_cancel, ← Real.exp_mul]; congr 1; ring
  have hLpos : 1 / 2 < Real.log (T + 2) := by
    have := half_lt_log_abs_add_two T
    rwa [abs_of_nonneg hT] at this
  have hlog : Real.log (T + 2) ≤ 2 * r := by
    rw [Real.log_le_iff_le_exp (by linarith)]
    have : Real.exp (2 * r) = Real.exp r * Real.exp r := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this, hTdef]; nlinarith
  have hη : c / 2 * r ≤ c / Real.log (T + 2) * u := by
    have h1 : c / (2 * r) ≤ c / Real.log (T + 2) :=
      div_le_div_of_nonneg_left hc0.le (by linarith) hlog
    have h2 : c / (2 * r) * u = c / 2 * r := by
      rw [← hrr]; field_simp
    calc c / 2 * r = c / (2 * r) * u := h2.symm
      _ ≤ c / Real.log (T + 2) * u := mul_le_mul_of_nonneg_right h1 (by linarith)
  set X := Real.exp (-(c / 2) * r) with hXdef
  have hX : 0 < X := Real.exp_pos _
  have e2 : Real.exp (-(c / Real.log (T + 2)) * u) ≤ X :=
    Real.exp_le_exp.mpr (by linarith)
  have e3 : Real.exp (-(1 / 4) * r) ≤ X := Real.exp_le_exp.mpr (by nlinarith)
  have e4 : Real.exp (-u) ≤ Real.exp u * X := by
    rw [hXdef, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hJ32 := J_nonneg (3 / 2)
  have hJ54 := J_nonneg (5 / 4)
  have hγ0 := Real.one_half_lt_eulerMascheroniConstant
  have hγ1 := Real.eulerMascheroniConstant_lt_two_thirds
  have hmain : |rampH u| ≤ B * Real.exp u * ((J (5 / 4) + 4) * Real.exp 1 * X + J (3 / 2) * X) := by
    refine hbound.trans ?_
    rw [e1]
    have h1 : (J (5 / 4) + 4) * Real.exp 1 * Real.exp (-(1 / 4) * r)
        ≤ (J (5 / 4) + 4) * Real.exp 1 * X := mul_le_mul_of_nonneg_left e3 (by positivity)
    have h2 : J (3 / 2) * Real.exp (-(c / Real.log (T + 2)) * u) ≤ J (3 / 2) * X :=
      mul_le_mul_of_nonneg_left e2 hJ32
    exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
  have hsec : |(1 + Real.eulerMascheroniConstant) * Real.exp (-u)| ≤ 2 * (Real.exp u * X) := by
    rw [abs_of_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le)]
    have := mul_le_mul_of_nonneg_right
      (by linarith : 1 + Real.eulerMascheroniConstant ≤ 2) (Real.exp_pos (-u)).le
    linarith
  have hG : rampG (Real.exp u)
      = rampH u + (1 + Real.eulerMascheroniConstant) * Real.exp (-u) := by
    unfold rampH; ring
  rw [hG]
  calc |rampH u + (1 + Real.eulerMascheroniConstant) * Real.exp (-u)|
      ≤ |rampH u| + |(1 + Real.eulerMascheroniConstant) * Real.exp (-u)| := abs_add_le _ _
    _ ≤ B * Real.exp u * ((J (5 / 4) + 4) * Real.exp 1 * X + J (3 / 2) * X)
        + 2 * (Real.exp u * X) := add_le_add hmain hsec
    _ = (B * ((J (5 / 4) + 4) * Real.exp 1 + J (3 / 2)) + 2) * Real.exp u * X := by ring

/-- **The prime number theorem for the centred ramp with the classical error term**, from a
zero-free region with a bound for the logarithmic derivative of zeta. -/
theorem rampPNT_of_region (h : ZetaShared.RegionStatement) : ZetaShared.RampPNTStatement := by
  obtain ⟨c₁, C, h₁⟩ := h
  have hc₁ := h₁.c_pos
  set c := min c₁ (1 / 4) with hcdef
  have hcpos : 0 < c := lt_min hc₁ (by norm_num)
  have hc : c ≤ 1 / 4 := min_le_right _ _
  have hR := regionData_shrink h₁ hcpos (min_le_left _ _)
  obtain ⟨B, hB0, hB⟩ := exists_psi_bound hR hc
  have hJ32 := J_nonneg (3 / 2)
  have hJ54 := J_nonneg (5 / 4)
  set A := B * ((J (5 / 4) + 4) * Real.exp 1 + J (3 / 2)) + 2 with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨c / 2, A + 5 * Real.exp 2, by positivity, fun y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  have hyu : Real.exp (Real.log y) = y := Real.exp_log hy0
  have hu0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  generalize Real.log y = u at hyu hu0 ⊢
  subst hyu
  have hX := Real.exp_pos (-(c / 2) * Real.sqrt u)
  have hEu := Real.exp_pos u
  have h0 : 0 ≤ A * Real.exp u * Real.exp (-(c / 2) * Real.sqrt u) := by positivity
  rcases le_or_gt 1 u with h1 | h1
  · refine (abs_rampG_exp_le_of_one_le hR hc hB0 hB h1).trans ?_
    have h2 : 0 ≤ 5 * Real.exp 2 * Real.exp u * Real.exp (-(c / 2) * Real.sqrt u) := by
      positivity
    linarith
  · have h5 := abs_rampG_exp_le hu0
    have hs0 := Real.sqrt_nonneg u
    have hs : Real.sqrt u ≤ 1 :=
      Real.sqrt_le_iff.mpr ⟨zero_le_one, by rw [one_pow]; exact h1.le⟩
    have hX1 : Real.exp (-1) ≤ Real.exp (-(c / 2) * Real.sqrt u) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h6 : Real.exp (2 * u)
        ≤ Real.exp 2 * Real.exp u * Real.exp (-(c / 2) * Real.sqrt u) := by
      calc Real.exp (2 * u) = Real.exp u * Real.exp u := by
            rw [← Real.exp_add]; congr 1; ring
        _ ≤ Real.exp u * Real.exp 1 :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h1.le) hEu.le
        _ = Real.exp 2 * Real.exp u * Real.exp (-1) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
        _ ≤ Real.exp 2 * Real.exp u * Real.exp (-(c / 2) * Real.sqrt u) :=
            mul_le_mul_of_nonneg_left hX1 (by positivity)
    calc |rampG (Real.exp u)| ≤ 5 * Real.exp (2 * u) := h5
      _ ≤ 5 * (Real.exp 2 * Real.exp u * Real.exp (-(c / 2) * Real.sqrt u)) := by linarith
      _ ≤ (A + 5 * Real.exp 2) * Real.exp u * Real.exp (-(c / 2) * Real.sqrt u) := by linarith

end ZetaRamp

#print axioms ZetaRamp.rampPNT_of_region
