import Mathlib
import ZetaShared.Statements
import IndependentLandau.Analytic

/-! Bounds in the classical region for the transform of the centred ramp with its jump at the
origin removed.

`zetaPhi s` behaves like `(1 + γ) / s` on vertical lines, because `u ↦ rampG (exp u)` restricted
to `u > 0` has the jump `rampG 1 = 1 + γ` at `u = 0`. Subtracting `(1 + γ) / (s + 1)`, the
transform of `(1 + γ) exp (-u)`, leaves `psi`, which is `O (log² |t| / t²)` in the region. -/

open Complex Set Filter Topology

noncomputable section

namespace ZetaRamp

open IndependentLandau ZetaShared

local notation "γ" => (Real.eulerMascheroniConstant : ℂ)

/-- The transform of `rampH`: `zetaPhi` with the `1 / s` decay removed. -/
def psi (s : ℂ) : ℂ := zetaPhi s - (1 + γ) / (s + 1)

/-- The classical region to the right of `σ = 1 - c / log (|t| + 2)`. -/
def region (c : ℝ) : Set ℂ := {s : ℂ | 1 - c / Real.log (|s.im| + 2) ≤ s.re}

lemma half_lt_log_abs_add_two (t : ℝ) : 1 / 2 < Real.log (|t| + 2) := by
  have h1 : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have := Real.log_two_gt_d9
  linarith

/-- The hypothesis may be weakened to a smaller constant `c`. -/
lemma regionData_shrink {c C c' : ℝ} (h : RegionData c C) (hc' : 0 < c') (hle : c' ≤ c) :
    RegionData c' C := by
  have key : ∀ s : ℂ, 1 - c' / Real.log (|s.im| + 2) ≤ s.re →
      1 - c / Real.log (|s.im| + 2) ≤ s.re := by
    intro s hs
    have hL := half_lt_log_abs_add_two s.im
    have : c' / Real.log (|s.im| + 2) ≤ c / Real.log (|s.im| + 2) :=
      div_le_div_of_nonneg_right hle (by linarith)
    linarith
  exact ⟨hc', h.C_pos, fun s hs => h.nonvanishing s (key s hs),
    fun s hs => h.logDeriv s (key s hs)⟩

lemma half_le_re_of_mem_region {c : ℝ} (hc : c ≤ 1 / 4) {s : ℂ} (hs : s ∈ region c) :
    1 / 2 ≤ s.re := by
  have hL := half_lt_log_abs_add_two s.im
  have h1 : c / Real.log (|s.im| + 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h2 : 1 - c / Real.log (|s.im| + 2) ≤ s.re := hs
  linarith

lemma ne_zero_of_half_le_re {s : ℂ} (h : 1 / 2 ≤ s.re) : s ≠ 0 := by
  rintro rfl
  norm_num at h

lemma add_one_ne_zero_of_half_le_re {s : ℂ} (h : 1 / 2 ≤ s.re) : s + 1 ≠ 0 := by
  intro h0
  have := congrArg Complex.re h0
  simp at this
  linarith

lemma analyticAt_psi {c C : ℝ} (h : RegionData c C) (hc : c ≤ 1 / 4) {s : ℂ}
    (hs : s ∈ region c) : AnalyticAt ℂ psi s := by
  have hre := half_le_re_of_mem_region hc hs
  have hZ : riemannZeta₁ s ≠ 0 := by
    rcases eq_or_ne s 1 with rfl | h1
    · simp
    · exact fun h0 => h.nonvanishing s hs h1 (zeta₁_eq_zero_iff.mp h0)
  exact (analyticAt_zetaPhi hZ (ne_zero_of_half_le_re hre)).sub
    (analyticAt_const.div (analyticAt_id.add analyticAt_const)
      (add_one_ne_zero_of_half_le_re hre))

/-- The explicit formula for `psi`. -/
lemma psi_eq {s : ℂ} (hs1 : s ≠ 1) (hs0 : s ≠ 0) (hsm : s + 1 ≠ 0) (hζ : riemannZeta s ≠ 0) :
    psi s = -(deriv riemannZeta s / riemannZeta s) / (s * (s - 1)) - 1 / (s - 1) ^ 2
      + 2 * (1 + γ) / ((s - 1) * (s + 1)) := by
  have h : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have e : -deriv riemannZeta s / riemannZeta s = -(deriv riemannZeta s / riemannZeta s) :=
    neg_div _ _
  rw [psi, zetaPhi_eq hs1 hs0 hζ, e]
  generalize deriv riemannZeta s / riemannZeta s = q
  field_simp
  ring

lemma log_sq_le {x : ℝ} (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 16 * Real.sqrt x := by
  have hp : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hq : 0 < Real.sqrt (Real.sqrt x) := Real.sqrt_pos.mpr hp
  have h1 : Real.log x = 4 * Real.log (Real.sqrt (Real.sqrt x)) := by
    rw [Real.log_sqrt hp.le, Real.log_sqrt (by linarith)]; ring
  have h2 : Real.log (Real.sqrt (Real.sqrt x)) ≤ Real.sqrt (Real.sqrt x) - 1 :=
    Real.log_le_sub_one_of_pos hq
  have h3 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h4 : Real.sqrt (Real.sqrt x) ^ 2 = Real.sqrt x := Real.sq_sqrt hp.le
  have h5 : Real.log x ≤ 4 * Real.sqrt (Real.sqrt x) := by linarith
  calc Real.log x ^ 2 ≤ (4 * Real.sqrt (Real.sqrt x)) ^ 2 := pow_le_pow_left₀ h3 h5 2
    _ = 16 * Real.sqrt x := by rw [mul_pow, h4]; norm_num

lemma rpow_neg_three_half {x : ℝ} (hx : 0 < x) :
    x ^ (-(3 / 2) : ℝ) = (x * Real.sqrt x)⁻¹ := by
  rw [Real.rpow_neg hx.le, Real.sqrt_eq_rpow]
  congr 1
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx, Real.rpow_one]

lemma norm_one_add_gamma_le : ‖(1 : ℂ) + γ‖ ≤ 2 := by
  have h0 := Real.one_half_lt_eulerMascheroniConstant
  have h1 := Real.eulerMascheroniConstant_lt_two_thirds
  calc ‖(1 : ℂ) + γ‖ ≤ ‖(1 : ℂ)‖ + ‖γ‖ := norm_add_le _ _
    _ ≤ 2 := by
      rw [norm_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith

/-- The bound for `psi` in the region at height at least `1`. -/
lemma norm_psi_le_of_one_le {c C : ℝ} (h : RegionData c C) (hc : c ≤ 1 / 4) {s : ℂ}
    (hs : s ∈ region c) (hs2 : s.re ≤ 2) (ht : 1 ≤ |s.im|) :
    ‖psi s‖ ≤ 4 * (32 * C + 5) * (1 + |s.im|) ^ (-(3 / 2) : ℝ) := by
  have hre := half_le_re_of_mem_region hc hs
  have hC := h.C_pos
  have hs1 : s ≠ 1 := by
    rintro rfl
    norm_num at ht
  have hζ := h.nonvanishing s hs hs1
  have hLD := h.logDeriv s hs hs2 ht
  rw [psi_eq hs1 (ne_zero_of_half_le_re hre) (add_one_ne_zero_of_half_le_re hre) hζ]
  have n0 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have n1 : |s.im| ≤ ‖s - 1‖ := by simpa using Complex.abs_im_le_norm (s - 1)
  have n2 : |s.im| ≤ ‖s + 1‖ := by simpa using Complex.abs_im_le_norm (s + 1)
  generalize |s.im| = τ at *
  have hτ0 : 0 < τ := by linarith
  have hτ2 : 0 < τ ^ 2 := by positivity
  have t1 : ‖-(deriv riemannZeta s / riemannZeta s) / (s * (s - 1))‖
      ≤ C * Real.log (τ + 2) ^ 2 / τ ^ 2 := by
    rw [norm_div, norm_neg, norm_mul]
    refine div_le_div₀ (by positivity) hLD hτ2 ?_
    rw [pow_two]
    exact mul_le_mul n0 n1 hτ0.le (norm_nonneg _)
  have t2 : ‖1 / (s - 1) ^ 2‖ ≤ 1 / τ ^ 2 := by
    rw [norm_div, norm_one, norm_pow]
    exact one_div_le_one_div_of_le hτ2 (pow_le_pow_left₀ hτ0.le n1 2)
  have t3 : ‖2 * (1 + γ) / ((s - 1) * (s + 1))‖ ≤ 4 / τ ^ 2 := by
    rw [norm_div, norm_mul, norm_mul]
    refine div_le_div₀ (by norm_num) ?_ hτ2 ?_
    · have : ‖(2 : ℂ)‖ = 2 := by simp
      rw [this]
      linarith [norm_one_add_gamma_le]
    · rw [pow_two]
      exact mul_le_mul n1 n2 hτ0.le (norm_nonneg _)
  have hsum : ‖-(deriv riemannZeta s / riemannZeta s) / (s * (s - 1)) - 1 / (s - 1) ^ 2
      + 2 * (1 + γ) / ((s - 1) * (s + 1))‖ ≤ (C * Real.log (τ + 2) ^ 2 + 5) / τ ^ 2 := by
    calc _ ≤ ‖-(deriv riemannZeta s / riemannZeta s) / (s * (s - 1)) - 1 / (s - 1) ^ 2‖
          + ‖2 * (1 + γ) / ((s - 1) * (s + 1))‖ := norm_add_le _ _
      _ ≤ ‖-(deriv riemannZeta s / riemannZeta s) / (s * (s - 1))‖ + ‖1 / (s - 1) ^ 2‖
          + ‖2 * (1 + γ) / ((s - 1) * (s + 1))‖ := by
          gcongr
          exact norm_sub_le _ _
      _ ≤ C * Real.log (τ + 2) ^ 2 / τ ^ 2 + 1 / τ ^ 2 + 4 / τ ^ 2 := by gcongr
      _ = (C * Real.log (τ + 2) ^ 2 + 5) / τ ^ 2 := by ring
  refine hsum.trans ?_
  -- elementary comparison
  set w := Real.sqrt (1 + τ) with hwdef
  have hw2 : w ^ 2 = 1 + τ := Real.sq_sqrt (by linarith)
  have hw1 : 1 ≤ w := by
    nlinarith [Real.sqrt_nonneg (1 + τ)]
  have hp : Real.sqrt (τ + 2) ≤ 2 * w := by
    rw [Real.sqrt_le_iff]
    refine ⟨by linarith, ?_⟩
    rw [mul_pow, hw2]; linarith
  have hL : Real.log (τ + 2) ^ 2 ≤ 32 * w := by
    have := log_sq_le (x := τ + 2) (by linarith)
    linarith
  have hnum : C * Real.log (τ + 2) ^ 2 + 5 ≤ (32 * C + 5) * w := by
    have : C * Real.log (τ + 2) ^ 2 ≤ C * (32 * w) := mul_le_mul_of_nonneg_left hL hC.le
    nlinarith
  have hD : 0 < 32 * C + 5 := by linarith
  rw [rpow_neg_three_half (by linarith), ← hwdef]
  have e : ((1 + τ) * w)⁻¹ = w / (1 + τ) ^ 2 := by
    rw [← hw2]; field_simp
  rw [e]
  have key : (1 + τ) ^ 2 ≤ 4 * τ ^ 2 := by nlinarith
  have h1τ : 0 < (1 + τ) ^ 2 := by positivity
  calc (C * Real.log (τ + 2) ^ 2 + 5) / τ ^ 2 ≤ (32 * C + 5) * w / τ ^ 2 := by gcongr
    _ ≤ 4 * (32 * C + 5) * (w / (1 + τ) ^ 2) := by
        rw [div_le_iff₀ hτ2]
        have h3 : 1 ≤ 4 * τ ^ 2 / (1 + τ) ^ 2 := by
          rw [le_div_iff₀ h1τ]; linarith
        have h4 : 4 * (32 * C + 5) * (w / (1 + τ) ^ 2) * τ ^ 2
            = (32 * C + 5) * w * (4 * τ ^ 2 / (1 + τ) ^ 2) := by
          field_simp
        rw [h4]
        exact le_mul_of_one_le_right (by positivity) h3

/-- The part of the region at height at most `1` is compact. -/
lemma isCompact_smallBox (c : ℝ) :
    IsCompact {s : ℂ | s ∈ region c ∧ 1 / 2 ≤ s.re ∧ s.re ≤ 2 ∧ |s.im| ≤ 1} := by
  have hlog : Continuous fun s : ℂ => Real.log (|s.im| + 2) :=
    ((Complex.continuous_im.abs).add continuous_const).log
      (fun s => (by positivity : (0 : ℝ) < |s.im| + 2).ne')
  have hcurve : Continuous fun s : ℂ => 1 - c / Real.log (|s.im| + 2) :=
    continuous_const.sub (continuous_const.div hlog
      (fun s => (by linarith [half_lt_log_abs_add_two s.im] :
        (0 : ℝ) < Real.log (|s.im| + 2)).ne'))
  have hclosed : IsClosed {s : ℂ | s ∈ region c ∧ 1 / 2 ≤ s.re ∧ s.re ≤ 2 ∧ |s.im| ≤ 1} := by
    refine (isClosed_le hcurve Complex.continuous_re).inter
      ((isClosed_le continuous_const Complex.continuous_re).inter
        ((isClosed_le Complex.continuous_re continuous_const).inter
          (isClosed_le Complex.continuous_im.abs continuous_const)))
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) 3) hclosed ?_
  rintro s ⟨-, h1, h2, h3⟩
  rw [mem_closedBall_zero_iff]
  have := Complex.norm_le_abs_re_add_abs_im s
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s.re)] at this
  linarith

/-- A uniform bound for `psi` in the part of the region with `re s ≤ 2`. -/
theorem exists_psi_bound {c C : ℝ} (h : RegionData c C) (hc : c ≤ 1 / 4) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ region c, s.re ≤ 2 →
      ‖psi s‖ ≤ B * (1 + |s.im|) ^ (-(3 / 2) : ℝ) := by
  obtain ⟨M, hM⟩ := (isCompact_smallBox c).exists_bound_of_continuousOn (f := psi)
    (fun s hs => (analyticAt_psi h hc hs.1).continuousAt.continuousWithinAt)
  have hC := h.C_pos
  refine ⟨4 * |M| + 4 * (32 * C + 5), by positivity, fun s hs hs2 => ?_⟩
  have hpow : 0 ≤ (1 + |s.im|) ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg (by positivity) _
  rcases le_total |s.im| 1 with ht | ht
  · have h1 : ‖psi s‖ ≤ |M| :=
      (hM s ⟨hs, half_le_re_of_mem_region hc hs, hs2, ht⟩).trans (le_abs_self M)
    have h2 : (1 : ℝ) / 4 ≤ (1 + |s.im|) ^ (-(3 / 2) : ℝ) := by
      rw [rpow_neg_three_half (by positivity)]
      have hτ := abs_nonneg s.im
      set w := Real.sqrt (1 + |s.im|) with hwdef
      have hw2 : w ^ 2 = 1 + |s.im| := Real.sq_sqrt (by linarith)
      have hw0 : 0 ≤ w := Real.sqrt_nonneg _
      have hw : w ≤ 2 := by nlinarith
      have hpos : 0 < (1 + |s.im|) * w := by
        have : 0 < w := by
          rw [hwdef]; exact Real.sqrt_pos.mpr (by linarith)
        positivity
      rw [one_div, inv_le_inv₀ (by norm_num) hpos]
      nlinarith
    calc ‖psi s‖ ≤ |M| := h1
      _ ≤ 4 * |M| * (1 + |s.im|) ^ (-(3 / 2) : ℝ) := by nlinarith [abs_nonneg M]
      _ ≤ (4 * |M| + 4 * (32 * C + 5)) * (1 + |s.im|) ^ (-(3 / 2) : ℝ) := by
          gcongr; linarith
  · refine (norm_psi_le_of_one_le h hc hs hs2 ht).trans ?_
    gcongr
    linarith [abs_nonneg M]

end ZetaRamp
