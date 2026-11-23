import Mathlib
import ZetaShared.Perron
import ZetaExplicit.LogDeriv

/-! Estimates for the Perron integrand on the sides of the rectangle. -/

open Complex Set Filter Topology MeasureTheory

noncomputable section
namespace ZetaExplicit

open ZetaShared

lemma log_facts {u T : ℝ} (hT : 2 ≤ T) (hTu : T ≤ u) :
    1 ≤ Real.log (T + 2) ∧ Real.log (T + 2) ≤ Real.log (u * T) ∧
      Real.log u ≤ Real.log (u * T) ∧ Real.log 2 ≤ Real.log u ∧ (1 / 2 : ℝ) < Real.log 2 := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  refine ⟨?_, ?_, ?_, ?_, by linarith⟩
  · have : Real.log 4 ≤ Real.log (T + 2) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  · exact Real.log_le_log (by linarith) (by nlinarith)
  · exact Real.log_le_log (by linarith) (by nlinarith)
  · exact Real.log_le_log (by norm_num) (by linarith)

lemma abscissa_gt_one {u : ℝ} (hu : 2 ≤ u) : 1 < perronAbscissa u := by
  have h := (log_facts (le_refl 2) hu).2.2.2
  unfold perronAbscissa
  have : 0 < 1 / Real.log u := by apply one_div_pos.mpr; linarith
  linarith

lemma abscissa_le_three {u : ℝ} (hu : 2 ≤ u) : perronAbscissa u ≤ 3 := by
  have h := (log_facts (le_refl 2) hu).2.2.2
  unfold perronAbscissa
  have : 1 / Real.log u ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  linarith

lemma inv_abscissa_sub_one (u : ℝ) : 1 / (perronAbscissa u - 1) = Real.log u := by
  unfold perronAbscissa; simp

lemma rpow_abscissa {u : ℝ} (hu : 2 ≤ u) : u ^ perronAbscissa u = Real.exp 1 * u := by
  have h := (log_facts (le_refl 2) hu).2.2.2
  have hu0 : 0 < u := by linarith
  have hl : Real.log u ≠ 0 := by linarith
  rw [Real.rpow_def_of_pos hu0]
  unfold perronAbscissa
  rw [show Real.log u * (1 + 1 / Real.log u) = 1 + Real.log u by field_simp; ring,
    Real.exp_add, Real.exp_log hu0]

/-- Top and bottom sides. -/
lemma horiz_bound {u T T' B y : ℝ} (hT : 2 ≤ T) (hTu : T ≤ u) (hTT' : T ≤ T') (hy : |y| = T')
    (hB : 0 ≤ B)
    (hb : ∀ x : ℝ, -1 / 2 ≤ x → x ≤ perronAbscissa u →
      ‖deriv riemannZeta ((x : ℂ) + (y : ℂ) * I) / riemannZeta ((x : ℂ) + (y : ℂ) * I)‖ ≤
        B * Real.log (T + 2) ^ 2) :
    ‖∫ x in (-1 / 2 : ℝ)..perronAbscissa u, perronIntegrand u ((x : ℂ) + (y : ℂ) * I)‖ ≤
      10 * B * (u * Real.log (u * T) ^ 2 / T) := by
  have hu : 2 ≤ u := hT.trans hTu
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  obtain ⟨hL1, hLle, -, -, -⟩ := log_facts hT hTu
  have hc1 := abscissa_gt_one hu
  have hc3 := abscissa_le_three hu
  have hpt : ∀ x ∈ Set.uIoc (-1 / 2 : ℝ) (perronAbscissa u),
      ‖perronIntegrand u ((x : ℂ) + (y : ℂ) * I)‖ ≤
        B * Real.log (T + 2) ^ 2 * (Real.exp 1 * u) / T := by
    intro x hx
    rw [uIoc_of_le (by linarith)] at hx
    rw [norm_perronIntegrand hu0]
    have h1 := hb x hx.1.le hx.2
    have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
    have him : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
    have h2 : u ^ ((x : ℂ) + (y : ℂ) * I).re ≤ Real.exp 1 * u := by
      rw [hre, ← rpow_abscissa hu]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) hx.2
    have h3 : T ≤ ‖(x : ℂ) + (y : ℂ) * I‖ := by
      have := Complex.abs_im_le_norm ((x : ℂ) + (y : ℂ) * I)
      rw [him, hy] at this; linarith
    have h4 : 0 ≤ u ^ ((x : ℂ) + (y : ℂ) * I).re := Real.rpow_nonneg hu0.le _
    have h5 : 0 ≤ B * Real.log (T + 2) ^ 2 := by positivity
    have h6 : 0 ≤ Real.exp 1 * u := by positivity
    exact div_le_div₀ (mul_nonneg h5 h6) (mul_le_mul h1 h2 h4 h5) hT0 h3
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [abs_of_nonneg (by linarith)] at h
  refine h.trans ?_
  have e1 : Real.exp 1 * (perronAbscissa u - -1 / 2) ≤ 10 := by
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have e0 : 0 ≤ Real.exp 1 * (perronAbscissa u - -1 / 2) :=
    mul_nonneg (Real.exp_pos 1).le (by linarith)
  have e2 : Real.log (T + 2) ^ 2 ≤ Real.log (u * T) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hLle 2
  have e3 : 0 ≤ B * (u / T) := by positivity
  calc B * Real.log (T + 2) ^ 2 * (Real.exp 1 * u) / T * (perronAbscissa u - -1 / 2)
      = B * (u / T) * (Real.log (T + 2) ^ 2 * (Real.exp 1 * (perronAbscissa u - -1 / 2))) := by
        ring
    _ ≤ B * (u / T) * (Real.log (u * T) ^ 2 * 10) :=
        mul_le_mul_of_nonneg_left (mul_le_mul e2 e1 e0 (by positivity)) e3
    _ = 10 * B * (u * Real.log (u * T) ^ 2 / T) := by ring

lemma integral_inv_one_add_abs {A : ℝ} (hA : 0 ≤ A) :
    ∫ y in (-A)..A, 1 / (1 + |y|) = 2 * Real.log (1 + A) := by
  have hcont : Continuous (fun y : ℝ => 1 / (1 + |y|)) :=
    continuous_const.div (by fun_prop) fun y => by positivity
  have h1 : ∫ y in (0 : ℝ)..A, 1 / (1 + |y|) = Real.log (1 + A) := by
    rw [intervalIntegral.integral_congr (g := fun y : ℝ => 1 / (1 + y)) (fun y hy => by
      rw [uIcc_of_le hA] at hy
      simp [abs_of_nonneg hy.1])]
    rw [intervalIntegral.integral_comp_add_left (fun x : ℝ => 1 / x) 1,
      integral_one_div_of_pos (by norm_num) (by linarith)]
    simp
  have h2 : ∫ y in (-A)..0, 1 / (1 + |y|) = ∫ y in (0 : ℝ)..A, 1 / (1 + |y|) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := A) (fun y : ℝ => 1 / (1 + |y|))
    simp only [abs_neg, neg_zero] at this
    exact this.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hcont.intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _), h2, h1]
  ring

/-- Left side. -/
lemma left_bound {u T T' C : ℝ} (hT : 2 ≤ T) (hTu : T ≤ u) (hTT' : T ≤ T') (hT'1 : T' ≤ T + 1)
    (hC : 0 ≤ C)
    (hb : ∀ t : ℝ, ‖deriv riemannZeta ((-1 / 2 : ℂ) + (t : ℂ) * I) /
      riemannZeta ((-1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤ C * Real.log (|t| + 2)) :
    ‖∫ y in (-T')..T', perronIntegrand u (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      24 * C * (u * Real.log (u * T) ^ 2 / T) := by
  have hu : 2 ≤ u := hT.trans hTu
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hT'0 : 0 ≤ T' := by linarith
  obtain ⟨hL1, hLle, -, -, -⟩ := log_facts hT hTu
  have hcast : (((-1 / 2 : ℝ) : ℂ)) = (-1 / 2 : ℂ) := by push_cast; ring
  have hlogT' : 0 ≤ Real.log (T' + 2) := Real.log_nonneg (by linarith)
  have hpt : ∀ y ∈ Ioc (-T') T', ‖perronIntegrand u (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      (3 * C * Real.log (T' + 2)) * (1 / (1 + |y|)) := by
    intro y hy
    rw [norm_perronIntegrand hu0, hcast]
    have habs : |y| ≤ T' := abs_le.mpr ⟨hy.1.le, hy.2⟩
    have h1 : ‖deriv riemannZeta ((-1 / 2 : ℂ) + (y : ℂ) * I) /
        riemannZeta ((-1 / 2 : ℂ) + (y : ℂ) * I)‖ ≤ C * Real.log (T' + 2) :=
      (hb y).trans (mul_le_mul_of_nonneg_left
        (Real.log_le_log (by positivity) (by linarith)) hC)
    have hre : ((-1 / 2 : ℂ) + (y : ℂ) * I).re = -1 / 2 := by simp
    have him : ((-1 / 2 : ℂ) + (y : ℂ) * I).im = y := by simp
    have h2 : u ^ ((-1 / 2 : ℂ) + (y : ℂ) * I).re ≤ 1 := by
      rw [hre]; exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have h3 : (1 + |y|) / 3 ≤ ‖(-1 / 2 : ℂ) + (y : ℂ) * I‖ := by
      have a := Complex.abs_im_le_norm ((-1 / 2 : ℂ) + (y : ℂ) * I)
      have b := Complex.abs_re_le_norm ((-1 / 2 : ℂ) + (y : ℂ) * I)
      rw [him] at a
      rw [hre, show |(-1 / 2 : ℝ)| = 1 / 2 by rw [abs_of_neg (by norm_num)]; norm_num] at b
      linarith
    have h4 : 0 ≤ u ^ ((-1 / 2 : ℂ) + (y : ℂ) * I).re := Real.rpow_nonneg hu0.le _
    have h5 : 0 ≤ C * Real.log (T' + 2) := mul_nonneg hC hlogT'
    have hpos : 0 < (1 + |y|) / 3 := by positivity
    calc _ ≤ C * Real.log (T' + 2) * 1 / ((1 + |y|) / 3) :=
          div_le_div₀ (mul_nonneg h5 zero_le_one) (mul_le_mul h1 h2 h4 h5) hpos h3
      _ = (3 * C * Real.log (T' + 2)) * (1 / (1 + |y|)) := by
          have : (1 + |y|) ≠ 0 := by positivity
          field_simp
  have hcont : Continuous (fun y : ℝ => (3 * C * Real.log (T' + 2)) * (1 / (1 + |y|))) :=
    continuous_const.mul (continuous_const.div (by fun_prop) fun y => by positivity)
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (by linarith : -T' ≤ T')
    (Filter.Eventually.of_forall hpt) (hcont.intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul, integral_inv_one_add_abs hT'0] at h
  refine h.trans ?_
  have hsq : Real.log (T' + 2) ≤ 2 * Real.log (T + 2) := by
    have : Real.log (T' + 2) ≤ Real.log ((T + 2) ^ 2) :=
      Real.log_le_log (by linarith) (by nlinarith)
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hsq' : Real.log (1 + T') ≤ Real.log (T + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have hl0 : 0 ≤ Real.log (1 + T') := Real.log_nonneg (by linarith)
  have e2 : Real.log (T + 2) ^ 2 ≤ Real.log (u * T) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hLle 2
  have hr : 1 ≤ u / T := by rw [le_div_iff₀ hT0]; linarith
  have hX : Real.log (T + 2) ^ 2 ≤ u * Real.log (u * T) ^ 2 / T := by
    calc Real.log (T + 2) ^ 2 ≤ 1 * Real.log (u * T) ^ 2 := by linarith
      _ ≤ (u / T) * Real.log (u * T) ^ 2 := mul_le_mul_of_nonneg_right hr (by positivity)
      _ = u * Real.log (u * T) ^ 2 / T := by ring
  calc 3 * C * Real.log (T' + 2) * (2 * Real.log (1 + T'))
      ≤ 3 * C * (2 * Real.log (T + 2)) * (2 * Real.log (T + 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsq (by positivity))
          (by linarith) (by positivity) (by positivity)
    _ = 12 * C * Real.log (T + 2) ^ 2 := by ring
    _ ≤ 12 * C * (u * Real.log (u * T) ^ 2 / T) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ ≤ 24 * C * (u * Real.log (u * T) ^ 2 / T) := by
        have : 0 ≤ C * (u * Real.log (u * T) ^ 2 / T) := by positivity
        linarith

/-- A short vertical piece on the Perron line at height at least `T`. -/
lemma right_piece {u T M a b : ℝ} (hT : 2 ≤ T) (hTu : T ≤ u) (hM : 0 ≤ M)
    (hbound : ∀ s : ℂ, 1 < s.re → s.re ≤ 3 →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ 1 / (s.re - 1) + M)
    (hab : a ≤ b) (hba : b ≤ a + 1) (hy : ∀ y ∈ Ioc a b, T ≤ |y|) :
    ‖∫ y in a..b, perronIntegrand u ((perronAbscissa u : ℂ) + (y : ℂ) * I)‖ ≤
      3 * (1 + M / Real.log 2) * (u * Real.log (u * T) ^ 2 / T) := by
  have hu : 2 ≤ u := hT.trans hTu
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  obtain ⟨hL1, hLle, hule, h2u, hl2⟩ := log_facts hT hTu
  have hc1 := abscissa_gt_one hu
  have hc3 := abscissa_le_three hu
  have hlu : 0 ≤ Real.log u := by linarith
  have hpt : ∀ y ∈ Set.uIoc a b, ‖perronIntegrand u ((perronAbscissa u : ℂ) + (y : ℂ) * I)‖ ≤
      (Real.log u + M) * (Real.exp 1 * u) / T := by
    intro y hy'
    rw [uIoc_of_le hab] at hy'
    rw [norm_perronIntegrand hu0]
    have hre : ((perronAbscissa u : ℂ) + (y : ℂ) * I).re = perronAbscissa u := by simp
    have him : ((perronAbscissa u : ℂ) + (y : ℂ) * I).im = y := by simp
    have h1 := hbound ((perronAbscissa u : ℂ) + (y : ℂ) * I) (by rw [hre]; exact hc1)
      (by rw [hre]; exact hc3)
    rw [hre, inv_abscissa_sub_one] at h1
    have h2 : u ^ ((perronAbscissa u : ℂ) + (y : ℂ) * I).re = Real.exp 1 * u := by
      rw [hre, rpow_abscissa hu]
    have h3 : T ≤ ‖(perronAbscissa u : ℂ) + (y : ℂ) * I‖ := by
      have := Complex.abs_im_le_norm ((perronAbscissa u : ℂ) + (y : ℂ) * I)
      rw [him] at this; linarith [hy y hy']
    rw [h2]
    have h6 : 0 ≤ Real.exp 1 * u := by positivity
    exact div_le_div₀ (mul_nonneg (by linarith) h6) (mul_le_mul_of_nonneg_right h1 h6) hT0 h3
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [abs_of_nonneg (by linarith)] at h
  have hnn : 0 ≤ (Real.log u + M) * (Real.exp 1 * u) / T := by positivity
  have h' : ‖∫ y in a..b, perronIntegrand u ((perronAbscissa u : ℂ) + (y : ℂ) * I)‖ ≤
      (Real.log u + M) * (Real.exp 1 * u) / T :=
    h.trans (by nlinarith)
  refine h'.trans ?_
  have hM' : M ≤ M / Real.log 2 * Real.log u := by
    calc M = M / Real.log 2 * Real.log 2 := by field_simp
      _ ≤ M / Real.log 2 * Real.log u := mul_le_mul_of_nonneg_left h2u (by positivity)
  have hLu1 : 1 ≤ Real.log (u * T) := by linarith
  have hsq : Real.log (u * T) ≤ Real.log (u * T) ^ 2 := by nlinarith
  have e1 : Real.log u + M ≤ (1 + M / Real.log 2) * Real.log (u * T) ^ 2 := by
    have hk : 0 ≤ 1 + M / Real.log 2 := by positivity
    calc Real.log u + M ≤ (1 + M / Real.log 2) * Real.log u := by linarith
      _ ≤ (1 + M / Real.log 2) * Real.log (u * T) ^ 2 :=
          mul_le_mul_of_nonneg_left (by linarith) hk
  have e3 : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have hr : 0 ≤ u / T := by positivity
  calc (Real.log u + M) * (Real.exp 1 * u) / T
      = (Real.log u + M) * Real.exp 1 * (u / T) := by ring
    _ ≤ ((1 + M / Real.log 2) * Real.log (u * T) ^ 2) * 3 * (u / T) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul e1 e3 (Real.exp_pos 1).le (by positivity)) hr
    _ = 3 * (1 + M / Real.log 2) * (u * Real.log (u * T) ^ 2 / T) := by ring

end ZetaExplicit

#print axioms ZetaExplicit.horiz_bound
#print axioms ZetaExplicit.left_bound
#print axioms ZetaExplicit.right_piece
