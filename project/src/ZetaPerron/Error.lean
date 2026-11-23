import Mathlib
import ZetaShared.Perron
import ZetaPerron.Kernel
import ZetaPerron.Series

/-! Termwise error bounds for the truncated Perron formula and their summation. Mathlib only. -/

open Complex MeasureTheory Set ArithmeticFunction
open scoped Real Interval

noncomputable section

namespace ZetaPerron

/-- The weighted von Mangoldt term `Λ(n) (u/n)^c`. -/
def Aterm (u c : ℝ) (n : ℕ) : ℝ := Λ n * Real.exp (c * Ln u n)

/-- Extra bound for `1 ≤ n < N`. -/
def B1 (u T : ℝ) (N n : ℕ) : ℝ :=
  if 1 ≤ n ∧ n < N then (Real.exp 1 * u * Real.log u / T) / ((N : ℝ) - n) else 0

/-- Extra bound for `N + 2 ≤ n < 2N + 2`. -/
def B2 (u T : ℝ) (N n : ℕ) : ℝ :=
  if N + 2 ≤ n ∧ n < 2 * N + 2 then (6 * u * Real.log u / T) / ((n : ℝ) - N - 1) else 0

/-- Bound for the two integers next to `u`. -/
def B3 (u : ℝ) (N n : ℕ) : ℝ :=
  if n = N ∨ n = N + 1 then 11 * Real.log u else 0

/-- The `n`th term of `ψ(u) - perronIntegral`. -/
def errTerm (u c T : ℝ) (N n : ℕ) : ℂ :=
  (Λ n : ℂ) * ((if n ≤ N then (1 : ℂ) else 0) - kint (Ln u n) c T / (2 * π))

/-- The termwise majorant. -/
def bnd (u c T : ℝ) (N n : ℕ) : ℝ :=
  (2 / T) * Aterm u c n + B1 u T N n + B2 u T N n + B3 u N n

lemma Aterm_nonneg (u c : ℝ) (n : ℕ) : 0 ≤ Aterm u c n :=
  mul_nonneg vonMangoldt_nonneg (Real.exp_pos _).le

lemma two_pi_ne : (2 * (π : ℂ)) ≠ 0 := by
  have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  exact mul_ne_zero two_ne_zero this

lemma norm_two_pi : ‖(2 * (π : ℂ))‖ = 2 * π := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_two]

lemma norm_one_sub_div (K : ℂ) : ‖(1 : ℂ) - K / (2 * π)‖ = ‖K - 2 * π‖ / (2 * π) := by
  have e : (1 : ℂ) - K / (2 * π) = -((K - 2 * π) / (2 * π)) := by
    rw [← neg_div, neg_sub, sub_div, div_self two_pi_ne]
  rw [e, norm_neg, norm_div, norm_two_pi]

lemma norm_errTerm_le (u c T : ℝ) (N n : ℕ) (h : n ≤ N) :
    ‖errTerm u c T N n‖ = Λ n * (‖kint (Ln u n) c T - 2 * π‖ / (2 * π)) := by
  unfold errTerm
  rw [if_pos h, norm_mul, norm_one_sub_div, Complex.norm_real,
    Real.norm_of_nonneg vonMangoldt_nonneg]

lemma norm_errTerm_gt (u c T : ℝ) (N n : ℕ) (h : N < n) :
    ‖errTerm u c T N n‖ = Λ n * (‖kint (Ln u n) c T‖ / (2 * π)) := by
  unfold errTerm
  rw [if_neg (not_le.mpr h), zero_sub, norm_mul, norm_neg, norm_div, norm_two_pi,
    Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]

/-! ### Termwise bounds -/

lemma err_small (u c T : ℝ) (N n : ℕ) (hu : 2 ≤ u) (hT : 2 ≤ T) (hc1 : 1 < c)
    (hcu : c * Real.log u = Real.log u + 1) (hNu : (N : ℝ) ≤ u) (hn1 : 1 ≤ n) (hnN : n < N) :
    ‖errTerm u c T N n‖ ≤ (2 / T) * Aterm u c n
      + (Real.exp 1 * u * Real.log u / T) / ((N : ℝ) - n) := by
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnNR : (n : ℝ) + 1 ≤ N := by exact_mod_cast hnN
  have hn0 : (0 : ℝ) < n := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hd : 0 < (N : ℝ) - n := by linarith
  have hLlow : ((N : ℝ) - n) / N ≤ Ln u n := by
    have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hN0 hn0)
    have h2 : Real.log ((N : ℝ) / n) = Real.log N - Real.log n :=
      Real.log_div hN0.ne' hn0.ne'
    have h3 : Real.log N ≤ Real.log u := Real.log_le_log hN0 hNu
    have h4 : 1 - ((N : ℝ) / n)⁻¹ = ((N : ℝ) - n) / N := by field_simp
    unfold Ln
    linarith
  have hLpos : 0 < Ln u n := lt_of_lt_of_le (div_pos hd hN0) hLlow
  have hK := kint_bound_pos (L := Ln u n) (c := c) (T := T) hLpos (by linarith) hT0
  have hΛ0 : 0 ≤ Λ n := vonMangoldt_nonneg
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hnR
  have hΛ : Λ n ≤ Real.log u :=
    vonMangoldt_le_log.trans (Real.log_le_log hn0 (by linarith))
  have hEpos : 0 < Real.exp (c * Ln u n) := Real.exp_pos _
  have key1 : ‖kint (Ln u n) c T - 2 * π‖ / (2 * π)
      ≤ Real.exp (c * Ln u n) / (T * Ln u n) := by
    have hpi : (2 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
    calc ‖kint (Ln u n) c T - 2 * π‖ / (2 * π) ≤ ‖kint (Ln u n) c T - 2 * π‖ / 2 :=
          div_le_div_of_nonneg_left (norm_nonneg _) two_pos hpi
      _ ≤ (2 * Real.exp (c * Ln u n) / (T * Ln u n)) / 2 :=
          div_le_div_of_nonneg_right hK two_pos.le
      _ = Real.exp (c * Ln u n) / (T * Ln u n) := by ring
  have key2 : Real.exp (c * Ln u n) / (T * Ln u n)
      ≤ Real.exp (c * Ln u n) / (T * (((N : ℝ) - n) / N)) :=
    div_le_div_of_nonneg_left hEpos.le (by positivity)
      (mul_le_mul_of_nonneg_left hLlow hT0.le)
  have key3 : Real.exp (c * Ln u n) / (T * (((N : ℝ) - n) / N))
      = (1 / T) * Real.exp (c * Ln u n)
        + (Real.exp (c * Ln u n) * n) / T / ((N : ℝ) - n) := by
    have hdne : (N : ℝ) - n ≠ 0 := hd.ne'
    field_simp
    ring
  have key4 : Real.exp (c * Ln u n) * n ≤ u * Real.exp 1 := by
    have h1 : Real.exp (c * Ln u n) * n = Real.exp (c * Ln u n + Real.log n) := by
      rw [Real.exp_add, Real.exp_log hn0]
    have h2 : c * Ln u n + Real.log n ≤ Real.log u + 1 := by
      unfold Ln
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ c - 1) hlogn]
    have h3 : Real.exp (Real.log u + 1) = u * Real.exp 1 := by
      rw [Real.exp_add, Real.exp_log hu0]
    rw [h1, ← h3]
    exact Real.exp_le_exp.mpr h2
  rw [norm_errTerm_le u c T N n hnN.le]
  have hmain : Λ n * (‖kint (Ln u n) c T - 2 * π‖ / (2 * π))
      ≤ Λ n * ((1 / T) * Real.exp (c * Ln u n)
        + (Real.exp (c * Ln u n) * n) / T / ((N : ℝ) - n)) := by
    apply mul_le_mul_of_nonneg_left _ hΛ0
    rw [← key3]
    exact key1.trans key2
  have h5 : Λ n * ((Real.exp (c * Ln u n) * n) / T / ((N : ℝ) - n))
      ≤ (Real.exp 1 * u * Real.log u / T) / ((N : ℝ) - n) := by
    rw [← mul_div_assoc, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hd.le
    apply div_le_div_of_nonneg_right _ hT0.le
    calc Λ n * (Real.exp (c * Ln u n) * n) ≤ Real.log u * (u * Real.exp 1) :=
          mul_le_mul hΛ key4 (by positivity) (le_trans hΛ0 hΛ)
      _ = Real.exp 1 * u * Real.log u := by ring
  have h6 : (1 / T) * (Λ n * Real.exp (c * Ln u n))
      ≤ (2 / T) * (Λ n * Real.exp (c * Ln u n)) := by
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg hΛ0 hEpos.le)
    exact div_le_div_of_nonneg_right (by norm_num) hT0.le
  have h7 : Λ n * ((1 / T) * Real.exp (c * Ln u n)
        + (Real.exp (c * Ln u n) * n) / T / ((N : ℝ) - n))
      = (1 / T) * (Λ n * Real.exp (c * Ln u n))
        + Λ n * ((Real.exp (c * Ln u n) * n) / T / ((N : ℝ) - n)) := by ring
  unfold Aterm
  linarith

lemma err_at_floor (u c T : ℝ) (N : ℕ) (hu : 2 ≤ u) (hT : 2 ≤ T) (hc1 : 1 < c) (hc3 : c ≤ 3)
    (hNu : (N : ℝ) ≤ u) (huN : u < N + 1) (hN2 : 2 ≤ N) :
    ‖errTerm u c T N N‖ ≤ 11 * Real.log u := by
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hN2R : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hL0 : 0 ≤ Ln u N := by
    unfold Ln
    linarith [Real.log_le_log hN0 hNu]
  have hL1 : Ln u N ≤ 1 / 2 := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hu0 hN0)
    have h2 : Real.log (u / N) = Real.log u - Real.log N := Real.log_div hu0.ne' hN0.ne'
    have h3 : u / N - 1 ≤ 1 / 2 := by
      rw [div_sub_one hN0.ne', div_le_iff₀ hN0]
      linarith
    unfold Ln
    linarith
  have hK := kint_bound_nonneg (L := Ln u N) (c := c) (T := T) hL0 (by linarith) hT0
  have hE : Real.exp (c * Ln u N) ≤ 9 := by
    have h0 : c * Ln u N ≤ 3 * (1 / 2) := mul_le_mul hc3 hL1 hL0 (by norm_num)
    have h1 : c * Ln u N ≤ 1 + 1 := by linarith
    have h2 : Real.exp (1 + 1) = Real.exp 1 * Real.exp 1 := Real.exp_add 1 1
    have h3 := Real.exp_one_lt_three
    have h4 : Real.exp (c * Ln u N) ≤ Real.exp (1 + 1) := Real.exp_le_exp.mpr h1
    nlinarith [Real.exp_pos 1]
  have hcoef : 4 + 2 * c / T ≤ 7 := by
    have : 2 * c / T ≤ 3 := by
      rw [div_le_iff₀ hT0]
      nlinarith
    linarith
  have hKb : ‖kint (Ln u N) c T - 2 * π‖ ≤ 63 := by
    calc ‖kint (Ln u N) c T - 2 * π‖ ≤ (4 + 2 * c / T) * Real.exp (c * Ln u N) := hK
      _ ≤ 7 * 9 := mul_le_mul hcoef hE (Real.exp_pos _).le (by norm_num)
      _ = 63 := by norm_num
  rw [norm_errTerm_le u c T N N le_rfl]
  have hΛ : Λ N ≤ Real.log u := vonMangoldt_le_log.trans (Real.log_le_log hN0 hNu)
  have hdiv : ‖kint (Ln u N) c T - 2 * π‖ / (2 * π) ≤ 11 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hlog : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  calc Λ N * (‖kint (Ln u N) c T - 2 * π‖ / (2 * π)) ≤ Real.log u * 11 :=
        mul_le_mul hΛ hdiv (by positivity) hlog
    _ = 11 * Real.log u := by ring

lemma err_above_floor (u c T : ℝ) (N : ℕ) (hu : 2 ≤ u) (hT : 2 ≤ T) (hc1 : 1 < c)
    (hNu : (N : ℝ) ≤ u) (huN : u < N + 1) :
    ‖errTerm u c T N (N + 1)‖ ≤ 11 * Real.log u := by
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hlog : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have hL : Ln u (N + 1) ≤ 0 := by
    unfold Ln
    push_cast
    linarith [Real.log_le_log hu0 huN.le]
  have hK := kint_bound_nonpos (L := Ln u (N + 1)) (c := c) (T := T) hL (by linarith) hT0
  have hE : Real.exp (c * Ln u (N + 1)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos (by linarith) hL)
  rw [norm_errTerm_gt u c T N (N + 1) (Nat.lt_succ_self N)]
  have hΛ : Λ (N + 1) ≤ 2 * Real.log u := by
    have h1 : Λ (N + 1) ≤ Real.log ((N + 1 : ℕ) : ℝ) := vonMangoldt_le_log
    have h2 : Real.log ((N + 1 : ℕ) : ℝ) ≤ Real.log (u ^ 2) :=
      Real.log_le_log (by positivity) (by push_cast; nlinarith)
    rw [Real.log_pow] at h2
    push_cast at h1 h2
    linarith
  have hdiv : ‖kint (Ln u (N + 1)) c T‖ / (2 * π) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three]
  calc Λ (N + 1) * (‖kint (Ln u (N + 1)) c T‖ / (2 * π)) ≤ (2 * Real.log u) * 1 :=
        mul_le_mul hΛ hdiv (by positivity) (by positivity)
    _ ≤ 11 * Real.log u := by linarith

lemma err_large (u c T : ℝ) (N n : ℕ) (hu : 2 ≤ u) (hT : 2 ≤ T) (hc1 : 1 < c)
    (huN : u < N + 1) (hn : N + 2 ≤ n) :
    ‖errTerm u c T N n‖ ≤ (1 / T) * Aterm u c n
      + (1 / T) * (Aterm u c n * ((N : ℝ) + 1)) / ((n : ℝ) - N - 1) := by
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hnR : (N : ℝ) + 2 ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hm : 0 < (n : ℝ) - N - 1 := by linarith
  have hLlow : ((n : ℝ) - N - 1) / n ≤ -Ln u n := by
    have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hn0 hN1)
    have h2 : Real.log ((n : ℝ) / ((N : ℝ) + 1)) = Real.log n - Real.log ((N : ℝ) + 1) :=
      Real.log_div hn0.ne' hN1.ne'
    have h3 : Real.log u ≤ Real.log ((N : ℝ) + 1) := Real.log_le_log hu0 huN.le
    have h4 : 1 - ((n : ℝ) / ((N : ℝ) + 1))⁻¹ = ((n : ℝ) - N - 1) / n := by field_simp; ring
    unfold Ln
    linarith
  have hLpos : 0 < -Ln u n := lt_of_lt_of_le (div_pos hm hn0) hLlow
  have hLneg : Ln u n < 0 := by linarith
  have hK := kint_bound_neg (L := Ln u n) (c := c) (T := T) hLneg (by linarith) hT0
  have hΛ0 : 0 ≤ Λ n := vonMangoldt_nonneg
  have hEpos : 0 < Real.exp (c * Ln u n) := Real.exp_pos _
  have key1 : ‖kint (Ln u n) c T‖ / (2 * π)
      ≤ Real.exp (c * Ln u n) / (T * (-Ln u n)) := by
    have hpi : (2 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
    calc ‖kint (Ln u n) c T‖ / (2 * π) ≤ ‖kint (Ln u n) c T‖ / 2 :=
          div_le_div_of_nonneg_left (norm_nonneg _) two_pos hpi
      _ ≤ (2 * Real.exp (c * Ln u n) / (T * (-Ln u n))) / 2 :=
          div_le_div_of_nonneg_right hK two_pos.le
      _ = Real.exp (c * Ln u n) / (T * (-Ln u n)) := by ring
  have key2 : Real.exp (c * Ln u n) / (T * (-Ln u n))
      ≤ Real.exp (c * Ln u n) / (T * (((n : ℝ) - N - 1) / n)) :=
    div_le_div_of_nonneg_left hEpos.le (by positivity)
      (mul_le_mul_of_nonneg_left hLlow hT0.le)
  have key3 : Real.exp (c * Ln u n) / (T * (((n : ℝ) - N - 1) / n))
      = (1 / T) * Real.exp (c * Ln u n)
        + (1 / T) * (Real.exp (c * Ln u n) * ((N : ℝ) + 1)) / ((n : ℝ) - N - 1) := by
    have hmne : (n : ℝ) - N - 1 ≠ 0 := hm.ne'
    field_simp
    ring
  rw [norm_errTerm_gt u c T N n (by omega)]
  have hmain : Λ n * (‖kint (Ln u n) c T‖ / (2 * π))
      ≤ Λ n * ((1 / T) * Real.exp (c * Ln u n)
        + (1 / T) * (Real.exp (c * Ln u n) * ((N : ℝ) + 1)) / ((n : ℝ) - N - 1)) := by
    apply mul_le_mul_of_nonneg_left _ hΛ0
    rw [← key3]
    exact key1.trans key2
  have h7 : Λ n * ((1 / T) * Real.exp (c * Ln u n)
        + (1 / T) * (Real.exp (c * Ln u n) * ((N : ℝ) + 1)) / ((n : ℝ) - N - 1))
      = (1 / T) * (Λ n * Real.exp (c * Ln u n))
        + (1 / T) * (Λ n * Real.exp (c * Ln u n) * ((N : ℝ) + 1)) / ((n : ℝ) - N - 1) := by
    ring
  unfold Aterm
  linarith

/-- The termwise majorant dominates the error terms. -/
lemma err_le_bnd (u c T : ℝ) (N : ℕ) (hu : 2 ≤ u) (hT : 2 ≤ T) (hc1 : 1 < c) (hc3 : c ≤ 3)
    (hcu : c * Real.log u = Real.log u + 1) (hNu : (N : ℝ) ≤ u) (huN : u < N + 1) (n : ℕ) :
    ‖errTerm u c T N n‖ ≤ bnd u c T N n := by
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hlog : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have hN2 : 2 ≤ N := by
    have h1 : (1 : ℝ) < N := by linarith
    have h2 : 1 < N := by exact_mod_cast h1
    omega
  have hA := Aterm_nonneg u c n
  have hA2 : 0 ≤ (2 / T) * Aterm u c n := mul_nonneg (by positivity) hA
  unfold bnd B1 B2 B3
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · have c1 : ¬(1 ≤ n ∧ n < N) := by omega
    have c2 : ¬(N + 2 ≤ n ∧ n < 2 * N + 2) := by omega
    have c3 : ¬(n = N ∨ n = N + 1) := by omega
    rw [if_neg c1, if_neg c2, if_neg c3]
    have : errTerm u c T N n = 0 := by
      rw [h0]
      simp [errTerm]
    rw [this, norm_zero]
    linarith
  rcases lt_trichotomy n N with h | h | h
  · have c1 : 1 ≤ n ∧ n < N := ⟨hn, h⟩
    have c2 : ¬(N + 2 ≤ n ∧ n < 2 * N + 2) := by omega
    have c3 : ¬(n = N ∨ n = N + 1) := by omega
    rw [if_pos c1, if_neg c2, if_neg c3]
    have := err_small u c T N n hu hT hc1 hcu hNu hn h
    linarith
  · have c1 : ¬(1 ≤ n ∧ n < N) := by omega
    have c2 : ¬(N + 2 ≤ n ∧ n < 2 * N + 2) := by omega
    have c3 : n = N ∨ n = N + 1 := Or.inl h
    rw [if_neg c1, if_neg c2, if_pos c3]
    have := err_at_floor u c T N hu hT hc1 hc3 hNu huN hN2
    rw [h]
    rw [h] at hA2
    linarith
  · rcases Nat.lt_or_ge n (N + 2) with h2 | h2
    · have hn' : n = N + 1 := by omega
      have c1 : ¬(1 ≤ n ∧ n < N) := by omega
      have c2 : ¬(N + 2 ≤ n ∧ n < 2 * N + 2) := by omega
      have c3 : n = N ∨ n = N + 1 := Or.inr hn'
      rw [if_neg c1, if_neg c2, if_pos c3]
      have := err_above_floor u c T N hu hT hc1 hNu huN
      rw [hn']
      rw [hn'] at hA2
      linarith
    · have hbase := err_large u c T N n hu hT hc1 huN h2
      have hnR : (N : ℝ) + 2 ≤ n := by exact_mod_cast h2
      have hm : 0 < (n : ℝ) - N - 1 := by linarith
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      rcases Nat.lt_or_ge n (2 * N + 2) with h3 | h3
      · have c1 : ¬(1 ≤ n ∧ n < N) := by omega
        have c2 : N + 2 ≤ n ∧ n < 2 * N + 2 := ⟨h2, h3⟩
        have c3 : ¬(n = N ∨ n = N + 1) := by omega
        rw [if_neg c1, if_pos c2, if_neg c3]
        have hn0 : (0 : ℝ) < n := by linarith
        have hn3 : (n : ℝ) ≤ u ^ 3 := by
          have h4 : (n : ℝ) + 1 ≤ 2 * (N : ℝ) + 2 := by exact_mod_cast h3
          nlinarith [sq_nonneg (u - 2), mul_nonneg hu0.le (sq_nonneg (u - 2))]
        have hΛ : Λ n ≤ 3 * Real.log u := by
          have h1 : Λ n ≤ Real.log (n : ℝ) := vonMangoldt_le_log
          have h2' : Real.log (n : ℝ) ≤ Real.log (u ^ 3) := Real.log_le_log hn0 hn3
          rw [Real.log_pow] at h2'
          push_cast at h2'
          linarith
        have hL : Ln u n ≤ 0 := by
          unfold Ln
          linarith [Real.log_le_log hu0 (by linarith : u ≤ (n : ℝ))]
        have hE : Real.exp (c * Ln u n) ≤ 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos (by linarith) hL)
        have hAle : Aterm u c n ≤ 3 * Real.log u := by
          unfold Aterm
          calc Λ n * Real.exp (c * Ln u n) ≤ (3 * Real.log u) * 1 :=
                mul_le_mul hΛ hE (Real.exp_pos _).le (by positivity)
            _ = 3 * Real.log u := by ring
        have hprod : Aterm u c n * ((N : ℝ) + 1) ≤ 6 * u * Real.log u := by
          calc Aterm u c n * ((N : ℝ) + 1) ≤ (3 * Real.log u) * (2 * u) :=
                mul_le_mul hAle (by linarith) (by linarith) (by positivity)
            _ = 6 * u * Real.log u := by ring
        have hfin : (1 / T) * (Aterm u c n * ((N : ℝ) + 1)) / ((n : ℝ) - N - 1)
            ≤ (6 * u * Real.log u / T) / ((n : ℝ) - N - 1) := by
          apply div_le_div_of_nonneg_right _ hm.le
          rw [one_div_mul_eq_div]
          exact div_le_div_of_nonneg_right hprod hT0.le
        have h6 : (1 / T) * Aterm u c n ≤ (2 / T) * Aterm u c n := by
          apply mul_le_mul_of_nonneg_right _ hA
          exact div_le_div_of_nonneg_right (by norm_num) hT0.le
        linarith
      · have c1 : ¬(1 ≤ n ∧ n < N) := by omega
        have c2 : ¬(N + 2 ≤ n ∧ n < 2 * N + 2) := by omega
        have c3 : ¬(n = N ∨ n = N + 1) := by omega
        rw [if_neg c1, if_neg c2, if_neg c3]
        have h4 : 2 * (N : ℝ) + 2 ≤ n := by exact_mod_cast h3
        have hfin : (1 / T) * (Aterm u c n * ((N : ℝ) + 1)) / ((n : ℝ) - N - 1)
            ≤ (1 / T) * Aterm u c n := by
          rw [div_le_iff₀ hm]
          have h5 : Aterm u c n * ((N : ℝ) + 1) ≤ Aterm u c n * ((n : ℝ) - N - 1) :=
            mul_le_mul_of_nonneg_left (by linarith) hA
          have h6 : (0 : ℝ) ≤ 1 / T := by positivity
          calc (1 / T) * (Aterm u c n * ((N : ℝ) + 1))
              ≤ (1 / T) * (Aterm u c n * ((n : ℝ) - N - 1)) := mul_le_mul_of_nonneg_left h5 h6
            _ = (1 / T) * Aterm u c n * ((n : ℝ) - N - 1) := by ring
        have h8 : (2 / T) * Aterm u c n = (1 / T) * Aterm u c n + (1 / T) * Aterm u c n := by
          ring
        linarith

/-! ### Summing the majorant -/

lemma sum_range_inv_le (N : ℕ) : ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  have e : ((harmonic N : ℚ) : ℝ) = ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) := by
    unfold harmonic
    push_cast
    simp [one_div]
  rw [e] at h
  exact h

lemma sum_Ico_reflect_le (N : ℕ) :
    ∑ n ∈ Finset.Ico 1 N, 1 / ((N : ℝ) - n) ≤ 1 + Real.log N := by
  have e : ∀ n ∈ Finset.Ico 1 N, 1 / ((N : ℝ) - n) = (fun j : ℕ => 1 / (j : ℝ)) (N - n) := by
    intro n hn
    have := (Finset.mem_Ico.mp hn).2
    simp only
    rw [Nat.cast_sub this.le]
  rw [Finset.sum_congr rfl e, Finset.sum_Ico_reflect (fun j : ℕ => 1 / (j : ℝ)) 1 (Nat.le_succ N)]
  have e1 : N + 1 - N = 1 := by omega
  have e2 : N + 1 - 1 = N := by omega
  rw [e1, e2, Finset.sum_Ico_eq_sum_range]
  have e3 : ∀ k ∈ Finset.range (N - 1), 1 / (((1 + k : ℕ)) : ℝ) = 1 / ((k : ℝ) + 1) := by
    intro k _
    push_cast
    ring
  rw [Finset.sum_congr rfl e3]
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le N 1))
    (fun _ _ _ => by positivity)) (sum_range_inv_le N)

lemma sum_Ico_shift_le (N : ℕ) :
    ∑ n ∈ Finset.Ico (N + 2) (2 * N + 2), 1 / ((n : ℝ) - N - 1) ≤ 1 + Real.log N := by
  rw [Finset.sum_Ico_eq_sum_range]
  have e1 : 2 * N + 2 - (N + 2) = N := by omega
  rw [e1]
  have e3 : ∀ k ∈ Finset.range N, 1 / ((((N + 2 + k : ℕ)) : ℝ) - N - 1) = 1 / ((k : ℝ) + 1) := by
    intro k _
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl e3]
  exact sum_range_inv_le N

lemma hasSum_B1 (u T : ℝ) (N : ℕ) :
    HasSum (fun n => B1 u T N n)
      ((Real.exp 1 * u * Real.log u / T) * ∑ n ∈ Finset.Ico 1 N, 1 / ((N : ℝ) - n)) := by
  have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (f := fun n => B1 u T N n) (s := Finset.Ico 1 N)
    (fun n hn => if_neg (fun h => hn (Finset.mem_Ico.mpr h)))
  have e : ∑ n ∈ Finset.Ico 1 N, B1 u T N n
      = (Real.exp 1 * u * Real.log u / T) * ∑ n ∈ Finset.Ico 1 N, 1 / ((N : ℝ) - n) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    unfold B1
    rw [if_pos (Finset.mem_Ico.mp hn)]
    ring
  rw [e] at h
  exact h

lemma hasSum_B2 (u T : ℝ) (N : ℕ) :
    HasSum (fun n => B2 u T N n)
      ((6 * u * Real.log u / T)
        * ∑ n ∈ Finset.Ico (N + 2) (2 * N + 2), 1 / ((n : ℝ) - N - 1)) := by
  have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (f := fun n => B2 u T N n)
    (s := Finset.Ico (N + 2) (2 * N + 2))
    (fun n hn => if_neg (fun h => hn (Finset.mem_Ico.mpr h)))
  have e : ∑ n ∈ Finset.Ico (N + 2) (2 * N + 2), B2 u T N n
      = (6 * u * Real.log u / T)
        * ∑ n ∈ Finset.Ico (N + 2) (2 * N + 2), 1 / ((n : ℝ) - N - 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    unfold B2
    rw [if_pos (Finset.mem_Ico.mp hn)]
    ring
  rw [e] at h
  exact h

lemma hasSum_B3 (u : ℝ) (N : ℕ) :
    HasSum (fun n => B3 u N n) (11 * Real.log u + 11 * Real.log u) := by
  have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (f := fun n => B3 u N n) (s := {N, N + 1})
    (fun n hn => if_neg (fun h => hn (by
      rcases h with h | h
      · exact Finset.mem_insert.mpr (Or.inl h)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h)))))
  have e : ∑ n ∈ ({N, N + 1} : Finset ℕ), B3 u N n = 11 * Real.log u + 11 * Real.log u := by
    rw [Finset.sum_pair (by omega)]
    unfold B3
    rw [if_pos (Or.inl rfl), if_pos (Or.inr rfl)]
  rw [e] at h
  exact h

/-- The truncated Perron formula with abstract abscissa `c` and floor `N`. -/
theorem perron_bound_aux (u T c : ℝ) (N : ℕ) (hT : 2 ≤ T) (hTu : T ≤ u)
    (hc : c = 1 + 1 / Real.log u) (hNu : (N : ℝ) ≤ u) (huN : u < N + 1) (ψu : ℝ)
    (hψ : HasSum (fun n : ℕ => (Λ n : ℂ) * (if n ≤ N then (1 : ℂ) else 0)) (ψu : ℂ)) :
    ‖(ψu : ℂ) - (1 / (2 * (π : ℂ)))
        * ∫ t in (-T)..T, ZetaShared.perronIntegrand u ((c : ℂ) + (t : ℂ) * I)‖
      ≤ 100 * (u * Real.log u ^ 2 / T + Real.log u) := by
  have hu : 2 ≤ u := le_trans hT hTu
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hl : 1 / 2 < Real.log u := by
    have h1 := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log u := Real.log_le_log two_pos hu
    have h3 : (1 : ℝ) / 2 < 0.6931471803 := by norm_num
    linarith
  have hl0 : 0 < Real.log u := by linarith
  have hc1 : 1 < c := by
    rw [hc]
    have : 0 < 1 / Real.log u := by positivity
    linarith
  have hc3 : c ≤ 3 := by
    rw [hc]
    have : 1 / Real.log u ≤ 2 := by
      rw [div_le_iff₀ hl0]
      linarith
    linarith
  have hcu : c * Real.log u = Real.log u + 1 := by
    rw [hc]
    field_simp
  have hε : 0 < 1 / (2 * Real.log u) := by positivity
  have hcε : c = 1 + 2 * (1 / (2 * Real.log u)) := by
    rw [hc]
    field_simp
  have hA := summable_A u c (1 / (2 * Real.log u)) hε hcε
  have h2 := hasSum_kint u c T hu0 hc1 hA
  have herr : HasSum (fun n => errTerm u c T N n)
      ((ψu : ℂ) - (1 / (2 * (π : ℂ)))
        * ∫ t in (-T)..T, ZetaShared.perronIntegrand u ((c : ℂ) + (t : ℂ) * I)) := by
    have h3 := hψ.sub (h2.mul_left (1 / (2 * (π : ℂ))))
    have e : (fun n : ℕ => (Λ n : ℂ) * (if n ≤ N then (1 : ℂ) else 0)
        - 1 / (2 * (π : ℂ)) * ((Λ n : ℂ) * kint (Ln u n) c T))
        = fun n => errTerm u c T N n := by
      funext n
      unfold errTerm
      ring
    rw [e] at h3
    exact h3
  have hb : HasSum (fun n => bnd u c T N n)
      ((2 / T) * ∑' n, Aterm u c n
        + (Real.exp 1 * u * Real.log u / T) * ∑ n ∈ Finset.Ico 1 N, 1 / ((N : ℝ) - n)
        + (6 * u * Real.log u / T)
          * ∑ n ∈ Finset.Ico (N + 2) (2 * N + 2), 1 / ((n : ℝ) - N - 1)
        + (11 * Real.log u + 11 * Real.log u)) := by
    have hAs : HasSum (fun n => Aterm u c n) (∑' n, Aterm u c n) := hA.hasSum
    exact (((hAs.mul_left (2 / T)).add (hasSum_B1 u T N)).add (hasSum_B2 u T N)).add
      (hasSum_B3 u N)
  have hnorm := herr.norm_le_of_bounded hb
    (err_le_bnd u c T N hu hT hc1 hc3 hcu hNu huN)
  refine hnorm.trans ?_
  -- numerical estimate of the majorant
  have hN2R : (1 : ℝ) < N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hlogN : Real.log N ≤ Real.log u := Real.log_le_log hN0 hNu
  have he3 : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hSA : ∑' n, Aterm u c n ≤ 24 * u * Real.log u ^ 2 := by
    have h1 : ∑' n, Aterm u c n
        ≤ Real.exp (c * Real.log u) / (1 / (2 * Real.log u))
          * (1 + 1 / (1 / (2 * Real.log u))) :=
      tsum_A_le u c (1 / (2 * Real.log u)) hε hcε
    have h2 : Real.exp (c * Real.log u) / (1 / (2 * Real.log u))
          * (1 + 1 / (1 / (2 * Real.log u)))
        = u * Real.exp 1 * (2 * Real.log u) * (1 + 2 * Real.log u) := by
      rw [hcu, Real.exp_add, Real.exp_log hu0]
      field_simp
    rw [h2] at h1
    have h3 : u * Real.exp 1 * (2 * Real.log u) * (1 + 2 * Real.log u)
        ≤ u * 3 * (2 * Real.log u) * (4 * Real.log u) := by
      have ha : u * Real.exp 1 ≤ u * 3 := mul_le_mul_of_nonneg_left he3 hu0.le
      have hb' : u * Real.exp 1 * (2 * Real.log u) ≤ u * 3 * (2 * Real.log u) :=
        mul_le_mul_of_nonneg_right ha (by positivity)
      exact mul_le_mul hb' (by linarith) (by positivity) (by positivity)
    have h4 : u * 3 * (2 * Real.log u) * (4 * Real.log u) = 24 * u * Real.log u ^ 2 := by ring
    linarith
  have hQ : 0 ≤ u * Real.log u ^ 2 / T := by positivity
  have hpA : (2 / T) * ∑' n, Aterm u c n ≤ 48 * (u * Real.log u ^ 2 / T) := by
    calc (2 / T) * ∑' n, Aterm u c n ≤ (2 / T) * (24 * u * Real.log u ^ 2) :=
          mul_le_mul_of_nonneg_left hSA (by positivity)
      _ = 48 * (u * Real.log u ^ 2 / T) := by ring
  have hs1 : ∑ n ∈ Finset.Ico 1 N, 1 / ((N : ℝ) - n) ≤ 3 * Real.log u := by
    have := sum_Ico_reflect_le N
    linarith
  have hs2 : ∑ n ∈ Finset.Ico (N + 2) (2 * N + 2), 1 / ((n : ℝ) - N - 1) ≤ 3 * Real.log u := by
    have := sum_Ico_shift_le N
    linarith
  have hpB1 : (Real.exp 1 * u * Real.log u / T) * ∑ n ∈ Finset.Ico 1 N, 1 / ((N : ℝ) - n)
      ≤ 9 * (u * Real.log u ^ 2 / T) := by
    have hX : Real.exp 1 * u * Real.log u / T ≤ 3 * u * Real.log u / T := by
      apply div_le_div_of_nonneg_right _ hT0.le
      have : Real.exp 1 * u ≤ 3 * u := mul_le_mul_of_nonneg_right he3 hu0.le
      exact mul_le_mul_of_nonneg_right this hl0.le
    have hX0 : 0 ≤ Real.exp 1 * u * Real.log u / T := by positivity
    calc (Real.exp 1 * u * Real.log u / T) * ∑ n ∈ Finset.Ico 1 N, 1 / ((N : ℝ) - n)
        ≤ (Real.exp 1 * u * Real.log u / T) * (3 * Real.log u) :=
          mul_le_mul_of_nonneg_left hs1 hX0
      _ ≤ (3 * u * Real.log u / T) * (3 * Real.log u) :=
          mul_le_mul_of_nonneg_right hX (by positivity)
      _ = 9 * (u * Real.log u ^ 2 / T) := by ring
  have hpB2 : (6 * u * Real.log u / T)
        * ∑ n ∈ Finset.Ico (N + 2) (2 * N + 2), 1 / ((n : ℝ) - N - 1)
      ≤ 18 * (u * Real.log u ^ 2 / T) := by
    have hX0 : 0 ≤ 6 * u * Real.log u / T := by positivity
    calc (6 * u * Real.log u / T)
          * ∑ n ∈ Finset.Ico (N + 2) (2 * N + 2), 1 / ((n : ℝ) - N - 1)
        ≤ (6 * u * Real.log u / T) * (3 * Real.log u) := mul_le_mul_of_nonneg_left hs2 hX0
      _ = 18 * (u * Real.log u ^ 2 / T) := by ring
  linarith

end ZetaPerron
