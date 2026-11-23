import Mathlib
import ZetaShared.Perron
import ZetaPerron.Kernel

/-! The Dirichlet series of `-ζ'/ζ` on the Perron line, termwise integration, and a bound for
`∑ Λ(n) (u/n)^c`. Mathlib only. -/

open Complex MeasureTheory Set ArithmeticFunction
open scoped Real Interval

noncomputable section

namespace ZetaPerron

/-- `log (u / n)`, written as a difference. -/
def Ln (u : ℝ) (n : ℕ) : ℝ := Real.log u - Real.log n

/-! ### `∑ n^{-(1+ε)} ≤ 1 + 1/ε` -/

lemma sum_range_rpow_le (ε : ℝ) (hε : 0 < ε) (a : ℕ) :
    ∑ i ∈ Finset.range (a + 2), ((i : ℝ) ^ (1 + ε))⁻¹ ≤ 1 + 1 / ε := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have h0 : (((0 : ℕ) : ℝ) ^ (1 + ε))⁻¹ = 0 := by
    rw [Nat.cast_zero, Real.zero_rpow (by linarith), inv_zero]
  have h1 : (((0 + 1 : ℕ) : ℝ) ^ (1 + ε))⁻¹ = 1 := by simp
  rw [h0, h1, add_zero]
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-(1 + ε))) (Icc (1 : ℝ) (1 + (a : ℝ))) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)).mono
      (fun x hx => lt_of_lt_of_le zero_lt_one hx.1)
  have hsum := AntitoneOn.sum_le_integral (x₀ := 1) (a := a)
    (f := fun x : ℝ => x ^ (-(1 + ε))) hanti
  have hterm : ∀ i ∈ Finset.range a, (((i + 1 + 1 : ℕ) : ℝ) ^ (1 + ε))⁻¹
      = (fun x : ℝ => x ^ (-(1 + ε))) (1 + ((i + 1 : ℕ) : ℝ)) := by
    intro i _
    have hpos : (0 : ℝ) ≤ 1 + ((i + 1 : ℕ) : ℝ) := by positivity
    show _ = (1 + ((i + 1 : ℕ) : ℝ)) ^ (-(1 + ε))
    rw [Real.rpow_neg hpos]
    congr 2
    push_cast; ring
  rw [Finset.sum_congr rfl hterm]
  have hint : ∫ x in (1 : ℝ)..1 + (a : ℝ), x ^ (-(1 + ε)) ≤ 1 / ε := by
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    rw [integral_rpow (Or.inr ⟨by linarith, by
      rw [Set.uIcc_of_le (by linarith)]
      intro h
      linarith [h.1]⟩)]
    have e : -(1 + ε) + 1 = -ε := by ring
    rw [e, Real.one_rpow, div_neg, ← neg_div, neg_sub]
    exact div_le_div_of_nonneg_right
      (by linarith [Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + a) (-ε)]) hε.le
  linarith

lemma tsum_rpow_le (ε : ℝ) (hε : 0 < ε) : ∑' n : ℕ, ((n : ℝ) ^ (1 + ε))⁻¹ ≤ 1 + 1 / ε := by
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity)
  intro n
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (by omega : n ≤ n + 2)) (fun _ _ _ => by positivity))
    (sum_range_rpow_le ε hε n)

/-! ### The weighted von Mangoldt sum -/

lemma vonMangoldt_mul_exp_le (u c ε : ℝ) (hε : 0 < ε) (hc : c = 1 + 2 * ε) (n : ℕ) :
    Λ n * Real.exp (c * Ln u n) ≤ Real.exp (c * Real.log u) / ε * ((n : ℝ) ^ (1 + ε))⁻¹ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : (((0 : ℕ) : ℝ) ^ (1 + ε))⁻¹ = 0 := by
      rw [Nat.cast_zero, Real.zero_rpow (by linarith), inv_zero]
    rw [h0]; simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : Λ n ≤ (n : ℝ) ^ ε / ε :=
      vonMangoldt_le_log.trans (Real.log_le_rpow_div hn'.le hε)
    have h2 : Real.exp (c * Ln u n) = Real.exp (c * Real.log u) * (n : ℝ) ^ (-c) := by
      rw [Real.rpow_def_of_pos hn', ← Real.exp_add]
      congr 1
      unfold Ln; ring
    have h3 : (n : ℝ) ^ ε * (n : ℝ) ^ (-c) = ((n : ℝ) ^ (1 + ε))⁻¹ := by
      rw [← Real.rpow_add hn', ← Real.rpow_neg hn'.le]
      congr 1
      rw [hc]; ring
    rw [h2]
    calc Λ n * (Real.exp (c * Real.log u) * (n : ℝ) ^ (-c))
        ≤ ((n : ℝ) ^ ε / ε) * (Real.exp (c * Real.log u) * (n : ℝ) ^ (-c)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = Real.exp (c * Real.log u) / ε * ((n : ℝ) ^ ε * (n : ℝ) ^ (-c)) := by ring
      _ = _ := by rw [h3]

lemma summable_A (u c ε : ℝ) (hε : 0 < ε) (hc : c = 1 + 2 * ε) :
    Summable (fun n : ℕ => Λ n * Real.exp (c * Ln u n)) :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg vonMangoldt_nonneg (Real.exp_pos _).le)
    (vonMangoldt_mul_exp_le u c ε hε hc)
    ((Real.summable_nat_rpow_inv.mpr (by linarith)).mul_left _)

lemma tsum_A_le (u c ε : ℝ) (hε : 0 < ε) (hc : c = 1 + 2 * ε) :
    ∑' n : ℕ, Λ n * Real.exp (c * Ln u n) ≤ Real.exp (c * Real.log u) / ε * (1 + 1 / ε) := by
  have hs : Summable (fun n : ℕ => ((n : ℝ) ^ (1 + ε))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  calc ∑' n : ℕ, Λ n * Real.exp (c * Ln u n)
      ≤ ∑' n : ℕ, Real.exp (c * Real.log u) / ε * ((n : ℝ) ^ (1 + ε))⁻¹ :=
        Summable.tsum_le_tsum (vonMangoldt_mul_exp_le u c ε hε hc) (summable_A u c ε hε hc)
          (hs.mul_left _)
    _ = Real.exp (c * Real.log u) / ε * ∑' n : ℕ, ((n : ℝ) ^ (1 + ε))⁻¹ := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (tsum_rpow_le ε hε) (by positivity)

/-! ### The Dirichlet series on the Perron line -/

lemma term_mul_eq (u : ℝ) (hu : 0 < u) (s : ℂ) (n : ℕ) :
    LSeries.term (fun n => (Λ n : ℂ)) s n * ((u : ℂ) ^ s / s) = (Λ n : ℂ) * kf (Ln u n) s := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn]
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    rw [Complex.cpow_def_of_ne_zero hnC, Complex.cpow_def_of_ne_zero huC, ← Complex.natCast_log,
      ← Complex.ofReal_log hu.le]
    unfold kf Ln
    have : s * ((Real.log u - Real.log n : ℝ) : ℂ)
        = (Real.log u : ℂ) * s - (Real.log n : ℂ) * s := by push_cast; ring
    rw [this, Complex.exp_sub]
    ring

lemma hasSum_integrand (u : ℝ) (hu : 0 < u) (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun n : ℕ => (Λ n : ℂ) * kf (Ln u n) s) (ZetaShared.perronIntegrand u s) := by
  have h1 : HasSum (LSeries.term (fun n => (Λ n : ℂ)) s) (LSeries (fun n => (Λ n : ℂ)) s) :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).LSeriesHasSum
  have h2 := h1.mul_right ((u : ℂ) ^ s / s)
  have h3 : LSeries (fun n => (Λ n : ℂ)) s * ((u : ℂ) ^ s / s)
      = ZetaShared.perronIntegrand u s := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
    unfold ZetaShared.perronIntegrand
    ring
  rw [h3] at h2
  have e : (fun n : ℕ => LSeries.term (fun n => (Λ n : ℂ)) s n * ((u : ℂ) ^ s / s))
      = fun n : ℕ => (Λ n : ℂ) * kf (Ln u n) s := funext (term_mul_eq u hu s)
  rw [e] at h2
  exact h2

/-- Termwise integration of the Dirichlet series along the Perron segment. -/
lemma hasSum_kint (u c T : ℝ) (hu : 0 < u) (hc : 1 < c)
    (hsumm : Summable (fun n : ℕ => Λ n * Real.exp (c * Ln u n))) :
    HasSum (fun n : ℕ => (Λ n : ℂ) * kint (Ln u n) c T)
      (∫ t in (-T)..T, ZetaShared.perronIntegrand u ((c : ℂ) + (t : ℂ) * I)) := by
  have hc0 : c ≠ 0 := by linarith
  have hb : ∀ (n : ℕ) (t : ℝ), ‖(Λ n : ℂ) * kf (Ln u n) ((c : ℂ) + (t : ℂ) * I)‖
      ≤ Λ n * Real.exp (c * Ln u n) := by
    intro n t
    rw [norm_mul, norm_kf, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
    have hre : ((c : ℂ) + (t : ℂ) * I).re = c := by simp
    rw [hre]
    have hle : 1 ≤ ‖(c : ℂ) + (t : ℂ) * I‖ := by
      have := Complex.abs_re_le_norm ((c : ℂ) + (t : ℂ) * I)
      rw [hre, abs_of_pos (by linarith)] at this
      linarith
    exact mul_le_mul_of_nonneg_left (div_le_self (Real.exp_pos _).le hle) vonMangoldt_nonneg
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := -T) (b := T)
    (F := fun (n : ℕ) (t : ℝ) => (Λ n : ℂ) * kf (Ln u n) ((c : ℂ) + (t : ℂ) * I))
    (f := fun t : ℝ => ZetaShared.perronIntegrand u ((c : ℂ) + (t : ℂ) * I))
    (fun (n : ℕ) (_ : ℝ) => Λ n * Real.exp (c * Ln u n))
    (fun n => (continuous_const.mul (cont_kf_vert _ c hc0)).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun t _ => hb n t)
    (Filter.Eventually.of_forall fun t _ => hsumm)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ => hasSum_integrand u hu _ (by simpa using hc))
  have e : (fun n : ℕ => ∫ t in (-T)..T, (Λ n : ℂ) * kf (Ln u n) ((c : ℂ) + (t : ℂ) * I))
      = fun n : ℕ => (Λ n : ℂ) * kint (Ln u n) c T := by
    funext n
    rw [intervalIntegral.integral_const_mul]
    rfl
  rw [e] at key
  exact key

end ZetaPerron
