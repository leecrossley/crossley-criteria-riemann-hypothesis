import IndependentLandau.Defs
import IndependentLandau.Elementary

/-! Laplace moments `Bc g k p = ∫ g(u) e^{-pu} u^k / k! du` and the window inequality. -/

open Complex MeasureTheory Set Filter Topology
open scoped Nat

noncomputable section

namespace IndependentLandau

/-- The `k`-th Laplace moment of `g` at `p`. -/
def Bc (g : ℝ → ℝ) (k : ℕ) (p : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-p * u) * ((u : ℂ) ^ k / (k ! : ℂ))

theorem kernel_integral {b : ℝ} (hb : 0 < b) (k : ℕ) :
    ∫ u in Ioi (0 : ℝ), u ^ k * Real.exp (-(b * u)) = (k ! : ℝ) / b ^ (k + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (by positivity) hb
  rw [Real.Gamma_nat_eq_factorial] at h
  simp only [add_sub_cancel_right, Real.rpow_natCast] at h
  rw [h]
  have e : ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [e, Real.rpow_natCast, one_div, inv_pow, div_eq_inv_mul]

theorem kernel_integrable {b : ℝ} (hb : 0 < b) (k : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-(b * u))) (Ioi 0) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [kernel_integral hb k]
  positivity

/-- Core window inequality with all parameters explicit. -/
theorem window_core {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C)
    (hgC : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2 * u))
    {σ θ : ℝ} (hσ : 2 < σ) (hA : 1 ≤ σ - θ) {U B : ℝ} (hU : 0 < U)
    {R : ℝ → ℝ} (hRi : IntegrableOn (fun u => R u * Real.exp (-θ * u)) (Icc U B))
    (hR : ∀ u ∈ Icc U B, 0 ≤ R u ∧ g u ≤ R u) {E : ℝ}
    (hE : ∫ u in Icc U B, R u * Real.exp (-θ * u) ≤ E)
    (k : ℕ) {t t' : ℝ} (ht : 0 < t) (ht' : 0 < t') (ht'σ : t' < σ - 2)
    (hL : Real.exp (t * U) * (σ - θ) ^ k ≤ (σ - 2 + t) ^ (k + 1))
    (hH : Real.exp (-t' * B) * (σ - θ) ^ k ≤ (σ - 2 - t') ^ (k + 1))
    {p : ℂ} (hp : p.re = σ) :
    ‖Bc g k p‖ + (Bc g k (σ : ℂ)).re ≤ (2 * E + 4 * C) / (σ - θ) ^ k := by
  have hA0 : 0 < σ - θ := by linarith
  have hk0 : (0 : ℝ) < (k ! : ℝ) := by positivity
  have ha : 0 < σ - 2 := by linarith
  have hat : 0 < σ - 2 + t := by linarith
  have hat' : 0 < σ - 2 - t' := by linarith
  set Kf : ℝ → ℝ := fun u => Real.exp (-σ * u) * (u ^ k / (k ! : ℝ)) with hKf
  have hKf0 : ∀ u : ℝ, 0 < u → 0 ≤ Kf u := fun u hu => by
    have : 0 ≤ u ^ k := pow_nonneg hu.le k
    positivity
  -- the Gamma-type majorant of `|g| * Kf`
  have hmaj : ∀ u : ℝ, 0 < u →
      |g u| * Kf u ≤ C / (k ! : ℝ) * (u ^ k * Real.exp (-((σ - 2) * u))) := by
    intro u hu
    have h1 := hgC u hu.le
    have h2 : Real.exp (2 * u) * Real.exp (-σ * u) = Real.exp (-((σ - 2) * u)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc |g u| * Kf u ≤ (C * Real.exp (2 * u)) * Kf u :=
          mul_le_mul_of_nonneg_right h1 (hKf0 u hu)
      _ = C / (k ! : ℝ) * (u ^ k * (Real.exp (2 * u) * Real.exp (-σ * u))) := by
          simp only [hKf]; field_simp
      _ = C / (k ! : ℝ) * (u ^ k * Real.exp (-((σ - 2) * u))) := by rw [h2]
  have hmeasK : Measurable Kf := by
    simp only [hKf]; fun_prop
  have hint_abs : IntegrableOn (fun u => |g u| * Kf u) (Ioi 0) := by
    have hm : Measurable fun u => |g u| * Kf u :=
      (continuous_abs.measurable.comp hg).mul hmeasK
    refine Integrable.mono' ((kernel_integrable ha k).const_mul (C / (k ! : ℝ)))
      hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (hKf0 u hu))]
    exact hmaj u hu
  have hint_g : IntegrableOn (fun u => g u * Kf u) (Ioi 0) := by
    refine Integrable.mono hint_abs (hg.mul hmeasK).aestronglyMeasurable ?_
    filter_upwards with u
    simp
  -- step 1: norm bound
  have h1 : ‖Bc g k p‖ ≤ ∫ u in Ioi (0 : ℝ), |g u| * Kf u := by
    calc ‖Bc g k p‖
        ≤ ∫ u in Ioi (0 : ℝ), ‖(g u : ℂ) * cexp (-p * u) * ((u : ℂ) ^ k / (k ! : ℂ))‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ u in Ioi (0 : ℝ), |g u| * Kf u := by
          refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
          have hu0 : (0 : ℝ) < u := hu
          have e1 : ‖cexp (-p * u)‖ = Real.exp (-σ * u) := by
            rw [Complex.norm_exp]; congr 1; simp [hp]
          have e2 : ‖((u : ℂ) ^ k / (k ! : ℂ))‖ = u ^ k / (k ! : ℝ) := by
            rw [norm_div, norm_pow, Complex.norm_real, Complex.norm_natCast,
              Real.norm_of_nonneg hu0.le]
          simp only [hKf]
          rw [norm_mul, norm_mul, Complex.norm_real, e1, e2, mul_assoc, Real.norm_eq_abs]
  -- step 2: the real moment
  have h2 : (Bc g k (σ : ℂ)).re = ∫ u in Ioi (0 : ℝ), g u * Kf u := by
    have : ((∫ u in Ioi (0 : ℝ), g u * Kf u : ℝ) : ℂ) = Bc g k (σ : ℂ) := by
      refine integral_ofReal.symm.trans (setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_)
      have he : ((Real.exp (-σ * u) : ℝ) : ℂ) = cexp (-(σ : ℂ) * u) := by
        rw [Complex.ofReal_exp]; congr 1; push_cast; ring
      have hc : ((g u * Kf u : ℝ) : ℂ) =
          (g u : ℂ) * ((Real.exp (-σ * u) : ℝ) : ℂ) * ((u : ℂ) ^ k / (k ! : ℂ)) := by
        simp only [hKf]; push_cast; ring
      exact hc.trans (by rw [he])
    rw [← this, Complex.ofReal_re]
  have hsum : ‖Bc g k p‖ + (Bc g k (σ : ℂ)).re ≤
      ∫ u in Ioi (0 : ℝ), (|g u| + g u) * Kf u := by
    rw [h2]
    have h3 := integral_add hint_abs hint_g
    have h4 : (∫ u in Ioi (0 : ℝ), (|g u| + g u) * Kf u) =
        ∫ u in Ioi (0 : ℝ), (|g u| * Kf u + g u * Kf u) := by
      congr 1; funext u; ring
    rw [h4, h3]
    linarith
  -- the pointwise majorant
  set c2 : ℝ := 2 * C * Real.exp (t * U) / (k ! : ℝ) with hc2
  set c3 : ℝ := 2 * C * Real.exp (-t' * B) / (k ! : ℝ) with hc3
  have hc2n : 0 ≤ c2 := by positivity
  have hc3n : 0 ≤ c3 := by positivity
  set G : ℝ → ℝ := fun u =>
    2 / (σ - θ) ^ k * (Icc U B).indicator (fun u => R u * Real.exp (-θ * u)) u +
      c2 * (u ^ k * Real.exp (-((σ - 2 + t) * u))) +
      c3 * (u ^ k * Real.exp (-((σ - 2 - t') * u))) with hG
  have hGint : IntegrableOn G (Ioi 0) := by
    have i1 : IntegrableOn
        (fun u => 2 / (σ - θ) ^ k * (Icc U B).indicator (fun u => R u * Real.exp (-θ * u)) u)
        (Ioi 0) :=
      (((integrable_indicator_iff measurableSet_Icc).2 hRi).integrableOn).const_mul _
    have i2 := (kernel_integrable hat k).const_mul c2
    have i3 := (kernel_integrable hat' k).const_mul c3
    exact (i1.add i2).add i3
  have hpt : ∀ u : ℝ, 0 < u → (|g u| + g u) * Kf u ≤ G u := by
    intro u hu
    have hK := hKf0 u hu
    have huk : 0 ≤ u ^ k := pow_nonneg hu.le k
    have t2 : 0 ≤ c2 * (u ^ k * Real.exp (-((σ - 2 + t) * u))) := by positivity
    have t3 : 0 ≤ c3 * (u ^ k * Real.exp (-((σ - 2 - t') * u))) := by positivity
    simp only [hG]
    by_cases hW : u ∈ Icc U B
    · rw [Set.indicator_of_mem hW]
      obtain ⟨hR0, hgR⟩ := hR u hW
      have hgg : |g u| + g u ≤ 2 * R u := by
        rcases abs_cases (g u) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
      have hKle : Kf u ≤ Real.exp (-θ * u) / (σ - θ) ^ k := by
        have h5 := Real.pow_div_factorial_le_exp (x := (σ - θ) * u) (by positivity) k
        have h6 : Real.exp (-σ * u) = Real.exp (-θ * u) * Real.exp (-((σ - θ) * u)) := by
          rw [← Real.exp_add]; congr 1; ring
        have h7 : u ^ k / (k ! : ℝ) ≤ Real.exp ((σ - θ) * u) / (σ - θ) ^ k := by
          rw [le_div_iff₀ (pow_pos hA0 k)]
          calc u ^ k / (k ! : ℝ) * (σ - θ) ^ k = ((σ - θ) * u) ^ k / (k ! : ℝ) := by
                rw [mul_pow]; ring
            _ ≤ Real.exp ((σ - θ) * u) := h5
        simp only [hKf]
        rw [h6]
        calc Real.exp (-θ * u) * Real.exp (-((σ - θ) * u)) * (u ^ k / (k ! : ℝ))
            ≤ Real.exp (-θ * u) * Real.exp (-((σ - θ) * u)) *
                (Real.exp ((σ - θ) * u) / (σ - θ) ^ k) :=
              mul_le_mul_of_nonneg_left h7 (by positivity)
          _ = Real.exp (-θ * u) / (σ - θ) ^ k *
                (Real.exp (-((σ - θ) * u)) * Real.exp ((σ - θ) * u)) := by ring
          _ = Real.exp (-θ * u) / (σ - θ) ^ k := by
              rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      have hgg0 : 0 ≤ |g u| + g u := by linarith [neg_abs_le (g u)]
      have hmain : (|g u| + g u) * Kf u ≤
          2 / (σ - θ) ^ k * (R u * Real.exp (-θ * u)) := by
        calc (|g u| + g u) * Kf u ≤ (2 * R u) * (Real.exp (-θ * u) / (σ - θ) ^ k) :=
              mul_le_mul hgg hKle hK (by linarith)
          _ = 2 / (σ - θ) ^ k * (R u * Real.exp (-θ * u)) := by ring
      linarith
    · rw [Set.indicator_of_notMem hW, mul_zero, zero_add]
      have hgg : (|g u| + g u) * Kf u ≤ 2 * (|g u| * Kf u) := by
        have : |g u| + g u ≤ 2 * |g u| := by linarith [le_abs_self (g u)]
        calc (|g u| + g u) * Kf u ≤ (2 * |g u|) * Kf u := mul_le_mul_of_nonneg_right this hK
          _ = 2 * (|g u| * Kf u) := by ring
      have hm := hmaj u hu
      have hCk : 0 ≤ 2 * C / (k ! : ℝ) * u ^ k := by positivity
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hW
      rcases hW with hlt | hgt
      · have hexp : Real.exp (-((σ - 2) * u)) ≤
            Real.exp (-((σ - 2 + t) * u)) * Real.exp (t * U) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.2
          nlinarith
        have : 2 * (C / (k ! : ℝ) * (u ^ k * Real.exp (-((σ - 2) * u)))) ≤
            c2 * (u ^ k * Real.exp (-((σ - 2 + t) * u))) := by
          calc 2 * (C / (k ! : ℝ) * (u ^ k * Real.exp (-((σ - 2) * u))))
              = 2 * C / (k ! : ℝ) * u ^ k * Real.exp (-((σ - 2) * u)) := by ring
            _ ≤ 2 * C / (k ! : ℝ) * u ^ k *
                  (Real.exp (-((σ - 2 + t) * u)) * Real.exp (t * U)) :=
                mul_le_mul_of_nonneg_left hexp hCk
            _ = c2 * (u ^ k * Real.exp (-((σ - 2 + t) * u))) := by rw [hc2]; ring
        linarith
      · have hexp : Real.exp (-((σ - 2) * u)) ≤
            Real.exp (-((σ - 2 - t') * u)) * Real.exp (-t' * B) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.2
          nlinarith
        have : 2 * (C / (k ! : ℝ) * (u ^ k * Real.exp (-((σ - 2) * u)))) ≤
            c3 * (u ^ k * Real.exp (-((σ - 2 - t') * u))) := by
          calc 2 * (C / (k ! : ℝ) * (u ^ k * Real.exp (-((σ - 2) * u))))
              = 2 * C / (k ! : ℝ) * u ^ k * Real.exp (-((σ - 2) * u)) := by ring
            _ ≤ 2 * C / (k ! : ℝ) * u ^ k *
                  (Real.exp (-((σ - 2 - t') * u)) * Real.exp (-t' * B)) :=
                mul_le_mul_of_nonneg_left hexp hCk
            _ = c3 * (u ^ k * Real.exp (-((σ - 2 - t') * u))) := by rw [hc3]; ring
        linarith
  have hmono : (∫ u in Ioi (0 : ℝ), (|g u| + g u) * Kf u) ≤ ∫ u in Ioi (0 : ℝ), G u := by
    refine integral_mono_of_nonneg ?_ hGint ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : (0 : ℝ) < u := hu
      exact mul_nonneg (by linarith [neg_abs_le (g u)]) (hKf0 u hu0)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact hpt u hu
  -- evaluate the majorant integral
  have hW0 : Icc U B ⊆ Ioi (0 : ℝ) := fun u hu => lt_of_lt_of_le hU hu.1
  have hGval : (∫ u in Ioi (0 : ℝ), G u) =
      2 / (σ - θ) ^ k * (∫ u in Icc U B, R u * Real.exp (-θ * u)) +
        c2 * ((k ! : ℝ) / (σ - 2 + t) ^ (k + 1)) +
        c3 * ((k ! : ℝ) / (σ - 2 - t') ^ (k + 1)) := by
    have i1 : IntegrableOn
        (fun u => 2 / (σ - θ) ^ k * (Icc U B).indicator (fun u => R u * Real.exp (-θ * u)) u)
        (Ioi 0) :=
      (((integrable_indicator_iff measurableSet_Icc).2 hRi).integrableOn).const_mul _
    have i2 := (kernel_integrable hat k).const_mul c2
    have i3 := (kernel_integrable hat' k).const_mul c3
    have i12 : IntegrableOn (fun u =>
        2 / (σ - θ) ^ k * (Icc U B).indicator (fun u => R u * Real.exp (-θ * u)) u +
          c2 * (u ^ k * Real.exp (-((σ - 2 + t) * u)))) (Ioi 0) := i1.add i2
    simp only [hG]
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul,
      integral_const_mul, integral_const_mul, kernel_integral hat k, kernel_integral hat' k,
      setIntegral_indicator measurableSet_Icc, Set.inter_eq_right.2 hW0]
  have hAk : 0 < (σ - θ) ^ k := pow_pos hA0 k
  have hb2 : c2 * ((k ! : ℝ) / (σ - 2 + t) ^ (k + 1)) ≤ 2 * C / (σ - θ) ^ k := by
    have e : c2 * ((k ! : ℝ) / (σ - 2 + t) ^ (k + 1)) =
        2 * C * (Real.exp (t * U) / (σ - 2 + t) ^ (k + 1)) := by
      rw [hc2]; field_simp
    have h : Real.exp (t * U) / (σ - 2 + t) ^ (k + 1) ≤ 1 / (σ - θ) ^ k := by
      rw [div_le_div_iff₀ (pow_pos hat _) hAk]; linarith
    rw [e]
    calc 2 * C * (Real.exp (t * U) / (σ - 2 + t) ^ (k + 1)) ≤ 2 * C * (1 / (σ - θ) ^ k) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 2 * C / (σ - θ) ^ k := by ring
  have hb3 : c3 * ((k ! : ℝ) / (σ - 2 - t') ^ (k + 1)) ≤ 2 * C / (σ - θ) ^ k := by
    have e : c3 * ((k ! : ℝ) / (σ - 2 - t') ^ (k + 1)) =
        2 * C * (Real.exp (-t' * B) / (σ - 2 - t') ^ (k + 1)) := by
      rw [hc3]; field_simp
    have h : Real.exp (-t' * B) / (σ - 2 - t') ^ (k + 1) ≤ 1 / (σ - θ) ^ k := by
      rw [div_le_div_iff₀ (pow_pos hat' _) hAk]; linarith
    rw [e]
    calc 2 * C * (Real.exp (-t' * B) / (σ - 2 - t') ^ (k + 1)) ≤ 2 * C * (1 / (σ - θ) ^ k) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 2 * C / (σ - θ) ^ k := by ring
  have hb1 : 2 / (σ - θ) ^ k * (∫ u in Icc U B, R u * Real.exp (-θ * u)) ≤
      2 * E / (σ - θ) ^ k := by
    calc 2 / (σ - θ) ^ k * (∫ u in Icc U B, R u * Real.exp (-θ * u))
        ≤ 2 / (σ - θ) ^ k * E := mul_le_mul_of_nonneg_left hE (by positivity)
      _ = 2 * E / (σ - θ) ^ k := by ring
  calc ‖Bc g k p‖ + (Bc g k (σ : ℂ)).re ≤ ∫ u in Ioi (0 : ℝ), G u := hsum.trans hmono
    _ ≤ 2 * E / (σ - θ) ^ k + 2 * C / (σ - θ) ^ k + 2 * C / (σ - θ) ^ k := by
        rw [hGval]; linarith
    _ = (2 * E + 4 * C) / (σ - θ) ^ k := by ring

/-- Step B: the window inequality for the Laplace moments on a fixed vertical line. -/
theorem window_bound {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z)
    {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (hW : WindowHypU g θ δ) :
    ∃ σ : ℝ, 2 < σ ∧ ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ η : ℝ, 0 < η → ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧
      ∃ k : ℕ, U ≤ k ∧ ∀ p : ℂ, p.re = σ →
        ‖Bc g k p‖ + (Bc g k (σ : ℂ)).re ≤ C₁ * Real.exp (η * U) / (σ - θ) ^ k := by
  obtain ⟨σ, hσ, hpar⟩ := params hθ hθ1 hδ
  obtain ⟨C, hgC⟩ := hP.growth
  have hC : 0 ≤ C := by
    have := hgC 0 le_rfl
    simp only [mul_zero, Real.exp_zero, mul_one] at this
    exact (abs_nonneg _).trans this
  refine ⟨σ, hσ, 2 + 4 * C, by positivity, fun η hη U₀ => ?_⟩
  obtain ⟨U, hU, R, hRi, hR, hE⟩ := hW η hη (max U₀ 1)
  have hU1 : 1 ≤ U := (le_max_right _ _).trans hU
  have hU0 : 0 < U := by linarith
  obtain ⟨k, hk, t, t', ht, ht', ht'σ, hL, hH⟩ := hpar U hU1
  refine ⟨U, (le_max_left _ _).trans hU, k, hk, fun p hp => ?_⟩
  have hcore := window_core hP.meas hC hgC hσ (by linarith) hU0 hRi hR hE k ht ht' ht'σ hL hH hp
  refine hcore.trans ?_
  have hA0 : 0 < σ - θ := by linarith
  have hexp : 1 ≤ Real.exp (η * U) := Real.one_le_exp (by positivity)
  rw [div_le_div_iff_of_pos_right (pow_pos hA0 k)]
  nlinarith

end IndependentLandau
