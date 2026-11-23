import Mathlib
import ZetaRegion.Local
import ZetaRegion.ZetaBounds
import ZetaRegion.ThreeFourOne

/-! The classical zero-free region `re s ≥ 1 - c / log (|im s| + 2)` for `ζ₁ s = (s - 1) ζ(s)`.

For `|im s| ≥ 1` this is de la Vallée-Poussin's argument: the 3-4-1 inequality at
`σ₀ = 1 + a / log (|t| + 2)`, with the local lemma of `ZetaRegion.Local` applied to `ζ₁` on discs
of radius `1/2` about `σ₀ + it` and `σ₀ + 2it`. For `|im s| ≤ 1` it is compactness. -/

open Complex Metric Set

noncomputable section
namespace ZetaRegion

lemma one_le_log {t : ℝ} (ht : 1 ≤ |t|) : 1 ≤ Real.log (|t| + 2) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have := Real.exp_one_lt_d9
  linarith

lemma bound_le_exp {a L x : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hx : 2 ≤ x) (hL : L = Real.log x)
    (hL1 : 1 ≤ L) :
    8 * x ^ 2 ≤ Real.exp ((3 + Real.log (24 / a)) * L) * (a / (3 * L)) := by
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < L := by linarith
  have h24 : 0 < 24 / a := by positivity
  have h1 : 0 ≤ Real.log (24 / a) := Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith)
  have h2 : Real.log L ≤ L - 1 := Real.log_le_sub_one_of_pos hL0
  have h3 : 2 * L + Real.log L + Real.log (24 / a) ≤ (3 + Real.log (24 / a)) * L := by
    nlinarith
  have h4 : Real.exp (2 * L + Real.log L + Real.log (24 / a)) = x ^ 2 * L * (24 / a) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log hL0, Real.exp_log h24, hL, two_mul,
      Real.exp_add, Real.exp_log hx0]
    ring
  calc 8 * x ^ 2 = x ^ 2 * L * (24 / a) * (a / (3 * L)) := by
        field_simp
        ring
    _ ≤ Real.exp ((3 + Real.log (24 / a)) * L) * (a / (3 * L)) := by
        gcongr
        rw [← h4]
        exact Real.exp_le_exp.mpr h3

/-- The hypothesis `‖ζ₁ z‖ ≤ e^M ‖ζ₁ c‖` of the local lemmas, with `M = (3 + log (24/a)) L`,
on discs of radius at most `1/2` about points `c` with `1 + a / L ≤ re c ≤ 2`. -/
lemma ball_bound {a t r : ℝ} {c : ℂ} (ha : 0 < a) (ha1 : a ≤ 1) (ht : 1 ≤ |t|)
    (hσ1 : 1 + a / Real.log (|t| + 2) ≤ c.re) (hσ2 : c.re ≤ 2) (hτ1 : 1 ≤ |c.im|)
    (hτ2 : |c.im| ≤ 2 * |t|) (hr : r ≤ 1 / 2) (z : ℂ) (hz : z ∈ ball c r) :
    ‖riemannZeta₁ z‖ ≤ Real.exp ((3 + Real.log (24 / a)) * Real.log (|t| + 2)) *
      ‖riemannZeta₁ c‖ := by
  have hL1 : 1 ≤ Real.log (|t| + 2) := one_le_log ht
  have hL0 : 0 < Real.log (|t| + 2) := by linarith
  have hdist : ‖z - c‖ < 1 / 2 := by
    rw [mem_ball, dist_eq_norm] at hz
    linarith
  have hzre : |z.re - c.re| < 1 / 2 := by
    have := Complex.abs_re_le_norm (z - c)
    rw [sub_re] at this
    linarith
  have hzim : |z.im - c.im| < 1 / 2 := by
    have := Complex.abs_im_le_norm (z - c)
    rw [sub_im] at this
    linarith
  have haL : 0 < a / Real.log (|t| + 2) := by positivity
  have hzim' : |z.im| ≤ |c.im| + 1 / 2 := by
    have := abs_sub_abs_le_abs_sub z.im c.im
    linarith
  rw [abs_lt] at hzre
  have h1 : ‖riemannZeta₁ z‖ ≤ 8 * (|t| + 2) ^ 2 :=
    norm_zeta₁_le_of_strip (by linarith) (by linarith) (by linarith)
  have h2 : (c.re - 1) / 3 ≤ ‖riemannZeta₁ c‖ := le_norm_zeta₁ (by linarith) hσ2 hτ1
  have h3 := bound_le_exp ha ha1 (x := |t| + 2) (by linarith [abs_nonneg t]) rfl hL1
  calc ‖riemannZeta₁ z‖ ≤ 8 * (|t| + 2) ^ 2 := h1
    _ ≤ Real.exp ((3 + Real.log (24 / a)) * Real.log (|t| + 2)) *
          (a / (3 * Real.log (|t| + 2))) := h3
    _ ≤ Real.exp ((3 + Real.log (24 / a)) * Real.log (|t| + 2)) * ‖riemannZeta₁ c‖ := by
        gcongr
        calc a / (3 * Real.log (|t| + 2)) = a / Real.log (|t| + 2) / 3 := by
              field_simp
          _ ≤ (c.re - 1) / 3 := by linarith
          _ ≤ _ := h2

lemma re_one_div_sub_one_le {c : ℂ} (h : 1 ≤ |c.im|) : (1 / (c - 1)).re ≤ 1 := by
  have h1 : 1 ≤ ‖c - 1‖ := by
    have := Complex.abs_im_le_norm (c - 1)
    simp only [sub_im, one_im, sub_zero] at this
    linarith
  calc (1 / (c - 1)).re ≤ ‖1 / (c - 1)‖ := Complex.re_le_norm _
    _ = 1 / ‖c - 1‖ := by rw [norm_div, norm_one]
    _ ≤ 1 := by
        rw [div_le_one (by linarith)]
        exact h1

/-- The inequality forced by a zero `β + it` close to the line `re s = 1`. -/
lemma key_ineq {E a t β : ℝ}
    (hE : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      -(deriv riemannZeta σ / riemannZeta σ).re ≤ 1 / (σ - 1) + E)
    (ha : 0 < a) (ha1 : a ≤ 1) (ht : 1 ≤ |t|)
    (hβ : riemannZeta₁ ((β : ℂ) + t * I) = 0)
    (hβ' : 1 + a / Real.log (|t| + 2) - 1 / 8 ≤ β) :
    4 / (1 + a / Real.log (|t| + 2) - β) ≤
      3 * (Real.log (|t| + 2) / a) + 3 * E +
        960 * ((3 + Real.log (24 / a)) * Real.log (|t| + 2)) + 5 := by
  have hL1 : 1 ≤ Real.log (|t| + 2) := one_le_log ht
  have hL0 : 0 < Real.log (|t| + 2) := by linarith
  set L := Real.log (|t| + 2) with hL
  set M := (3 + Real.log (24 / a)) * L with hM
  set σ₀ := 1 + a / L with hσ₀
  have haL : 0 < a / L := by positivity
  have haL1 : a / L ≤ 1 := (div_le_self ha.le hL1).trans ha1
  have hσ1 : 1 < σ₀ := by linarith
  have hσ2 : σ₀ ≤ 2 := by linarith
  have hβ1 : β < 1 := by
    by_contra h
    exact zeta₁_ne_zero_of_one_le_re (s := (β : ℂ) + t * I) (by simpa using h) hβ
  have ht0 : (0 : ℝ) ≤ |t| := abs_nonneg t
  -- the two centres
  have hre1 : ((σ₀ : ℂ) + t * I).re = σ₀ := by simp
  have him1 : ((σ₀ : ℂ) + t * I).im = t := by simp
  have hre2 : ((σ₀ : ℂ) + 2 * t * I).re = σ₀ := by simp
  have him2 : ((σ₀ : ℂ) + 2 * t * I).im = 2 * t := by simp
  have hd : DifferentiableOn ℂ riemannZeta₁ (ball ((σ₀ : ℂ) + t * I) (1 / 2)) :=
    differentiable_riemannZeta₁.differentiableOn
  have hd2 : DifferentiableOn ℂ riemannZeta₁ (ball ((σ₀ : ℂ) + 2 * t * I) (1 / 2)) :=
    differentiable_riemannZeta₁.differentiableOn
  have hc1 : riemannZeta₁ ((σ₀ : ℂ) + t * I) ≠ 0 :=
    zeta₁_ne_zero_of_one_le_re (by rw [hre1]; linarith)
  have hc2 : riemannZeta₁ ((σ₀ : ℂ) + 2 * t * I) ≠ 0 :=
    zeta₁_ne_zero_of_one_le_re (by rw [hre2]; linarith)
  have hb1 := ball_bound (r := 1 / 2) (c := (σ₀ : ℂ) + t * I) ha ha1 ht (by rw [hre1])
    (by rw [hre1]; exact hσ2) (by rw [him1]; exact ht) (by rw [him1]; linarith) le_rfl
  have hb2 := ball_bound (r := 1 / 2) (c := (σ₀ : ℂ) + 2 * t * I) ha ha1 ht (by rw [hre2])
    (by rw [hre2]; exact hσ2) (by rw [him2, abs_mul, abs_two]; linarith)
    (by rw [him2, abs_mul, abs_two]) le_rfl
  have hz1 : ∀ u ∈ closedBall ((σ₀ : ℂ) + t * I) (1 / 2 / 4), riemannZeta₁ u = 0 →
      u.re ≤ ((σ₀ : ℂ) + t * I).re := by
    intro u _ hu
    by_contra h
    rw [hre1] at h
    exact zeta₁_ne_zero_of_one_le_re (by linarith) hu
  have hz2 : ∀ u ∈ closedBall ((σ₀ : ℂ) + 2 * t * I) (1 / 2 / 4), riemannZeta₁ u = 0 →
      u.re ≤ ((σ₀ : ℂ) + 2 * t * I).re := by
    intro u _ hu
    by_contra h
    rw [hre2] at h
    exact zeta₁_ne_zero_of_one_le_re (by linarith) hu
  have hsub : ((σ₀ : ℂ) + t * I) - ((β : ℂ) + t * I) = ((σ₀ - β : ℝ) : ℂ) := by
    push_cast
    ring
  have hρ : (β : ℂ) + t * I ∈ closedBall ((σ₀ : ℂ) + t * I) (1 / 2 / 4) := by
    rw [mem_closedBall, dist_comm, dist_eq_norm, hsub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    linarith
  have hA := re_logDeriv_ge_of_zero (by norm_num : (0 : ℝ) < 1 / 2) hd hc1 hb1 hz1 hρ hβ
  have hB := re_logDeriv_ge (by norm_num : (0 : ℝ) < 1 / 2) hd2 hc2 hb2 hz2
  rw [hsub, ← ofReal_one, ← ofReal_div, ofReal_re] at hA
  -- pass from ζ₁ to ζ
  have hne1 : (σ₀ : ℂ) + t * I ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    rw [him1] at this
    simp only [one_im] at this
    rw [this] at ht
    norm_num at ht
  have hne2 : (σ₀ : ℂ) + 2 * t * I ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    rw [him2] at this
    simp only [one_im] at this
    have : t = 0 := by linarith
    rw [this] at ht
    norm_num at ht
  have hζ1 : riemannZeta ((σ₀ : ℂ) + t * I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [hre1]; linarith)
  have hζ2 : riemannZeta ((σ₀ : ℂ) + 2 * t * I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [hre2]; linarith)
  have h341 := three_four_one hσ1 t
  rw [logDeriv_zeta_eq hne1 hζ1, logDeriv_zeta_eq hne2 hζ2] at h341
  simp only [neg_re, sub_re] at h341
  have hr1 := re_one_div_sub_one_le (c := (σ₀ : ℂ) + t * I) (by rw [him1]; exact ht)
  have hr2 := re_one_div_sub_one_le (c := (σ₀ : ℂ) + 2 * t * I)
    (by rw [him2, abs_mul, abs_two]; linarith)
  have h0 := hE σ₀ hσ1 hσ2
  have e0 : 1 / (σ₀ - 1) = L / a := by
    rw [hσ₀, add_sub_cancel_left, one_div_div]
  rw [e0] at h0
  have e1 : (4 : ℝ) / (σ₀ - β) = 4 * (1 / (σ₀ - β)) := by ring
  have e2 : 96 * M / (1 / 2) = 192 * M := by ring
  rw [e2] at hA hB
  rw [e1]
  linarith

lemma exists_small_a (P : ℝ) (hP : 0 ≤ P) : ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 12 ∧
    a * (P + 960 * (3 + Real.log (24 / a))) ≤ 1 / 2 := by
  set D := 48 * P + 230400 with hD
  have hD0 : 0 < D := by positivity
  have hD1 : 230400 ≤ D := by linarith
  refine ⟨24 / D ^ 2, by positivity, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    nlinarith
  · have e : 24 / (24 / D ^ 2) = D ^ 2 := by
      field_simp
    have hlog : Real.log D ≤ D - 1 := Real.log_le_sub_one_of_pos hD0
    rw [e, Real.log_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    push_cast
    nlinarith

/-- **Zero-free region away from the real axis.** -/
theorem exists_zero_free_large : ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, 1 ≤ |s.im| →
    1 - c / Real.log (|s.im| + 2) ≤ s.re → riemannZeta₁ s ≠ 0 := by
  obtain ⟨E, hE0, hE⟩ := exists_logDeriv_real_bound
  obtain ⟨a, ha, ha12, haG⟩ := exists_small_a (3 * E + 5) (by positivity)
  refine ⟨a / 8, by positivity, fun s ht hs hzero => ?_⟩
  have hL1 : 1 ≤ Real.log (|s.im| + 2) := one_le_log ht
  have hL0 : 0 < Real.log (|s.im| + 2) := by linarith
  have hs_eq : (s.re : ℂ) + s.im * I = s := re_add_im s
  have h1 : a / Real.log (|s.im| + 2) ≤ a := div_le_self ha.le hL1
  have h2 : a / 8 / Real.log (|s.im| + 2) ≤ a / 8 := div_le_self (by positivity) hL1
  by_cases hfar : 1 + a / Real.log (|s.im| + 2) - 1 / 8 ≤ s.re
  · have key := key_ineq hE ha (by linarith) ht (by rw [hs_eq]; exact hzero) hfar
    have hβ1 : s.re < 1 := by
      by_contra h
      exact zeta₁_ne_zero_of_one_le_re (not_lt.mp h) hzero
    set L := Real.log (|s.im| + 2) with hL
    set d := 1 + a / L - s.re with hd
    have haL : 0 < a / L := by positivity
    have hd0 : 0 < d := by linarith
    have hlog0 : 0 ≤ Real.log (24 / a) := Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith)
    set G := 3 * E + 5 + 960 * (3 + Real.log (24 / a)) with hG
    have hG0 : 0 ≤ G := by positivity
    have h3 : 4 / d ≤ L * (3 / a + G) := by
      refine key.trans (le_of_eq_of_le ?_ ?_ (b := L * (3 / a) + (3 * E + 5) +
        960 * (3 + Real.log (24 / a)) * L))
      · ring
      · have : 3 * E + 5 ≤ L * (3 * E + 5) := le_mul_of_one_le_left (by positivity) hL1
        rw [hG]
        linarith
    have h4 : 4 ≤ d * (L * (3 / a + G)) := by
      rwa [div_le_iff₀' hd0] at h3
    have h5 : d ≤ a / L + a / 8 / L := by
      rw [hd]
      linarith
    have h6 : d * L ≤ 9 * a / 8 := by
      have e : (a / L + a / 8 / L) * L = 9 * a / 8 := by
        field_simp
        ring
      rw [← e]
      exact mul_le_mul_of_nonneg_right h5 hL0.le
    have h7 : a * (3 / a + G) = 3 + a * G := by
      field_simp
    have h8 : d * (L * (3 / a + G)) ≤ 9 * a / 8 * (3 / a + G) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right h6 (by positivity)
    have h9 : 9 * a / 8 * (3 / a + G) = 9 / 8 * (3 + a * G) := by
      rw [← h7]
      ring
    rw [h9] at h8
    linarith
  · push Not at hfar
    linarith

/-- **Zero-free region near the real axis**, by compactness. -/
theorem exists_zero_free_small : ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ, |s.im| ≤ 1 → 1 - δ ≤ s.re →
    riemannZeta₁ s ≠ 0 := by
  set K : Set ℂ := {s | 1 / 2 ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ 1 ∧ riemannZeta₁ s = 0} with hK
  have hKc : IsCompact K := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall 0 2) ?_ ?_
    · have h1 : IsClosed {s : ℂ | 1 / 2 ≤ s.re} := isClosed_le continuous_const continuous_re
      have h2 : IsClosed {s : ℂ | s.re ≤ 1} := isClosed_le continuous_re continuous_const
      have h3 : IsClosed {s : ℂ | |s.im| ≤ 1} :=
        isClosed_le (continuous_abs.comp continuous_im) continuous_const
      have h4 : IsClosed {s : ℂ | riemannZeta₁ s = 0} :=
        isClosed_eq differentiable_riemannZeta₁.continuous continuous_const
      exact h1.inter (h2.inter (h3.inter h4))
    · intro s hs
      rw [mem_closedBall_zero_iff]
      have hre : |s.re| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [hs.1, hs.2.1]
      calc ‖s‖ ≤ |s.re| + |s.im| := norm_le_abs_re_add_abs_im s
        _ ≤ 1 + 1 := add_le_add hre hs.2.2.1
        _ = 2 := by norm_num
  by_cases hne : K.Nonempty
  · obtain ⟨s₀, hs₀, hmax⟩ := hKc.exists_isMaxOn hne continuous_re.continuousOn
    have hlt : s₀.re < 1 := by
      rcases hs₀.2.1.lt_or_eq with h | h
      · exact h
      · exact absurd hs₀.2.2.2 (zeta₁_ne_zero_of_one_le_re h.ge)
    refine ⟨(1 - s₀.re) / 2, by linarith, fun s him hre hzero => ?_⟩
    have hs1 : s.re < 1 := by
      by_contra h
      exact zeta₁_ne_zero_of_one_le_re (not_lt.mp h) hzero
    have hsK : s ∈ K := ⟨by linarith [hs₀.1], hs1.le, him, hzero⟩
    have := isMaxOn_iff.mp hmax s hsK
    linarith
  · refine ⟨1 / 2, by norm_num, fun s him hre hzero => ?_⟩
    have hs1 : s.re < 1 := by
      by_contra h
      exact zeta₁_ne_zero_of_one_le_re (not_lt.mp h) hzero
    exact hne ⟨s, by linarith, hs1.le, him, hzero⟩

/-- **The zero-free region** for `ζ₁`. -/
theorem exists_zero_free : ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ,
    1 - c / Real.log (|s.im| + 2) ≤ s.re → riemannZeta₁ s ≠ 0 := by
  obtain ⟨c₁, hc₁, h₁⟩ := exists_zero_free_large
  obtain ⟨δ, hδ, h₂⟩ := exists_zero_free_small
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨min c₁ (δ * Real.log 2), lt_min hc₁ (by positivity), fun s hs => ?_⟩
  have hLpos : 0 < Real.log (|s.im| + 2) := Real.log_pos (by linarith [abs_nonneg s.im])
  rcases le_total 1 |s.im| with h | h
  · refine h₁ s h (le_trans ?_ hs)
    have : min c₁ (δ * Real.log 2) / Real.log (|s.im| + 2) ≤ c₁ / Real.log (|s.im| + 2) := by
      gcongr
      exact min_le_left _ _
    linarith
  · refine h₂ s h (le_trans ?_ hs)
    have h3 : Real.log 2 ≤ Real.log (|s.im| + 2) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
    have : min c₁ (δ * Real.log 2) / Real.log (|s.im| + 2) ≤ δ := by
      rw [div_le_iff₀ hLpos]
      calc min c₁ (δ * Real.log 2) ≤ δ * Real.log 2 := min_le_right _ _
        _ ≤ δ * Real.log (|s.im| + 2) := by gcongr
    linarith

end ZetaRegion

#print axioms ZetaRegion.exists_zero_free_large
#print axioms ZetaRegion.exists_zero_free
