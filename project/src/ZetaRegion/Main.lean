import Mathlib
import ZetaShared.Statements
import ZetaRegion.Region

/-! The classical zero-free region of the Riemann zeta function, with the bound
`ζ'/ζ = O(log² t)` inside it: `ZetaRegion.regionStatement : ZetaShared.RegionStatement`.

The logarithmic derivative is bounded by the zero-free local lemma
`ZetaRegion.norm_logDeriv_le_of_ne_zero` applied to `ζ₁ s = (s - 1) ζ(s)` on a disc of radius
`4c / log (|t| + 2)` inside the zero-free region, centred to the right of the line `re s = 1`. -/

open Complex Metric Set

noncomputable section
namespace ZetaRegion

lemma norm_one_div_sub_one_le {s : ℂ} (h : 1 ≤ |s.im|) : ‖1 / (s - 1)‖ ≤ 1 := by
  have h1 : 1 ≤ ‖s - 1‖ := by
    have := Complex.abs_im_le_norm (s - 1)
    simp only [sub_im, one_im, sub_zero] at this
    linarith
  rw [norm_div, norm_one, div_le_one (by linarith)]
  exact h1

/-- The bound for `ζ'/ζ` in a region `re s ≥ 1 - c / log (|im s| + 2)`, `|im s| ≥ 1`, `re s ≤ 2`,
given a zero-free region with constant `c₁ ≥ 6c` and `c ≤ 1/8`. -/
theorem norm_logDeriv_zeta_le {c₁ c : ℝ}
    (hzf : ∀ s : ℂ, 1 - c₁ / Real.log (|s.im| + 2) ≤ s.re → riemannZeta₁ s ≠ 0)
    (hc0 : 0 < c) (hc6 : c ≤ c₁ / 6) (hc8 : c ≤ 1 / 8) (s : ℂ)
    (hs : 1 - c / Real.log (|s.im| + 2) ≤ s.re) (hs2 : s.re ≤ 2) (ht : 1 ≤ |s.im|) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤
      (6 * (3 + Real.log (24 / c)) / c + 1) * Real.log (|s.im| + 2) ^ 2 := by
  have hlog0 : 0 ≤ Real.log (24 / c) := Real.log_nonneg (by rw [le_div_iff₀ hc0]; linarith)
  have hL1 : 1 ≤ Real.log (|s.im| + 2) := one_le_log ht
  set L := Real.log (|s.im| + 2) with hL
  have hL0 : 0 < L := by linarith
  have hcL : 0 < c / L := by positivity
  have hcL' : c / L ≤ c := div_le_self hc0.le hL1
  set σ₀ := max s.re (1 + c / L) with hσ₀
  set r := 4 * c / L with hr
  have hr4 : r = 4 * (c / L) := by rw [hr]; ring
  have hr0 : 0 < r := by positivity
  have hr12 : r ≤ 1 / 2 := by linarith
  have hre : ((σ₀ : ℂ) + s.im * I).re = σ₀ := by simp
  have him : ((σ₀ : ℂ) + s.im * I).im = s.im := by simp
  have hσ1 : 1 + c / L ≤ σ₀ := le_max_right _ _
  have hσ2 : σ₀ ≤ 2 := max_le hs2 (by linarith)
  have hσs : s.re ≤ σ₀ := le_max_left _ _
  have hσs' : σ₀ - s.re ≤ 2 * (c / L) := by
    rcases max_cases s.re (1 + c / L) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [hσ₀, h]
      linarith
    · rw [hσ₀, h]
      linarith
  have hsub : ((σ₀ : ℂ) + s.im * I) - s = ((σ₀ - s.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have hs_mem : s ∈ closedBall ((σ₀ : ℂ) + s.im * I) (r / 2) := by
    rw [mem_closedBall, dist_comm, dist_eq_norm, hsub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    linarith
  have hb := ball_bound (t := s.im) (r := r) (c := (σ₀ : ℂ) + s.im * I) hc0 (by linarith) ht
    (by rw [hre]; exact hσ1) (by rw [hre]; exact hσ2) (by rw [him]; exact ht)
    (by rw [him]; linarith [abs_nonneg s.im]) hr12
  have hne : ∀ z ∈ ball ((σ₀ : ℂ) + s.im * I) r, riemannZeta₁ z ≠ 0 := by
    intro z hz
    apply hzf
    rw [mem_ball, dist_eq_norm] at hz
    have hzre : |z.re - σ₀| < r := by
      have := Complex.abs_re_le_norm (z - ((σ₀ : ℂ) + s.im * I))
      rw [sub_re, hre] at this
      linarith
    have hzim : |z.im - s.im| < r := by
      have := Complex.abs_im_le_norm (z - ((σ₀ : ℂ) + s.im * I))
      rw [sub_im, him] at this
      linarith
    have hzim' : |z.im| ≤ |s.im| + 1 / 2 := by
      have := abs_sub_abs_le_abs_sub z.im s.im
      linarith
    have hlogz : Real.log (|z.im| + 2) ≤ 2 * L := by
      have h1 : |z.im| + 2 ≤ (|s.im| + 2) ^ 2 := by nlinarith [abs_nonneg s.im]
      calc Real.log (|z.im| + 2) ≤ Real.log ((|s.im| + 2) ^ 2) :=
            Real.log_le_log (by positivity) h1
        _ = 2 * L := by
            rw [Real.log_pow, hL]
            norm_num
    have hlogz0 : 0 < Real.log (|z.im| + 2) := Real.log_pos (by linarith [abs_nonneg z.im])
    have h3 : 3 * c / L ≤ c₁ / Real.log (|z.im| + 2) := by
      rw [div_le_div_iff₀ hL0 hlogz0]
      nlinarith [mul_le_mul_of_nonneg_left hlogz hc0.le, mul_le_mul_of_nonneg_right hc6 hL0.le]
    rw [abs_lt] at hzre
    have e : 3 * c / L = 3 * (c / L) := by ring
    linarith
  have hM := norm_logDeriv_le_of_ne_zero hr0 differentiable_riemannZeta₁.differentiableOn hne hb
    hs_mem
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at ht
    norm_num at ht
  have hζ₁ : riemannZeta₁ s ≠ 0 := hne s (closedBall_subset_ball (by linarith) hs_mem)
  have hζ : riemannZeta s ≠ 0 := zeta_ne_zero_of_zeta₁ hs1 hζ₁
  rw [logDeriv_zeta_eq hs1 hζ]
  have h1 := norm_one_div_sub_one_le ht
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
  calc ‖deriv riemannZeta₁ s / riemannZeta₁ s - 1 / (s - 1)‖
      ≤ ‖deriv riemannZeta₁ s / riemannZeta₁ s‖ + ‖1 / (s - 1)‖ := norm_sub_le _ _
    _ ≤ 24 * ((3 + Real.log (24 / c)) * L) / r + 1 := add_le_add hM h1
    _ = 6 * (3 + Real.log (24 / c)) / c * L ^ 2 + 1 := by
        rw [hr]
        field_simp
        ring
    _ ≤ (6 * (3 + Real.log (24 / c)) / c + 1) * L ^ 2 := by
        have : 0 ≤ 6 * (3 + Real.log (24 / c)) / c := by positivity
        nlinarith

/-- **The classical zero-free region with the bound for the logarithmic derivative.** -/
theorem regionStatement : ZetaShared.RegionStatement := by
  obtain ⟨c₁, hc₁, hzf⟩ := exists_zero_free
  have hc0 : 0 < min (c₁ / 6) (1 / 8) := lt_min (by positivity) (by norm_num)
  have hc6 : min (c₁ / 6) (1 / 8) ≤ c₁ / 6 := min_le_left _ _
  have hc8 : min (c₁ / 6) (1 / 8) ≤ 1 / 8 := min_le_right _ _
  have hlog0 : 0 ≤ Real.log (24 / min (c₁ / 6) (1 / 8)) :=
    Real.log_nonneg (by rw [le_div_iff₀ hc0]; linarith)
  refine ⟨min (c₁ / 6) (1 / 8), 6 * (3 + Real.log (24 / min (c₁ / 6) (1 / 8))) /
    min (c₁ / 6) (1 / 8) + 1, hc0, by positivity, ?_, ?_⟩
  · intro s hs hs1
    have hLpos : 0 < Real.log (|s.im| + 2) := Real.log_pos (by linarith [abs_nonneg s.im])
    refine zeta_ne_zero_of_zeta₁ hs1 (hzf s (le_trans ?_ hs))
    have : min (c₁ / 6) (1 / 8) / Real.log (|s.im| + 2) ≤ c₁ / Real.log (|s.im| + 2) := by
      gcongr
      linarith
    linarith
  · intro s hs hs2 ht
    exact norm_logDeriv_zeta_le hzf hc0 hc6 hc8 s hs hs2 ht

end ZetaRegion

#print axioms ZetaRegion.norm_logDeriv_zeta_le
#print axioms ZetaRegion.regionStatement
