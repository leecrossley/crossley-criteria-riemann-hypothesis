import Mathlib
import ZetaShared.Perron
import IndependentLandau.Analytic
import ZetaCount.Growth
import ZetaStrip.Left
import ZetaStrip.Growth
import ZetaStrip.Local

/-! Bounds for `ζ'/ζ` on the line `re s = -1/2` and on horizontal segments at well-chosen
heights, from Landau's lemma applied to `riemannZeta₁` on discs centred on `re s = 2`. -/

open Complex Set Filter Topology Metric

noncomputable section
namespace ZetaStrip

lemma mem_closedBall_of_sq {s c : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : (s.re - c.re) ^ 2 + (s.im - c.im) ^ 2 ≤ ρ ^ 2) : s ∈ closedBall c ρ := by
  rw [mem_closedBall, dist_eq_norm]
  have hsq : ‖s - c‖ ^ 2 = (s.re - c.re) ^ 2 + (s.im - c.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  by_contra hcon
  push Not at hcon
  nlinarith [norm_nonneg (s - c)]

/-- Growth of `riemannZeta₁` on the circle of radius `14/5` about `2 + i t₀`. -/
lemma norm_zeta₁_sphere_le (t₀ : ℝ) {z : ℂ} (hz : z ∈ sphere (2 + t₀ * I : ℂ) (14 / 5)) :
    ‖riemannZeta₁ z‖ ≤ 27 * (|t₀| + 2) ^ 3 := by
  set c : ℂ := 2 + t₀ * I with hc
  rw [mem_sphere, dist_eq_norm] at hz
  have ha : 0 ≤ |t₀| := abs_nonneg _
  have hre : -4 / 5 ≤ z.re := by
    have h := Complex.abs_re_le_norm (z - c)
    rw [hz] at h
    have h' := (abs_le.mp h).1
    have e : (z - c).re = z.re - 2 := by simp [hc]
    rw [e] at h'; linarith
  have hcn : ‖c‖ ≤ 2 + |t₀| := by
    calc ‖c‖ ≤ ‖(2 : ℂ)‖ + ‖(t₀ : ℂ) * I‖ := norm_add_le _ _
      _ = 2 + |t₀| := by simp
  have hz0 : ‖z‖ ≤ |t₀| + 24 / 5 := by
    have : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
      have := norm_add_le (z - c) c
      rwa [sub_add_cancel] at this
    rw [hz] at this; linarith
  have hz1 : ‖z - 1‖ ≤ |t₀| + 6 := by
    have : ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    rw [norm_one] at this; linarith
  have hz2 : ‖z + 1‖ ≤ |t₀| + 6 := by
    have : ‖z + 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    rw [norm_one] at this; linarith
  have hz0' : ‖z‖ ≤ |t₀| + 6 := by linarith
  set x : ℝ := |t₀| + 2 with hx
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hy : |t₀| + 6 ≤ 3 * x := by linarith
  have hy3 : (|t₀| + 6) ^ 3 ≤ 27 * x ^ 3 := by
    calc (|t₀| + 6) ^ 3 ≤ (3 * x) ^ 3 := pow_le_pow_left₀ (by linarith) hy 3
      _ = 27 * x ^ 3 := by ring
  have hx3 : x ≤ x ^ 3 := by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x) (by nlinarith : (0 : ℝ) ≤ x ^ 2 - 1)]
  refine (norm_zeta₁_le_left hre).trans ?_
  have hn0 := norm_nonneg z
  have hn1 := norm_nonneg (z - 1)
  have hn2 := norm_nonneg (z + 1)
  calc ‖z + 1‖ / 2 + 5 / 8 * ‖z‖ * ‖z - 1‖ * ‖z + 1‖
      ≤ (|t₀| + 6) / 2 + 5 / 8 * (|t₀| + 6) * (|t₀| + 6) * (|t₀| + 6) := by gcongr
    _ = (|t₀| + 6) / 2 + 5 / 8 * (|t₀| + 6) ^ 3 := by ring
    _ ≤ 27 * x ^ 3 := by nlinarith

/-- Landau's lemma for `riemannZeta₁` on the discs about `2 + i t₀`. -/
theorem zeta₁_local : ∃ K κ : ℝ, 0 < K ∧ 0 < κ ∧ ∀ t₀ : ℝ, ∃ S : Finset ℂ,
    (∀ u ∈ S, u ∈ closedBall (2 + t₀ * I : ℂ) (27 / 10) ∧ riemannZeta₁ u = 0 ∧
      1 ≤ analyticOrderNatAt riemannZeta₁ u) ∧
    (∀ z ∈ closedBall (2 + t₀ * I : ℂ) (27 / 10), riemannZeta₁ z = 0 → z ∈ S) ∧
    ((∑ u ∈ S, analyticOrderNatAt riemannZeta₁ u : ℕ) : ℝ) ≤ κ * Real.log (|t₀| + 2) ∧
    ∀ z ∈ closedBall (2 + t₀ * I : ℂ) (13 / 5), riemannZeta₁ z ≠ 0 →
      ‖deriv riemannZeta₁ z / riemannZeta₁ z -
        ∑ u ∈ S, (analyticOrderNatAt riemannZeta₁ u : ℂ) / (z - u)‖
          ≤ K * Real.log (|t₀| + 2) := by
  obtain ⟨K₀, hK₀, hL⟩ := exists_logDeriv_approx (r := 13 / 5) (R₁ := 27 / 10) (R := 14 / 5)
    (by norm_num) (by norm_num) (by norm_num)
  have hlog : 0 < Real.log ((14 / 5 : ℝ) / (27 / 10)) := Real.log_pos (by norm_num)
  refine ⟨K₀ * 11, 11 / Real.log ((14 / 5 : ℝ) / (27 / 10)), by positivity, by positivity, ?_⟩
  intro t₀
  set x : ℝ := |t₀| + 2 with hx
  have hx2 : (2 : ℝ) ≤ x := by have := abs_nonneg t₀; linarith
  have hx0 : 0 < x := by linarith
  set c : ℂ := 2 + t₀ * I with hc
  set A : ℝ := 11 * Real.log x with hA
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hA0 : 0 < A := by positivity
  have hexp : Real.exp A = x ^ 11 := by
    rw [hA, show (11 : ℝ) * Real.log x = ((11 : ℕ) : ℝ) * Real.log x by norm_num,
      Real.exp_nat_mul, Real.exp_log hx0]
  have hcge : 1 / 4 ≤ ‖riemannZeta₁ c‖ := ZetaCount.norm_zeta₁_two_add_ge t₀
  have hc0 : riemannZeta₁ c ≠ 0 := by
    intro h; rw [h, norm_zero] at hcge; norm_num at hcge
  have h8 : (256 : ℝ) ≤ x ^ 8 := by
    calc (256 : ℝ) = 2 ^ 8 := by norm_num
      _ ≤ x ^ 8 := pow_le_pow_left₀ (by norm_num) hx2 8
  have hx3 : (8 : ℝ) ≤ x ^ 3 := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx2 3
  have hbig : 27 * x ^ 3 ≤ Real.exp A * ‖riemannZeta₁ c‖ := by
    rw [hexp]
    have h1 : 256 * x ^ 3 ≤ x ^ 8 * x ^ 3 := mul_le_mul_of_nonneg_right h8 (by positivity)
    have h2 : x ^ 11 * (1 / 4) ≤ x ^ 11 * ‖riemannZeta₁ c‖ :=
      mul_le_mul_of_nonneg_left hcge (by positivity)
    have e : x ^ 11 = x ^ 8 * x ^ 3 := by ring
    rw [e] at h2 ⊢
    linarith
  obtain ⟨S, hS1, hS2, hS3, hS4⟩ := hL riemannZeta₁ c A differentiable_riemannZeta₁ hc0 hA0
    (by linarith) (fun z hz => (norm_zeta₁_sphere_le t₀ hz).trans hbig)
  refine ⟨S, hS1, hS2, ?_, ?_⟩
  · calc ((∑ u ∈ S, analyticOrderNatAt riemannZeta₁ u : ℕ) : ℝ)
        ≤ A / Real.log ((14 / 5 : ℝ) / (27 / 10)) := hS3
      _ = 11 / Real.log ((14 / 5 : ℝ) / (27 / 10)) * Real.log x := by rw [hA]; ring
  · intro z hz hne
    calc _ ≤ K₀ * A := hS4 z hz hne
      _ = K₀ * 11 * Real.log x := by rw [hA]; ring

/-- A height in `[T, T + 1]` at distance at least `1/(2(N+1))` from the heights of `N` given
points. -/
lemma exists_height (S : Finset ℂ) (T : ℝ) :
    ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧
      ∀ u ∈ S, 1 / (2 * ((S.card : ℝ) + 1)) ≤ |u.im - T'| := by
  classical
  set N : ℕ := S.card with hN
  set δ : ℝ := 1 / (2 * ((N : ℝ) + 1)) with hδ
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hδ0 : 0 < δ := by positivity
  have hδN : 2 * ((N : ℝ) + 1) * δ = 1 := by rw [hδ]; field_simp
  by_contra hcon
  push Not at hcon
  have hex : ∀ j ∈ Finset.range (N + 1),
      ∃ u ∈ S, |u.im - (T + (2 * (j : ℝ) + 1) * δ)| < δ := by
    intro j hj
    have hj' : (j : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    refine hcon _ ?_ ?_
    · nlinarith
    · nlinarith
  choose! φ hφS hφ using hex
  obtain ⟨j, hj, k, hk, hjk, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (N + 1)) (t := S) (by simp [hN]) hφS
  have h1 := hφ j hj
  have h2 := hφ k hk
  rw [heq] at h1
  have h3 : |(2 * (j : ℝ) + 1) * δ - (2 * (k : ℝ) + 1) * δ| < 2 * δ := by
    rw [abs_lt] at h1 h2 ⊢
    constructor <;> linarith
  have h4 : (1 : ℝ) ≤ |(j : ℝ) - k| := by
    have hne : (j : ℤ) - k ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hjk)
    have := Int.one_le_abs hne
    exact_mod_cast this
  have h5 : |(2 * (j : ℝ) + 1) * δ - (2 * (k : ℝ) + 1) * δ| = 2 * δ * |(j : ℝ) - k| := by
    rw [show (2 * (j : ℝ) + 1) * δ - (2 * (k : ℝ) + 1) * δ = 2 * δ * ((j : ℝ) - k) by ring,
      abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * δ)]
  rw [h5] at h3
  nlinarith

lemma norm_sum_div_le {S : Finset ℂ} {m : ℂ → ℕ} {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ u ∈ S, δ ≤ ‖z - u‖) :
    ‖∑ u ∈ S, (m u : ℂ) / (z - u)‖ ≤ ((∑ u ∈ S, m u : ℕ) : ℝ) / δ := by
  calc ‖∑ u ∈ S, (m u : ℂ) / (z - u)‖ ≤ ∑ u ∈ S, ‖(m u : ℂ) / (z - u)‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ S, (m u : ℝ) / δ := Finset.sum_le_sum fun u hu => by
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (h u hu)
    _ = ((∑ u ∈ S, m u : ℕ) : ℝ) / δ := by rw [← Finset.sum_div]; push_cast; rfl

/-- From `riemannZeta₁` to `ζ`: `ζ'/ζ = ζ₁'/ζ₁ - 1/(s - 1)`, and the triangle inequality. -/
lemma norm_logDeriv_zeta_le {s : ℂ} (hs1 : s ≠ 1) (hz : riemannZeta₁ s ≠ 0) {S : Finset ℂ}
    {m : ℂ → ℕ} {E δ a : ℝ} (hδ : 0 < δ) (ha : 0 < a)
    (happ : ‖deriv riemannZeta₁ s / riemannZeta₁ s - ∑ u ∈ S, (m u : ℂ) / (s - u)‖ ≤ E)
    (hfar : ∀ u ∈ S, δ ≤ ‖s - u‖) (hs1' : a ≤ ‖s - 1‖) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤ E + ((∑ u ∈ S, m u : ℕ) : ℝ) / δ + 1 / a := by
  have h : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have e : deriv riemannZeta s / riemannZeta s =
      (deriv riemannZeta₁ s / riemannZeta₁ s - ∑ u ∈ S, (m u : ℂ) / (s - u)) +
        ∑ u ∈ S, (m u : ℂ) / (s - u) - 1 / (s - 1) := by
    rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs1, riemannZeta_eq_inv_sub_mul hs1]
    field_simp
    ring
  rw [e]
  have h1 : ‖(1 : ℂ) / (s - 1)‖ ≤ 1 / a := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le ha hs1'
  have h2 := norm_sum_div_le (m := m) hδ hfar
  calc _ ≤ ‖(deriv riemannZeta₁ s / riemannZeta₁ s - ∑ u ∈ S, (m u : ℂ) / (s - u)) +
        ∑ u ∈ S, (m u : ℂ) / (s - u)‖ + ‖(1 : ℂ) / (s - 1)‖ := norm_sub_le _ _
    _ ≤ ‖deriv riemannZeta₁ s / riemannZeta₁ s - ∑ u ∈ S, (m u : ℂ) / (s - u)‖ +
        ‖∑ u ∈ S, (m u : ℂ) / (s - u)‖ + ‖(1 : ℂ) / (s - 1)‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ E + ((∑ u ∈ S, m u : ℕ) : ℝ) / δ + 1 / a := by gcongr

/-- Bounds for the logarithmic derivative of zeta on `re s = -1/2` and on horizontal segments
across the critical strip at well-chosen heights. -/
theorem stripLogDerivStatement : ZetaShared.StripLogDerivStatement := by
  obtain ⟨K, κ, hK, hκ, hloc⟩ := zeta₁_local
  refine ⟨(K + 2 * κ + 1) + (2 * K + 8 * κ ^ 2 + 4 * κ + 1), by positivity, ?_, ?_, ?_⟩
  · intro s h1 h0
    exact riemannZeta_ne_zero_of_re_le_zero (by linarith) h0
  · intro t
    have ehalf : (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [ehalf]
    set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I with hs
    have hsre : s.re = -1 / 2 := by simp [hs]
    have hsim : s.im = t := by simp [hs]
    obtain ⟨S, hS1, hS2, hS3, hS4⟩ := hloc t
    set L : ℝ := Real.log (|t| + 2) with hL
    have hL23 : 2 / 3 ≤ L := by
      have h2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
      have := Real.log_two_gt_d9
      linarith
    have hζ : riemannZeta s ≠ 0 :=
      riemannZeta_ne_zero_of_re_le_zero (by rw [hsre]; norm_num) (by rw [hsre]; norm_num)
    have hs1 : s ≠ 1 := by
      intro h; rw [h] at hsre; norm_num at hsre
    have hζ₁ : riemannZeta₁ s ≠ 0 := fun h => hζ (IndependentLandau.zeta₁_eq_zero_iff.mp h)
    have hsball : s ∈ closedBall (2 + t * I : ℂ) (13 / 5) :=
      mem_closedBall_of_sq (by norm_num) (by rw [hsre, hsim]; simp; norm_num)
    have hfar : ∀ u ∈ S, (1 / 2 : ℝ) ≤ ‖s - u‖ := by
      intro u hu
      obtain ⟨hub, hu0, -⟩ := hS1 u hu
      have hure : -7 / 10 ≤ u.re := by
        have h := Complex.abs_re_le_norm (u - (2 + t * I))
        rw [mem_closedBall, dist_eq_norm] at hub
        have h' := (abs_le.mp (h.trans hub)).1
        simp at h'; linarith
      have hupos : 0 < u.re := by
        by_contra hneg
        push Not at hneg
        exact riemannZeta_ne_zero_of_re_le_zero (by linarith) hneg
          (IndependentLandau.zeta₁_eq_zero_iff.mp hu0)
      have h := Complex.abs_re_le_norm (s - u)
      rw [Complex.sub_re, hsre] at h
      linarith [neg_le_abs (-1 / 2 - u.re)]
    have hs1n : (3 / 2 : ℝ) ≤ ‖s - 1‖ := by
      have h := Complex.abs_re_le_norm (s - 1)
      rw [Complex.sub_re, hsre, Complex.one_re] at h
      linarith [neg_le_abs ((-1 / 2 : ℝ) - 1)]
    have key := norm_logDeriv_zeta_le hs1 hζ₁ (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 3 / 2) (hS4 s hsball hζ₁) hfar hs1n
    have hextra : 0 ≤ (2 * K + 8 * κ ^ 2 + 4 * κ + 1) * L := by
      have : 0 ≤ L := by linarith
      positivity
    have hn : ((∑ u ∈ S, analyticOrderNatAt riemannZeta₁ u : ℕ) : ℝ) / (1 / 2) ≤ 2 * (κ * L) := by
      rw [div_div_eq_mul_div, div_one]; linarith
    calc _ ≤ K * L + ((∑ u ∈ S, analyticOrderNatAt riemannZeta₁ u : ℕ) : ℝ) / (1 / 2)
          + 1 / (3 / 2) := key
      _ ≤ K * L + 2 * (κ * L) + L := by
          have : (1 : ℝ) / (3 / 2) ≤ L := by norm_num; linarith
          linarith
      _ ≤ ((K + 2 * κ + 1) + (2 * K + 8 * κ ^ 2 + 4 * κ + 1)) * L := by linarith
  · intro T hT
    set t₀ : ℝ := T + 1 / 2 with ht₀
    obtain ⟨S, hS1, hS2, hS3, hS4⟩ := hloc t₀
    obtain ⟨T', hT1, hT2, hfarT⟩ := exists_height S T
    refine ⟨T', hT1, hT2, ?_⟩
    intro σ hσ1 hσ2
    set s : ℂ := (σ : ℂ) + (T' : ℂ) * I with hs
    have hsre : s.re = σ := by simp [hs]
    have hsim : s.im = T' := by simp [hs]
    set N : ℕ := S.card with hN
    set δ : ℝ := 1 / (2 * ((N : ℝ) + 1)) with hδ
    have hδ0 : 0 < δ := by positivity
    have hsball : s ∈ closedBall (2 + t₀ * I : ℂ) (13 / 5) :=
      mem_closedBall_of_sq (by norm_num) (by
        rw [hsre, hsim]
        simp only [add_re, re_ofNat, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero, add_im, im_ofNat, mul_im, zero_add]
        rw [ht₀]
        nlinarith [mul_nonneg (sub_nonneg.mpr hσ1) (sub_nonneg.mpr hσ2),
          mul_nonneg (sub_nonneg.mpr hT1) (sub_nonneg.mpr hT2)])
    have hζ₁ : riemannZeta₁ s ≠ 0 := by
      intro h
      have hsS := hS2 s (closedBall_subset_closedBall (by norm_num) hsball) h
      have := hfarT s hsS
      rw [hsim, sub_self, abs_zero] at this
      linarith
    have hs1 : s ≠ 1 := by
      intro h; rw [h] at hsim; simp at hsim; linarith
    have hζ : riemannZeta s ≠ 0 := fun h => hζ₁ (IndependentLandau.zeta₁_eq_zero_iff.mpr h)
    refine ⟨hζ, ?_⟩
    have hfar : ∀ u ∈ S, δ ≤ ‖s - u‖ := by
      intro u hu
      have h := Complex.abs_im_le_norm (s - u)
      rw [Complex.sub_im, hsim] at h
      have := hfarT u hu
      rw [abs_sub_comm] at this
      exact this.trans h
    have hs1n : (2 : ℝ) ≤ ‖s - 1‖ := by
      have h := Complex.abs_im_le_norm (s - 1)
      rw [Complex.sub_im, hsim, Complex.one_im, sub_zero] at h
      linarith [le_abs_self T']
    have key := norm_logDeriv_zeta_le hs1 hζ₁ hδ0 (by norm_num : (0 : ℝ) < 2)
      (hS4 s hsball hζ₁) hfar hs1n
    set L : ℝ := Real.log (T + 2) with hL
    have hL1 : 1 ≤ L := by
      have h : Real.exp 1 ≤ T + 2 := by have := Real.exp_one_lt_d9; linarith
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ L := Real.log_le_log (Real.exp_pos 1) h
    have hL₀ : Real.log (|t₀| + 2) ≤ 2 * L := by
      rw [abs_of_pos (by linarith : 0 < t₀)]
      have h : t₀ + 2 ≤ (T + 2) ^ 2 := by rw [ht₀]; nlinarith
      calc Real.log (t₀ + 2) ≤ Real.log ((T + 2) ^ 2) := Real.log_le_log (by linarith) h
        _ = 2 * L := by rw [Real.log_pow]; push_cast; ring
    set n : ℕ := ∑ u ∈ S, analyticOrderNatAt riemannZeta₁ u with hn
    have hNn : (N : ℝ) ≤ n := by
      have h : N ≤ n := by
        rw [hn, hN, Finset.card_eq_sum_ones]
        exact Finset.sum_le_sum fun u hu => (hS1 u hu).2.2
      exact_mod_cast h
    have hn2 : (n : ℝ) ≤ 2 * κ * L := by
      calc (n : ℝ) ≤ κ * Real.log (|t₀| + 2) := hS3
        _ ≤ κ * (2 * L) := by gcongr
        _ = 2 * κ * L := by ring
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hsum : (n : ℝ) / δ ≤ 2 * (2 * κ * L) * (2 * κ * L + 1) := by
      have e : (n : ℝ) / δ = 2 * n * (N + 1) := by rw [hδ]; field_simp
      rw [e]
      have h : (N : ℝ) + 1 ≤ 2 * κ * L + 1 := by linarith
      gcongr
    have hLL : L ≤ L ^ 2 := by nlinarith
    have h1L : 1 ≤ L ^ 2 := by nlinarith
    calc _ ≤ K * Real.log (|t₀| + 2) + (n : ℝ) / δ + 1 / 2 := key
      _ ≤ K * (2 * L) + 2 * (2 * κ * L) * (2 * κ * L + 1) + 1 / 2 := by gcongr
      _ ≤ ((K + 2 * κ + 1) + (2 * K + 8 * κ ^ 2 + 4 * κ + 1)) * L ^ 2 := by
          nlinarith [mul_nonneg hK.le (sub_nonneg.mpr hLL), mul_nonneg hκ.le (sub_nonneg.mpr hLL),
            mul_nonneg hK.le (sq_nonneg L), mul_nonneg hκ.le (sq_nonneg L), sq_nonneg L,
            mul_nonneg (sq_nonneg κ) (sq_nonneg L)]

end ZetaStrip

#print axioms ZetaStrip.stripLogDerivStatement
