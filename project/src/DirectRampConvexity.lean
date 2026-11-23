import Mathlib
import IndependentLandau.Ramp

/-! Direct real-variable convexity, finite-mesh reduction, and Chebyshev
convolution for the prime-power ramp `IndependentLandau.rampS` and `IndependentLandau.rampG`,
proved from Mathlib and `IndependentLandau.Ramp` alone without complex analysis. -/

open scoped ArithmeticFunction.vonMangoldt
open Finset Real

noncomputable section

namespace DirectRampConvexity

lemma rampT_convex_ineq (n : ℕ) {x y a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    IndependentLandau.rampT n (a * x + b * y) ≤
      a * IndependentLandau.rampT n x + b * IndependentLandau.rampT n y := by
  unfold IndependentLandau.rampT
  have hlin : (a * x + b * y) / (n : ℝ) - 1 =
      a * (x / (n : ℝ) - 1) + b * (y / (n : ℝ) - 1) := by
    calc (a * x + b * y) / (n : ℝ) - 1
        = a * (x / (n : ℝ)) + b * (y / (n : ℝ)) - (a + b) := by
            rw [hab, add_div, mul_div_assoc, mul_div_assoc]
      _ = a * (x / (n : ℝ) - 1) + b * (y / (n : ℝ) - 1) := by ring
  have hrhs : a * (Λ n * max (x / (n : ℝ) - 1) 0) + b * (Λ n * max (y / (n : ℝ) - 1) 0) =
      Λ n * (a * max (x / (n : ℝ) - 1) 0 + b * max (y / (n : ℝ) - 1) 0) := by ring
  rw [hlin, hrhs]
  refine mul_le_mul_of_nonneg_left ?_ ArithmeticFunction.vonMangoldt_nonneg
  refine max_le ?_ ?_
  · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
  · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))

theorem rampT_convexOn (n : ℕ) : ConvexOn ℝ Set.univ (IndependentLandau.rampT n) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simpa [smul_eq_mul] using rampT_convex_ineq n ha hb hab

private lemma rampS_eq_sum_range_of_lt {y : ℝ} {N : ℕ} (hN : ⌊y⌋₊ < N) :
    IndependentLandau.rampS y = ∑ n ∈ range N, IndependentLandau.rampT n y := by
  unfold IndependentLandau.rampS
  refine sum_subset (range_subset_range.mpr (Nat.succ_le_of_lt hN)) fun n _ hn => ?_
  exact IndependentLandau.rampT_eq_zero_of_floor_lt (by simpa [mem_range, Nat.lt_succ_iff] using hn)

theorem rampS_convex_ineq {x y a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    IndependentLandau.rampS (a * x + b * y) ≤
      a * IndependentLandau.rampS x + b * IndependentLandau.rampS y := by
  let N := max ⌊a * x + b * y⌋₊ (max ⌊x⌋₊ ⌊y⌋₊) + 1
  rw [rampS_eq_sum_range_of_lt (N := N) (by omega),
      rampS_eq_sum_range_of_lt (N := N) (by omega),
      rampS_eq_sum_range_of_lt (N := N) (by omega),
      mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_le_sum fun n _ => rampT_convex_ineq n ha hb hab

/-- The uncentered prime-power ramp `rampS` is globally convex on `ℝ`. -/
theorem rampS_convexOn : ConvexOn ℝ Set.univ IndependentLandau.rampS := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simpa [smul_eq_mul] using rampS_convex_ineq ha hb hab

private lemma xlogx_chord_gap {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let x := (1 - t) * a + t * b
    (1 - t) * (a * Real.log a) + t * (b * Real.log b) - x * Real.log x ≤
      (x - a) * (b - x) / a := by
  intro x
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hax : a ≤ x := by dsimp [x]; nlinarith
  have hx : 0 < x := ha.trans_le hax
  have hb0 : 0 < b := ha.trans_le hab
  have hdecomp :
      (1 - t) * (a * Real.log a) + t * (b * Real.log b) - x * Real.log x =
        (1 - t) * a * Real.log (a / x) + t * b * Real.log (b / x) := by
    rw [Real.log_div ha.ne' hx.ne', Real.log_div hb0.ne' hx.ne']
    dsimp [x]
    ring
  rw [hdecomp]
  have hla : Real.log (a / x) ≤ a / x - 1 := Real.log_le_sub_one_of_pos (div_pos ha hx)
  have hlb : Real.log (b / x) ≤ b / x - 1 := Real.log_le_sub_one_of_pos (div_pos hb0 hx)
  have hstep1 :
      (1 - t) * a * Real.log (a / x) + t * b * Real.log (b / x) ≤
        (1 - t) * a * (a / x - 1) + t * b * (b / x - 1) :=
    add_le_add (mul_le_mul_of_nonneg_left hla (mul_nonneg h1t ha.le))
      (mul_le_mul_of_nonneg_left hlb (mul_nonneg ht0 hb0.le))
  have hident :
      (1 - t) * a * (a / x - 1) + t * b * (b / x - 1) = (x - a) * (b - x) / x := by
    have hxn : x ≠ 0 := hx.ne'
    field_simp [hxn]
    dsimp [x]
    ring
  have hnum_nonneg : 0 ≤ (x - a) * (b - x) := by
    have hbx : x ≤ b := by dsimp [x]; nlinarith
    exact mul_nonneg (sub_nonneg.mpr hax) (sub_nonneg.mpr hbx)
  exact hstep1.trans (hident.le.trans
    (div_le_div_of_nonneg_left hnum_nonneg ha hax))

/-- Chord bound for `rampG`: on any `[a, b] ⊆ (0, ∞)`, `rampG` exceeds its secant chord
by at most `(x - a)(b - x) / a ≤ (b - a)^2 / (4a)`. -/
theorem rampG_chord_le {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let x := (1 - t) * a + t * b
    IndependentLandau.rampG x ≤
      (1 - t) * IndependentLandau.rampG a + t * IndependentLandau.rampG b +
        (x - a) * (b - x) / a := by
  intro x
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hS := rampS_convex_ineq (x := a) (y := b) h1t ht0 (by ring)
  have hL := xlogx_chord_gap ha hab ht0 ht1
  simp only [IndependentLandau.rampG_eq]
  dsimp [x] at hS hL ⊢
  linarith

theorem rampG_le_max_add_sq {a b x : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    IndependentLandau.rampG x ≤
      max (IndependentLandau.rampG a) (IndependentLandau.rampG b) + (b - a) ^ 2 / (4 * a) := by
  by_cases hlt : a < b
  · let t := (x - a) / (b - a)
    have hba : 0 < b - a := sub_pos.mpr hlt
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hax) hba.le
    have ht1 : t ≤ 1 := (div_le_one hba).mpr (by linarith)
    have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
    have hx_eq : (1 - t) * a + t * b = x := by
      dsimp [t]; field_simp [hba.ne']; ring
    have hchord := rampG_chord_le ha hlt.le ht0 ht1
    rw [hx_eq] at hchord
    have hmax :
        (1 - t) * IndependentLandau.rampG a + t * IndependentLandau.rampG b ≤
          max (IndependentLandau.rampG a) (IndependentLandau.rampG b) := by
      calc (1 - t) * IndependentLandau.rampG a + t * IndependentLandau.rampG b
          ≤ (1 - t) * max (IndependentLandau.rampG a) (IndependentLandau.rampG b) +
              t * max (IndependentLandau.rampG a) (IndependentLandau.rampG b) :=
            add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) h1t)
              (mul_le_mul_of_nonneg_left (le_max_right _ _) ht0)
        _ = max (IndependentLandau.rampG a) (IndependentLandau.rampG b) := by ring
    have hquad : (x - a) * (b - x) ≤ (b - a) ^ 2 / 4 := by nlinarith [sq_nonneg (2 * x - a - b)]
    have hdiv : (x - a) * (b - x) / a ≤ (b - a) ^ 2 / (4 * a) := by
      calc (x - a) * (b - x) / a ≤ ((b - a) ^ 2 / 4) / a :=
            div_le_div_of_nonneg_right hquad ha.le
        _ = (b - a) ^ 2 / (4 * a) := by ring
    linarith
  · have hab_eq : b = a := le_antisymm (le_of_not_gt hlt) (hax.trans hxb)
    have hxa : x = a := le_antisymm (hxb.trans hab_eq.le) hax
    rw [hab_eq, hxa]
    have hnn : 0 ≤ (a - a) ^ 2 / (4 * a) := by positivity
    linarith [le_max_left (IndependentLandau.rampG a) (IndependentLandau.rampG a)]

/-- Finite-mesh reduction of continuous window bounds: checking `rampG (pts k) ≤ C * (pts k)^θ`
on a finite partition `Y = pts 0 ≤ ... ≤ pts K = Y^(3/2)` of step at most `2 * (pts k)^((1+θ)/2)`
certifies `rampG x ≤ (3 * C + 1) * x^θ` at **every** real `x ∈ [Y, Y^(3/2)]`. -/
theorem ordinaryWindow_of_finite_mesh {θ C Y : ℝ} {K : ℕ} {pts : ℕ → ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hC : 0 ≤ C) (hY : 1 ≤ Y)
    (h0 : pts 0 = Y) (hK : pts K = Y ^ (3 / 2 : ℝ))
    (hmono : ∀ k < K, pts k ≤ pts (k + 1))
    (hstep : ∀ k < K, pts (k + 1) - pts k ≤ 2 * (pts k) ^ ((1 + θ) / 2))
    (hmesh : ∀ k ≤ K, IndependentLandau.rampG (pts k) ≤ C * (pts k) ^ θ) :
    ∀ x ∈ Set.Icc Y (Y ^ (3 / 2 : ℝ)), IndependentLandau.rampG x ≤ (3 * C + 1) * x ^ θ := by
  have hpts_ge : ∀ k ≤ K, Y ≤ pts k := by
    intro k hk
    induction k with
    | zero => exact h0.symm.le
    | succ j ih => exact (ih (Nat.le_of_succ_le hk)).trans (hmono j (Nat.lt_of_succ_le hk))
  have hcover : ∀ k : ℕ, 1 ≤ k → k ≤ K → ∀ x ∈ Set.Icc (pts 0) (pts k),
      ∃ j < k, x ∈ Set.Icc (pts j) (pts (j + 1)) := by
    intro k hk1 hkK
    induction k with
    | zero => omega
    | succ m ih =>
      intro x hx
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · exact ⟨0, Nat.succ_pos 0, hx⟩
      · by_cases hxm : x ≤ pts m
        · obtain ⟨j, hj, hjx⟩ := ih hmpos (Nat.le_of_succ_le hkK) x ⟨hx.1, hxm⟩
          exact ⟨j, Nat.lt_succ_of_lt hj, hjx⟩
        · exact ⟨m, Nat.lt_succ_self m, le_of_not_ge hxm, hx.2⟩
  intro x hx
  have hx' : x ∈ Set.Icc (pts 0) (pts K) := by rwa [h0, hK]
  rcases Nat.eq_zero_or_pos K with rfl | hKpos
  · obtain rfl : x = pts 0 := le_antisymm hx'.2 hx'.1
    have hpt0 : 0 < pts 0 := by linarith
    have hrpow : 0 ≤ (pts 0) ^ θ := Real.rpow_nonneg hpt0.le θ
    have h1 := hmesh 0 le_rfl
    nlinarith
  · obtain ⟨j, hjK, hjx⟩ := hcover K hKpos le_rfl x hx'
    have ha1 : 1 ≤ pts j := hY.trans (hpts_ge j (Nat.le_of_lt hjK))
    have ha : 0 < pts j := by linarith
    have hx_pos : 0 < x := ha.trans_le hjx.1
    have hmain := rampG_le_max_add_sq ha hjx.1 hjx.2
    have hba0 : 0 ≤ pts (j + 1) - pts j := sub_nonneg.mpr (hmono j hjK)
    have hsq : (pts (j + 1) - pts j) ^ 2 ≤ (2 * (pts j) ^ ((1 + θ) / 2)) ^ 2 :=
      pow_le_pow_left₀ hba0 (hstep j hjK) 2
    have hpow_eq : ((pts j) ^ ((1 + θ) / 2)) ^ 2 = (pts j) ^ (1 + θ) := by
      rw [← Real.rpow_natCast ((pts j) ^ ((1 + θ) / 2)) 2, ← Real.rpow_mul ha.le]
      ring_nf
    have herr : (pts (j + 1) - pts j) ^ 2 / (4 * pts j) ≤ x ^ θ := by
      calc (pts (j + 1) - pts j) ^ 2 / (4 * pts j)
          ≤ (2 * (pts j) ^ ((1 + θ) / 2)) ^ 2 / (4 * pts j) :=
            div_le_div_of_nonneg_right hsq (by positivity)
        _ = ((pts j) ^ ((1 + θ) / 2)) ^ 2 / pts j := by ring
        _ = (pts j) ^ (1 + θ) / pts j := by rw [hpow_eq]
        _ = (pts j) ^ θ := by
            rw [Real.rpow_add ha, Real.rpow_one, mul_comm, mul_div_cancel_right₀ _ ha.ne']
        _ ≤ x ^ θ := Real.rpow_le_rpow ha.le hjx.1 hθ0
    have hm1 : IndependentLandau.rampG (pts j) ≤ 3 * C * x ^ θ := by
      have h := (hmesh j (Nat.le_of_lt hjK)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha.le hjx.1 hθ0) hC)
      have hxθ : 0 ≤ x ^ θ := Real.rpow_nonneg hx_pos.le θ
      nlinarith
    have hb_le : pts (j + 1) ≤ 3 * x := by
      have hhalf : (pts j) ^ ((1 + θ) / 2) ≤ pts j := by
        calc (pts j) ^ ((1 + θ) / 2) ≤ (pts j) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le ha1 (by linarith)
          _ = pts j := Real.rpow_one _
      have hs := hstep j hjK
      linarith [hjx.1]
    have hm2 : IndependentLandau.rampG (pts (j + 1)) ≤ 3 * C * x ^ θ := by
      have hb0 : 0 ≤ pts (j + 1) := ha.le.trans (hmono j hjK)
      have h3θ : (3 : ℝ) ^ θ ≤ 3 := by
        calc (3 : ℝ) ^ θ ≤ (3 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1
          _ = 3 := Real.rpow_one _
      have hr : (pts (j + 1)) ^ θ ≤ 3 * x ^ θ := by
        calc (pts (j + 1)) ^ θ ≤ (3 * x) ^ θ := Real.rpow_le_rpow hb0 hb_le hθ0
          _ = (3 : ℝ) ^ θ * x ^ θ := Real.mul_rpow (by norm_num) hx_pos.le
          _ ≤ 3 * x ^ θ := mul_le_mul_of_nonneg_right h3θ (Real.rpow_nonneg hx_pos.le θ)
      have h := (hmesh (j + 1) hjK).trans (mul_le_mul_of_nonneg_left hr hC)
      linarith
    have hmax : max (IndependentLandau.rampG (pts j)) (IndependentLandau.rampG (pts (j + 1))) ≤
        3 * C * x ^ θ := max_le hm1 hm2
    linarith

/-- Direct Chebyshev convolution identity on `ℕ`: summing `rampS (x / m)` over `1 ≤ m ≤ ⌊x⌋₊`
eliminates `Λ` identically and yields the smooth integer ramp `∑_{1 ≤ k ≤ ⌊x⌋₊} (log k)(x / k - 1)`. -/
theorem sum_rampS_div_eq_log_ramp {x : ℝ} (hx : 0 ≤ x) :
    ∑ m ∈ Icc 1 ⌊x⌋₊, IndependentLandau.rampS (x / m) =
      ∑ k ∈ Icc 1 ⌊x⌋₊, Real.log k * (x / k - 1) := by
  have hterm : ∀ m ∈ Icc 1 ⌊x⌋₊,
      IndependentLandau.rampS (x / m) =
        ∑ k ∈ Icc 1 ⌊x⌋₊, if m ∣ k then Λ (k / m) * (x / k - 1) else 0 := by
    intro m hm
    obtain ⟨hm1, _⟩ := mem_Icc.mp hm
    have hm0 : 0 < m := hm1
    have hmr : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
    unfold IndependentLandau.rampS
    have hsub : range (⌊x / m⌋₊ + 1) = insert 0 (Icc 1 ⌊x / m⌋₊) := by
      ext n; simp [mem_range, mem_Icc]; omega
    rw [hsub, sum_insert (by simp), IndependentLandau.rampT_zero, zero_add, ← sum_filter]
    refine sum_nbij (fun n => m * n) ?_ ?_ ?_ ?_
    · intro n hn
      obtain ⟨hn1, hnfl⟩ := mem_Icc.mp hn
      have hle_r : ((m * n : ℕ) : ℝ) ≤ x := by
        have h1 : (n : ℝ) ≤ x / m := (Nat.le_floor_iff (div_nonneg hx hmr.le)).mp hnfl
        have h2 := (le_div_iff₀' hmr).mp h1
        exact_mod_cast h2
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hm0 hn1, Nat.le_floor hle_r⟩, dvd_mul_right m n⟩
    · intro n₁ _ n₂ _ hmul
      exact Nat.eq_of_mul_eq_mul_left hm0 hmul
    · intro k hk
      obtain ⟨hk_mem, ⟨n, rfl⟩⟩ := mem_filter.mp hk
      obtain ⟨hk1, hkfl⟩ := mem_Icc.mp hk_mem
      have hn1 : 1 ≤ n := by
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · simp at hk1
        · exact hpos
      have hmn_x : ((m * n : ℕ) : ℝ) ≤ x := (Nat.le_floor_iff hx).mp hkfl
      have hn_xm : (n : ℝ) ≤ x / m := (le_div_iff₀' hmr).mpr (by exact_mod_cast hmn_x)
      exact ⟨n, mem_Icc.mpr ⟨hn1, Nat.le_floor hn_xm⟩, rfl⟩
    · intro n hn
      obtain ⟨hn1, hnfl⟩ := mem_Icc.mp hn
      have hn_xm : (n : ℝ) ≤ x / m := (Nat.le_floor_iff (div_nonneg hx hmr.le)).mp hnfl
      have hnn0 : 0 ≤ (x / m) / n - 1 := by
        have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
        rw [sub_nonneg, one_le_div hnr]
        exact hn_xm
      unfold IndependentLandau.rampT
      rw [max_eq_left hnn0, Nat.mul_div_cancel_left n hm0, Nat.cast_mul, div_div]
  calc ∑ m ∈ Icc 1 ⌊x⌋₊, IndependentLandau.rampS (x / m)
      = ∑ m ∈ Icc 1 ⌊x⌋₊, ∑ k ∈ Icc 1 ⌊x⌋₊,
          if m ∣ k then Λ (k / m) * (x / k - 1) else 0 := sum_congr rfl hterm
    _ = ∑ k ∈ Icc 1 ⌊x⌋₊, ∑ m ∈ Icc 1 ⌊x⌋₊,
          if m ∣ k then Λ (k / m) * (x / k - 1) else 0 := sum_comm
    _ = ∑ k ∈ Icc 1 ⌊x⌋₊, Real.log k * (x / k - 1) := by
        refine sum_congr rfl fun k hk => ?_
        obtain ⟨hk1, hkfl⟩ := mem_Icc.mp hk
        rw [← sum_filter]
        have hfilt : (Icc 1 ⌊x⌋₊).filter (· ∣ k) = k.divisors := by
          ext m
          simp only [mem_filter, mem_Icc, Nat.mem_divisors]
          constructor
          · rintro ⟨_, hdvd⟩; exact ⟨hdvd, by omega⟩
          · rintro ⟨hdvd, _⟩
            have hm_le_k : m ≤ k := Nat.le_of_dvd hk1 hdvd
            exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd hk1, hm_le_k.trans hkfl⟩, hdvd⟩
        rw [hfilt, ← sum_mul]
        congr 1
        have hdiv_sum : (∑ m ∈ k.divisors, Λ (k / m)) = ∑ d ∈ k.divisors, Λ d := by
          refine sum_nbij (fun m => k / m) ?_ ?_ ?_ (fun _ _ => rfl)
          · intro m hm
            exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hm).1, by omega⟩
          · intro m₁ hm₁ m₂ hm₂ heq
            dsimp at heq
            have h1 := Nat.div_div_self (Nat.mem_divisors.mp hm₁).1 (by omega : k ≠ 0)
            have h2 := Nat.div_div_self (Nat.mem_divisors.mp hm₂).1 (by omega : k ≠ 0)
            rw [← h1, ← h2, heq]
          · intro d hd
            have hdvd := (Nat.mem_divisors.mp hd).1
            exact ⟨k / d, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdvd, by omega⟩,
              Nat.div_div_self hdvd (by omega : k ≠ 0)⟩
        rw [hdiv_sum, ArithmeticFunction.vonMangoldt_sum]

#print axioms rampS_convexOn
#print axioms rampG_chord_le
#print axioms rampG_le_max_add_sq
#print axioms ordinaryWindow_of_finite_mesh
#print axioms sum_rampS_div_eq_log_ramp

end DirectRampConvexity
