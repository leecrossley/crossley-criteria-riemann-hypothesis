import Mathlib

/-! Elementary real-variable lemmas used in the window form of Landau's theorem. -/

open Filter Topology

namespace IndependentLandau

/-- Final contradiction: a lower bound of rate `1/d` cannot be dominated by
terms of rate `1/e₁` with `d < e₁`, even with an `exp (η U)` loss, `U ≤ k`. -/
theorem no_room {d e₁ c₀ : ℝ} (M : ℝ) {C : ℝ} (hd : 0 < d) (hde : d < e₁) (hc₀ : 0 < c₀)
    (hC : 0 ≤ C) :
    ∃ η : ℝ, 0 < η ∧ ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U → ∀ k : ℕ, U ≤ k →
      M / e₁ ^ k + C * Real.exp (η * U) / e₁ ^ k < c₀ / d ^ (k + 1) := by
  have he₁ : 0 < e₁ := hd.trans hde
  set x : ℝ := Real.sqrt (e₁ / d) with hx
  have hx1 : 1 < x := by
    rw [hx]
    apply Real.lt_sqrt_of_sq_lt
    rw [one_pow, lt_div_iff₀ hd]
    linarith
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hx2 : x ^ 2 = e₁ / d := Real.sq_sqrt (by positivity)
  have he₁x : e₁ = x ^ 2 * d := by rw [hx2]; field_simp
  refine ⟨Real.log x, Real.log_pos hx1, ?_⟩
  have hT : Tendsto (fun k : ℕ => (|M| + C) * d * (x⁻¹) ^ k) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 hx0.le)
      (inv_lt_one_of_one_lt₀ hx1)).const_mul ((|M| + C) * d)
    simpa using this
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hT.eventually (gt_mem_nhds hc₀))
  refine ⟨N, fun U hU k hk => ?_⟩
  have hNk : N ≤ k := by exact_mod_cast hU.trans hk
  have hk' := hN k hNk
  set y : ℝ := x ^ k with hy
  have hy1 : 1 ≤ y := one_le_pow₀ hx1.le
  have hy0 : 0 < y := zero_lt_one.trans_le hy1
  have hinv : (x⁻¹) ^ k = y⁻¹ := by rw [inv_pow]
  rw [hinv] at hk'
  have h1 : (|M| + C) * d < c₀ * y := by
    have := mul_lt_mul_of_pos_right hk' hy0
    rwa [mul_assoc, inv_mul_cancel₀ hy0.ne', mul_one] at this
  have hexp : Real.exp (Real.log x * U) ≤ y := by
    calc Real.exp (Real.log x * U) ≤ Real.exp (Real.log x * k) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hk (Real.log_pos hx1).le)
      _ = y := by rw [mul_comm, Real.exp_nat_mul, Real.exp_log hx0]
  have hek : e₁ ^ k = y ^ 2 * d ^ k := by
    rw [he₁x, hy]; ring
  have hdk : 0 < d ^ k := pow_pos hd k
  rw [← add_div, div_lt_div_iff₀ (pow_pos he₁ k) (pow_pos hd (k + 1)), hek, pow_succ]
  have hM : M ≤ |M| := le_abs_self M
  have hMn : 0 ≤ |M| := abs_nonneg M
  have h2 : (M + C * Real.exp (Real.log x * U)) * d ≤ (|M| + C) * d * y := by
    have : M + C * Real.exp (Real.log x * U) ≤ (|M| + C) * y := by nlinarith
    calc (M + C * Real.exp (Real.log x * U)) * d ≤ ((|M| + C) * y) * d :=
          mul_le_mul_of_nonneg_right this hd.le
      _ = (|M| + C) * d * y := by ring
  have h3 : (M + C * Real.exp (Real.log x * U)) * d < c₀ * y ^ 2 := by
    calc (M + C * Real.exp (Real.log x * U)) * d ≤ (|M| + C) * d * y := h2
      _ < c₀ * y * y := mul_lt_mul_of_pos_right h1 hy0
      _ = c₀ * y ^ 2 := by ring
  calc (M + C * Real.exp (Real.log x * U)) * (d ^ k * d)
      = ((M + C * Real.exp (Real.log x * U)) * d) * d ^ k := by ring
    _ < (c₀ * y ^ 2) * d ^ k := mul_lt_mul_of_pos_right h3 hdk
    _ = c₀ * (y ^ 2 * d ^ k) := by ring

/-- Choice of the abscissa `σ` and, for each late window start `U`, of the index `k`
and the Chernoff tilts `t`, `t'`. -/
theorem params {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) :
    ∃ σ : ℝ, 2 < σ ∧ ∀ U : ℝ, 1 ≤ U → ∃ k : ℕ, U ≤ k ∧ ∃ t t' : ℝ, 0 < t ∧ 0 < t' ∧
      t' < σ - 2 ∧
      Real.exp (t * U) * (σ - θ) ^ k ≤ (σ - 2 + t) ^ (k + 1) ∧
      Real.exp (-t' * ((1 + δ) * U)) * (σ - θ) ^ k ≤ (σ - 2 - t') ^ (k + 1) := by
  set τ : ℝ := δ / (2 * (2 + δ)) with hτ
  have hτ0 : 0 < τ := by positivity
  have hτδ : τ * (2 + δ) = δ / 2 := by rw [hτ]; field_simp
  have hτ1 : τ < 1 / 2 := by
    rw [hτ, div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  set m : ℝ := (1 + δ) * (1 - τ) with hm
  set n : ℝ := 1 + τ with hn
  have hmn : m - n = δ / 2 := by rw [hm, hn]; nlinarith
  have hmn0 : 0 < m - n := by rw [hmn]; positivity
  have hn1 : 1 ≤ n := by rw [hn]; linarith
  have hn0 : 0 < n := by linarith
  have hm0 : 0 < m := by linarith
  set w : ℝ := 2 - θ with hw
  set X : ℝ := (2 * (m + n) + 1) / (m - n) + 2 with hX
  have hXmn : X * (m - n) = 2 * (m + n) + 1 + 2 * (m - n) := by
    rw [hX]; field_simp
  have hX2 : 2 < X := by
    rw [hX]
    have : 0 < (2 * (m + n) + 1) / (m - n) := by positivity
    linarith
  set A : ℝ := X / τ with hA
  have hAτ : A * τ = X := by rw [hA]; field_simp
  have hXA : X < A := by
    rw [hA, lt_div_iff₀ hτ0]; nlinarith
  have hA1 : 1 ≤ A := by linarith
  have hA0 : 0 < A := by linarith
  refine ⟨A + θ, by linarith, fun U hU => ?_⟩
  set t : ℝ := X + w with ht
  set t' : ℝ := X - w with ht'
  have ht0 : 0 < t := by rw [ht, hw]; linarith
  have ht1 : 1 ≤ t := by rw [ht, hw]; linarith
  have ht'0 : 0 < t' := by rw [ht', hw]; linarith
  have hκ : 1 ≤ t' * m - t * n := by
    have : t' * m - t * n = X * (m - n) - w * (m + n) := by rw [ht, ht']; ring
    rw [this, hXmn]
    have hw2 : w < 2 := by rw [hw]; linarith
    nlinarith
  have hU0 : 0 < U := by linarith
  have hx0 : 0 ≤ t * U * n / τ := by positivity
  refine ⟨⌈t * U * n / τ⌉₊, ?_, t, t', ht0, ht'0, ?_, ?_, ?_⟩
  · refine le_trans ?_ (Nat.le_ceil _)
    rw [le_div_iff₀ hτ0]
    have h1 : U * τ ≤ U * 1 := mul_le_mul_of_nonneg_left (by linarith) hU0.le
    have h2 : U * 1 ≤ t * U * n := by nlinarith [mul_le_mul ht1 hn1 zero_le_one ht0.le]
    linarith
  · rw [ht', hw]; linarith
  · -- lower tail
    set k : ℕ := ⌈t * U * n / τ⌉₊ with hk
    have hk1 : t * U * n / τ ≤ k := Nat.le_ceil _
    have e1 : A + θ - 2 + t = A * n := by rw [ht, hw, hn, mul_add, hAτ]; ring
    have e2 : A + θ - θ = A := by ring
    rw [e1, e2]
    have hnexp : Real.exp (τ / n) ≤ n := by
      have h := Real.add_one_le_exp (-(τ / n))
      have h' : -(τ / n) + 1 = n⁻¹ := by rw [hn]; field_simp; ring
      rw [h', Real.exp_neg] at h
      exact (inv_le_inv₀ hn0 (Real.exp_pos _)).1 h
    have h1 : Real.exp (t * U) ≤ n ^ k := by
      calc Real.exp (t * U) ≤ Real.exp (k * (τ / n)) := by
            apply Real.exp_le_exp.2
            have : t * U = (t * U * n / τ) * (τ / n) := by field_simp
            rw [this]
            exact mul_le_mul_of_nonneg_right hk1 (by positivity)
        _ = Real.exp (τ / n) ^ k := Real.exp_nat_mul _ _
        _ ≤ n ^ k := pow_le_pow_left₀ (Real.exp_pos _).le hnexp k
    have hAn : 1 ≤ A * n := by nlinarith
    calc Real.exp (t * U) * A ^ k ≤ n ^ k * A ^ k :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (A * n) ^ k := by rw [mul_pow, mul_comm]
      _ ≤ (A * n) ^ (k + 1) := pow_le_pow_right₀ hAn (Nat.le_succ k)
  · -- upper tail
    set k : ℕ := ⌈t * U * n / τ⌉₊ with hk
    have hk2 : (k : ℝ) < t * U * n / τ + 1 := Nat.ceil_lt_add_one hx0
    have e1 : A + θ - 2 - t' = A * (1 - τ) := by rw [ht', hw, mul_sub, hAτ]; ring
    have e2 : A + θ - θ = A := by ring
    rw [e1, e2]
    have h1τ : 0 < 1 - τ := by linarith
    have hexp : Real.exp (-(τ / (1 - τ))) ≤ 1 - τ := by
      have h := Real.add_one_le_exp (τ / (1 - τ))
      have h' : τ / (1 - τ) + 1 = (1 - τ)⁻¹ := by field_simp; ring
      rw [h'] at h
      rw [Real.exp_neg]
      exact inv_le_of_inv_le₀ h1τ h
    have hkτ : ((k : ℝ) + 1) * τ ≤ t' * m * U := by
      have h1 : ((k : ℝ) + 1) * τ < (t * U * n / τ + 2) * τ :=
        mul_lt_mul_of_pos_right (by linarith) hτ0
      have h2 : (t * U * n / τ + 2) * τ = t * U * n + 2 * τ := by field_simp
      have h3 : (t' * m - t * n) * U ≥ 1 := by nlinarith
      nlinarith
    have h1 : Real.exp (-t' * ((1 + δ) * U)) ≤ (1 - τ) ^ (k + 1) := by
      calc Real.exp (-t' * ((1 + δ) * U))
          ≤ Real.exp (((k + 1 : ℕ) : ℝ) * (-(τ / (1 - τ)))) := by
            apply Real.exp_le_exp.2
            have h4 : ((k : ℝ) + 1) * (τ / (1 - τ)) ≤ t' * ((1 + δ) * U) := by
              rw [← mul_div_assoc, div_le_iff₀ h1τ]
              calc ((k : ℝ) + 1) * τ ≤ t' * m * U := hkτ
                _ = t' * ((1 + δ) * U) * (1 - τ) := by rw [hm]; ring
            push_cast
            linarith
        _ = Real.exp (-(τ / (1 - τ))) ^ (k + 1) := Real.exp_nat_mul _ _
        _ ≤ (1 - τ) ^ (k + 1) := pow_le_pow_left₀ (Real.exp_pos _).le hexp _
    calc Real.exp (-t' * ((1 + δ) * U)) * A ^ k ≤ (1 - τ) ^ (k + 1) * A ^ k :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ (1 - τ) ^ (k + 1) * A ^ (k + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA1 (Nat.le_succ k)) (by positivity)
      _ = (A * (1 - τ)) ^ (k + 1) := by rw [mul_pow, mul_comm]

/-- A uniform gap separating a strictly nearest point of a finite set from the others. -/
theorem exists_gap {F : Set ℂ} (hF : F.Finite) (q ρ₁ : ℂ) {r : ℝ} (hr : dist q ρ₁ < r)
    (h : ∀ ρ ∈ F, ρ ≠ ρ₁ → dist q ρ₁ < dist q ρ) :
    ∃ e : ℝ, dist q ρ₁ < e ∧ e ≤ r ∧ ∀ ρ ∈ F, ρ ≠ ρ₁ → e ≤ dist q ρ := by
  have hG : (F \ {ρ₁}).Finite := hF.subset Set.sdiff_subset
  rcases (F \ {ρ₁}).eq_empty_or_nonempty with hE | hne
  · refine ⟨r, hr, le_rfl, fun ρ hρ hne => ?_⟩
    have : ρ ∈ F \ {ρ₁} := ⟨hρ, hne⟩
    rw [hE] at this
    exact absurd this (Set.notMem_empty _)
  · obtain ⟨a, ha, hmin⟩ := Set.exists_min_image (F \ {ρ₁}) (dist q) hG hne
    refine ⟨min r (dist q a), lt_min hr (h a ha.1 ha.2), min_le_left _ _, fun ρ hρ hne => ?_⟩
    exact (min_le_right _ _).trans (hmin ρ ⟨hρ, hne⟩)

end IndependentLandau
