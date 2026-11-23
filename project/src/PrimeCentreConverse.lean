import PrimeCentreRamp

open Finset Filter Set
open IndependentLandau

noncomputable section
namespace PrimeCentreMean

/-- The three-scale prime-power tent identity and `primeSum ≤ primePowerSum` convert a global
two-sided ramp bound `|rampG t| ≤ C * t ^ σ` (`t ≥ 1`) into `excess x ≤ 6 * C * x ^ σ` (`x ≥ 4`). -/
theorem excess_le_of_ramp_bound {C σ x : ℝ} (hC : 0 ≤ C) (hσ : 0 ≤ σ) (hx : 4 ≤ x)
    (hG : ∀ t : ℝ, 1 ≤ t → |rampG t| ≤ C * t ^ σ) :
    excess x ≤ 6 * C * x ^ σ := by
  have hx0 : 0 < x := by linarith
  have h := ThetaTransfer.deficit_eq_centered_ramps (y := x / 4) (by positivity)
  rw [show 4 * (x / 4) = x by ring, show 2 * (x / 4) = x / 2 by ring] at h
  change 2 * Real.log 2 * (x / 4) - ThetaTransfer.primePowerSum (x / 4) =
    -rampG x + 3 * rampG (x / 2) - 2 * rampG (x / 4) at h
  have hlin : 2 * Real.log 2 * (x / 4) = (x / 2) * Real.log 2 := by ring
  rw [hlin] at h
  have hp := ThetaTransfer.primeSum_le_primePowerSum (x / 4)
  have b1 : rampG x ≤ C * x ^ σ := (le_abs_self _).trans (hG x (by linarith))
  have b2 : -rampG (x / 2) ≤ C * x ^ σ := calc
    -rampG (x / 2) ≤ |rampG (x / 2)| := neg_le_abs _
    _ ≤ C * (x / 2) ^ σ := hG (x / 2) (by linarith)
    _ ≤ C * x ^ σ :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith) hσ) hC
  have b4 : rampG (x / 4) ≤ C * x ^ σ := calc
    rampG (x / 4) ≤ |rampG (x / 4)| := le_abs_self _
    _ ≤ C * (x / 4) ^ σ := hG (x / 4) (by linarith)
    _ ≤ C * x ^ σ :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith) hσ) hC
  unfold excess
  apply max_le
  · exact mul_nonneg (by positivity) (Real.rpow_nonneg hx0.le _)
  · linarith only [h, hp, b1, b2, b4]

private def nextPrime (n : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes (n + 1))

private theorem nextPrime_prime (n : ℕ) : (nextPrime n).Prime :=
  (Nat.find_spec (Nat.exists_infinite_primes (n + 1))).2

private theorem lt_nextPrime (n : ℕ) : n < nextPrime n :=
  Nat.lt_of_succ_le (Nat.find_spec (Nat.exists_infinite_primes (n + 1))).1

private theorem nextPrime_gap (n r : ℕ) (hr : r.Prime) : r ≤ n ∨ nextPrime n ≤ r := by
  rcases le_or_gt r n with h | h
  · exact Or.inl h
  · exact Or.inr (Nat.find_min' (Nat.exists_infinite_primes (n + 1)) ⟨h, hr⟩)

private theorem nextPrime_le_two_mul {n : ℕ} (hn : n ≠ 0) : nextPrime n ≤ 2 * n := by
  obtain ⟨q, hq, hnq, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul n hn
  exact (Nat.find_min' (Nat.exists_infinite_primes (n + 1)) ⟨hnq, hq⟩).trans hq2

private def primeSeq (p₀ : ℕ) : ℕ → ℕ
  | 0 => p₀
  | i + 1 => nextPrime (primeSeq p₀ i)

private theorem primeSeq_prime {p₀ : ℕ} (hp₀ : p₀.Prime) (i : ℕ) : (primeSeq p₀ i).Prime := by
  induction i with
  | zero => exact hp₀
  | succ _ ih => exact nextPrime_prime _

private theorem primeSeq_strictMono (p₀ : ℕ) : StrictMono (primeSeq p₀) :=
  strictMono_nat_of_lt_succ fun i => lt_nextPrime (primeSeq p₀ i)

private theorem add_le_primeSeq (p₀ i : ℕ) : p₀ + i ≤ primeSeq p₀ i := by
  induction i with
  | zero => simp [primeSeq]
  | succ i ih =>
    have hlt := lt_nextPrime (primeSeq p₀ i)
    simp only [primeSeq]
    omega

private theorem primeSeq_centre_ge_four {p₀ : ℕ} (hp₀ : p₀.Prime) (i : ℕ) :
    4 ≤ centre (primeSeq p₀ i) := by
  have hr : (2 : ℝ) ≤ primeSeq p₀ i := by exact_mod_cast (primeSeq_prime hp₀ i).two_le
  unfold centre
  linarith

private theorem primeSeq_centre_step {p₀ : ℕ} (hp₀ : p₀.Prime) (i : ℕ) :
    centre (primeSeq p₀ (i + 1)) ≤ 2 * centre (primeSeq p₀ i) := by
  have hle : primeSeq p₀ (i + 1) ≤ 2 * primeSeq p₀ i :=
    nextPrime_le_two_mul (primeSeq_prime hp₀ i).ne_zero
  have hr : (primeSeq p₀ (i + 1) : ℝ) ≤ 2 * (primeSeq p₀ i : ℝ) := by exact_mod_cast hle
  unfold centre
  linarith

private theorem exists_stop_index {p₀ : ℕ} (hp₀ : p₀.Prime) {δ : ℝ} (width : 0 < δ) :
    ∃ k : ℕ, (1 + δ) * Real.log (centre (primeSeq p₀ 0)) ≤
      Real.log (centre (primeSeq p₀ k)) := by
  let target := Real.exp ((1 + δ) * Real.log (centre (primeSeq p₀ 0)))
  refine ⟨⌈target⌉₊, ?_⟩
  have ht_pos : 0 < target := Real.exp_pos _
  have hle_nat : ⌈target⌉₊ ≤ primeSeq p₀ ⌈target⌉₊ := by
    have := add_le_primeSeq p₀ ⌈target⌉₊
    omega
  have hle_centre : target ≤ centre (primeSeq p₀ ⌈target⌉₊) := by
    have h1 : target ≤ (⌈target⌉₊ : ℝ) := Nat.le_ceil target
    have h2 : (⌈target⌉₊ : ℝ) ≤ primeSeq p₀ ⌈target⌉₊ := by exact_mod_cast hle_nat
    have h3 : (0 : ℝ) ≤ primeSeq p₀ ⌈target⌉₊ := Nat.cast_nonneg _
    unfold centre
    linarith
  have _ := hp₀
  have _ := width
  have hlog := Real.log_le_log ht_pos hle_centre
  rwa [Real.log_exp] at hlog

/-- Starting at any prime `p₀`, taking consecutive primes up to the first prime with
`(1 + δ) * log (2 * p₀) ≤ log (2 * p_k)` yields Bertrand step bounds `x_{i+1} ≤ 2 * x_i`,
terminal overshoot `x_k ≤ 2 * x_0 ^ (1 + δ)`, and logarithmic gap sum `≤ δ * log x_0 + log 2`. -/
theorem consecutive_prime_block_of_prime {p₀ : ℕ} (hp₀ : p₀.Prime) {δ : ℝ} (width : 0 < δ) :
    ∃ (p : ℕ → ℕ) (k : ℕ),
      p 0 = p₀ ∧
      0 < k ∧
      (∀ i ≤ k, (p i).Prime) ∧
      (∀ i < k, p i < p (i + 1) ∧ ∀ r : ℕ, r.Prime → r ≤ p i ∨ p (i + 1) ≤ r) ∧
      (∀ i < k, centre (p (i + 1)) ≤ 2 * centre (p i)) ∧
      (1 + δ) * Real.log (centre (p 0)) ≤ Real.log (centre (p k)) ∧
      centre (p k) ≤ 2 * (centre (p 0)) ^ (1 + δ) ∧
      (∑ i ∈ Finset.range k, (Real.log (centre (p (i + 1))) - Real.log (centre (p i)))) =
        Real.log (centre (p k)) - Real.log (centre (p 0)) ∧
      Real.log (centre (p k)) - Real.log (centre (p 0)) ≤
        δ * Real.log (centre (p 0)) + Real.log 2 := by
  classical
  let hex := exists_stop_index hp₀ width
  let k := Nat.find hex
  have hstop : (1 + δ) * Real.log (centre (primeSeq p₀ 0)) ≤ Real.log (centre (primeSeq p₀ k)) :=
    Nat.find_spec hex
  have hc0_ge4 : 4 ≤ centre (primeSeq p₀ 0) := primeSeq_centre_ge_four hp₀ 0
  have hc0_pos : 0 < centre (primeSeq p₀ 0) := by linarith
  have hlog0_pos : 0 < Real.log (centre (primeSeq p₀ 0)) := Real.log_pos (by linarith)
  have hk_ne : k ≠ 0 := by
    intro hk0
    rw [hk0] at hstop
    nlinarith
  obtain ⟨m, hkm⟩ := Nat.exists_eq_succ_of_ne_zero hk_ne
  have hm_lt_k : m < k := by omega
  have hm_lt : Real.log (centre (primeSeq p₀ m)) < (1 + δ) * Real.log (centre (primeSeq p₀ 0)) :=
    not_le.mp (Nat.find_min hex hm_lt_k)
  have hcm_pos : 0 < centre (primeSeq p₀ m) :=
    lt_of_lt_of_le (by norm_num) (primeSeq_centre_ge_four hp₀ m)
  have hck_pos : 0 < centre (primeSeq p₀ k) :=
    lt_of_lt_of_le (by norm_num) (primeSeq_centre_ge_four hp₀ k)
  have hstep_m : centre (primeSeq p₀ k) ≤ 2 * centre (primeSeq p₀ m) := by
    rw [hkm]; exact primeSeq_centre_step hp₀ m
  have hcm_rpow : centre (primeSeq p₀ m) ≤ (centre (primeSeq p₀ 0)) ^ (1 + δ) := by
    rw [← Real.exp_log hcm_pos, Real.rpow_def_of_pos hc0_pos, mul_comm]
    exact Real.exp_le_exp.mpr hm_lt.le
  have hlog_k : Real.log (centre (primeSeq p₀ k)) ≤
      Real.log 2 + Real.log (centre (primeSeq p₀ m)) := by
    rw [← Real.log_mul (by norm_num) hcm_pos.ne']
    exact Real.log_le_log hck_pos hstep_m
  refine ⟨primeSeq p₀, k, rfl, Nat.pos_of_ne_zero hk_ne,
    fun i _ => primeSeq_prime hp₀ i,
    fun i _ => ⟨lt_nextPrime _, fun r hr => nextPrime_gap _ r hr⟩,
    fun i _ => primeSeq_centre_step hp₀ i,
    hstop,
    hstep_m.trans (mul_le_mul_of_nonneg_left hcm_rpow (by norm_num)),
    Finset.sum_range_sub (fun i => Real.log (centre (primeSeq p₀ i))) k,
    by linarith⟩

/-- Constructive consecutive-prime block starting above any requested logarithmic threshold `U₀`. -/
theorem exists_consecutive_prime_block {δ : ℝ} (width : 0 < δ) (U₀ : ℝ) :
    ∃ (p : ℕ → ℕ) (k : ℕ),
      0 < k ∧
      (∀ i ≤ k, (p i).Prime) ∧
      (∀ i < k, p i < p (i + 1) ∧ ∀ r : ℕ, r.Prime → r ≤ p i ∨ p (i + 1) ≤ r) ∧
      (∀ i < k, centre (p (i + 1)) ≤ 2 * centre (p i)) ∧
      U₀ ≤ Real.log (centre (p 0)) ∧
      (1 + δ) * Real.log (centre (p 0)) ≤ Real.log (centre (p k)) ∧
      centre (p k) ≤ 2 * (centre (p 0)) ^ (1 + δ) ∧
      (∑ i ∈ Finset.range k, (Real.log (centre (p (i + 1))) - Real.log (centre (p i)))) =
        Real.log (centre (p k)) - Real.log (centre (p 0)) ∧
      Real.log (centre (p k)) - Real.log (centre (p 0)) ≤
        δ * Real.log (centre (p 0)) + Real.log 2 := by
  obtain ⟨p₀, hp₀_ge, hp₀⟩ := Nat.exists_infinite_primes ⌈Real.exp U₀⌉₊
  obtain ⟨p, k, hp0, hk, hpr, hgap, hstep, hstop, hcap, htele, hspan⟩ :=
    consecutive_prime_block_of_prime hp₀ width
  have hexp : Real.exp U₀ ≤ centre (p 0) := by
    rw [hp0]
    have h1 : Real.exp U₀ ≤ (⌈Real.exp U₀⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.exp U₀⌉₊ : ℝ) ≤ p₀ := by exact_mod_cast hp₀_ge
    have h3 : (0 : ℝ) ≤ p₀ := Nat.cast_nonneg _
    unfold centre
    linarith
  have hU₀ : U₀ ≤ Real.log (centre (p 0)) := by
    have := Real.log_le_log (Real.exp_pos U₀) hexp
    rwa [Real.log_exp] at this
  exact ⟨p, k, hk, hpr, hgap, hstep, hU₀, hstop, hcap, htele, hspan⟩

/-- Zero-freeness of `riemannZeta` in `Re s > θ` (`1/2 ≤ θ < 1`) implies `SmallPrimeCentreBudget θ δ`
at the exact same exponent `θ`, for every positive logarithmic window width `δ`. -/
theorem primeCentreBudget_of_zeroFree {θ δ : ℝ} (half : 1 / 2 ≤ θ) (one : θ < 1)
    (width : 0 < δ) (zeroFree : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) :
    SmallPrimeCentreBudget θ δ := by
  intro ε hε U₀
  have h1δ : 0 < 1 + δ := by linarith
  let η : ℝ := min ((1 - θ) / 2) (ε / (2 * (1 + δ)))
  have hη_pos : 0 < η := lt_min (by linarith) (div_pos hε (by positivity))
  have hθη_lt1 : θ + η < 1 := by
    have hle : η ≤ (1 - θ) / 2 := min_le_left _ _
    linarith
  have hη_prod : η * (1 + δ) ≤ ε / 2 := by
    have hle : η ≤ ε / (2 * (1 + δ)) := min_le_right _ _
    calc η * (1 + δ) ≤ (ε / (2 * (1 + δ))) * (1 + δ) := mul_le_mul_of_nonneg_right hle h1δ.le
      _ = ε / 2 := by field_simp
  obtain ⟨C, hC_pos, hG⟩ :=
    DirectRampEquivalence.abs_rampG_le_of_zeroFree half (by linarith : θ < θ + η) hθη_lt1 zeroFree
  let M : ℝ := 6 * C * Real.exp ((θ + η) * Real.log 2)
  have hM_pos : 0 < M := by dsimp [M]; positivity
  let V : ℝ := max (max U₀ 1) (8 * (δ + 1) * M / ε ^ 2)
  obtain ⟨p, k, _, hprimes, hgaps, hstep, hV_le, hstop, _, htele, hspan⟩ :=
    exists_consecutive_prime_block width V
  have hU₀ : U₀ ≤ Real.log (centre (p 0)) :=
    ((le_max_left U₀ 1).trans (le_max_left _ _)).trans hV_le
  have hu0_ge1 : 1 ≤ Real.log (centre (p 0)) :=
    ((le_max_right U₀ 1).trans (le_max_left _ _)).trans hV_le
  have hu0_quad : 8 * (δ + 1) * M / ε ^ 2 ≤ Real.log (centre (p 0)) :=
    (le_max_right _ _).trans hV_le
  refine ⟨p, k, hprimes, hgaps, hU₀, hstop, ?_⟩
  let u (j : ℕ) : ℝ := Real.log (centre (p j))
  have hc_ge4 (j : ℕ) (hj : j ≤ k) : 4 ≤ centre (p j) := by
    have hr : (2 : ℝ) ≤ p j := by exact_mod_cast (hprimes j hj).two_le
    unfold centre; linarith
  have hc_pos (j : ℕ) (hj : j ≤ k) : 0 < centre (p j) :=
    lt_of_lt_of_le (by norm_num) (hc_ge4 j hj)
  have hp_mono : ∀ a b : ℕ, a ≤ b → b ≤ k → p a ≤ p b := by
    intro a b hab hbk
    induction b with
    | zero =>
      have ha0 : a = 0 := Nat.eq_zero_of_le_zero hab
      subst ha0; exact le_rfl
    | succ b ih =>
      rcases eq_or_lt_of_le hab with rfl | hab_lt
      · exact le_rfl
      · exact (ih (Nat.lt_succ_iff.mp hab_lt) (by omega)).trans
          (hgaps b (Nat.lt_of_succ_le hbk)).1.le
  have hexcess (j : ℕ) (hj : j ≤ k) :
      excess (centre (p j)) ≤ 6 * C * Real.exp ((θ + η) * u j) := by
    have hb := excess_le_of_ramp_bound hC_pos.le (by linarith : 0 ≤ θ + η) (hc_ge4 j hj) hG
    rw [Real.rpow_def_of_pos (hc_pos j hj), mul_comm (Real.log (centre (p j))) (θ + η)] at hb
    exact hb
  have hgap_bound (i : ℕ) (hi : i ∈ Finset.range k) :
      gapCost θ (centre (p i)) (centre (p (i + 1))) ≤
        (u (i + 1) - u i) * (M * Real.exp (η * (1 + δ) * u 0)) := by
    have hik : i < k := Finset.mem_range.mp hi
    have hci_pos := hc_pos i hik.le
    have hci1_pos := hc_pos (i + 1) hik
    have hci_le : centre (p i) ≤ centre (p (i + 1)) := by
      have hr : (p i : ℝ) ≤ p (i + 1) := by exact_mod_cast (hgaps i hik).1.le
      unfold centre; linarith
    have hui_le : u i ≤ u (i + 1) := Real.log_le_log hci_pos hci_le
    have hui1_le_uk : u (i + 1) ≤ u k := by
      apply Real.log_le_log hci1_pos
      have hr : (p (i + 1) : ℝ) ≤ p k := by exact_mod_cast hp_mono (i + 1) k hik le_rfl
      unfold centre; linarith
    have hui_step : u (i + 1) ≤ Real.log 2 + u i := by
      dsimp [u]
      rw [← Real.log_mul (by norm_num) hci_pos.ne']
      exact Real.log_le_log hci1_pos (hstep i hik)
    have hmax : max (excess (centre (p i))) (excess (centre (p (i + 1)))) ≤
        6 * C * Real.exp ((θ + η) * u (i + 1)) := by
      apply max_le
      · exact (hexcess i hik.le).trans (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hui_le (by linarith))) (by positivity))
      · exact hexcess (i + 1) hik
    have hweight : Real.exp (-θ * u i) *
        max (excess (centre (p i))) (excess (centre (p (i + 1)))) ≤
        M * Real.exp (η * (1 + δ) * u 0) := by
      calc
        Real.exp (-θ * u i) * max (excess (centre (p i))) (excess (centre (p (i + 1))))
          ≤ Real.exp (-θ * u i) * (6 * C * Real.exp ((θ + η) * u (i + 1))) :=
            mul_le_mul_of_nonneg_left hmax (Real.exp_pos _).le
        _ = 6 * C * Real.exp (-θ * u i + (θ + η) * u (i + 1)) := by
            rw [Real.exp_add]; ring
        _ ≤ 6 * C * Real.exp ((θ + η) * Real.log 2 + η * (1 + δ) * u 0) := by
            apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by positivity)
            have hθ0 : 0 ≤ θ := by linarith
            have h1 : θ * (u (i + 1) - u i) ≤ θ * Real.log 2 :=
              mul_le_mul_of_nonneg_left (by linarith [hui_step]) hθ0
            have h2 : η * u (i + 1) ≤ η * ((1 + δ) * u 0 + Real.log 2) :=
              mul_le_mul_of_nonneg_left (by linarith [hui1_le_uk, hspan]) hη_pos.le
            linarith
        _ = M * Real.exp (η * (1 + δ) * u 0) := by
            dsimp [M]; rw [Real.exp_add]; ring
    unfold gapCost
    exact mul_le_mul_of_nonneg_left hweight (sub_nonneg.mpr hui_le)
  have hsum : budget θ p k ≤ (u k - u 0) * (M * Real.exp (η * (1 + δ) * u 0)) := by
    unfold budget
    calc ∑ i ∈ Finset.range k, gapCost θ (centre (p i)) (centre (p (i + 1)))
        ≤ ∑ i ∈ Finset.range k, (u (i + 1) - u i) * (M * Real.exp (η * (1 + δ) * u 0)) :=
          Finset.sum_le_sum hgap_bound
      _ = (∑ i ∈ Finset.range k, (u (i + 1) - u i)) * (M * Real.exp (η * (1 + δ) * u 0)) := by
          rw [← Finset.sum_mul]
      _ = (u k - u 0) * (M * Real.exp (η * (1 + δ) * u 0)) := by
          rw [htele]
  have hlog2_le1 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hspan_lin : u k - u 0 ≤ (δ + 1) * u 0 := by
    dsimp [u] at hspan ⊢
    linarith [hu0_ge1, hlog2_le1]
  have habsorb : (u k - u 0) * M ≤ Real.exp ((ε / 2) * u 0) := by
    have hq1 : 8 * (δ + 1) * M ≤ u 0 * ε ^ 2 :=
      (div_le_iff₀ (by positivity : 0 < ε ^ 2)).mp hu0_quad
    have hu0_nn : 0 ≤ u 0 := by dsimp [u]; linarith [hu0_ge1]
    have hprod_nn : 0 ≤ (ε / 2) * u 0 := mul_nonneg (by positivity) hu0_nn
    have hq2 : (δ + 1) * u 0 * M ≤ ((ε / 2) * u 0) ^ 2 / 2 := by
      have := mul_le_mul_of_nonneg_right hq1 hu0_nn
      nlinarith
    have hexp_q := Real.quadratic_le_exp_of_nonneg hprod_nn
    calc (u k - u 0) * M ≤ ((δ + 1) * u 0) * M := mul_le_mul_of_nonneg_right hspan_lin hM_pos.le
      _ ≤ Real.exp ((ε / 2) * u 0) := by linarith [hq2, hexp_q, hprod_nn]
  have hexp_half : Real.exp (η * (1 + δ) * u 0) ≤ Real.exp ((ε / 2) * u 0) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hη_prod (by dsimp [u]; linarith [hu0_ge1])
  calc budget θ p k
      ≤ ((u k - u 0) * M) * Real.exp (η * (1 + δ) * u 0) := by linarith [hsum]
    _ ≤ Real.exp ((ε / 2) * u 0) * Real.exp ((ε / 2) * u 0) :=
        mul_le_mul habsorb hexp_half (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (ε * Real.log (centre (p 0))) := by
        rw [← Real.exp_add]; dsimp [u]; congr 1; ring

/-- **Exact Prime-Centre Budget Equivalence:**
For every `θ ∈ [1/2, 1)` and `δ > 0`, `SmallPrimeCentreBudget θ δ` holds if and only if
`riemannZeta` has no zeros in the open right half-plane `Re s > θ`. -/
theorem smallPrimeCentreBudget_iff_zeroFree {θ δ : ℝ} (half : 1 / 2 ≤ θ) (one : θ < 1)
    (width : 0 < δ) :
    SmallPrimeCentreBudget θ δ ↔ ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 :=
  ⟨fun small => zeroFree_of_excessMean half one width
    (excessMean_of_primeCentreBudget (by linarith) width small),
   primeCentreBudget_of_zeroFree half one width⟩

/-- Continuous-mean counterpart: `SmallExcessMean θ δ` is equivalent to `Re s > θ` being zero-free. -/
theorem smallExcessMean_iff_zeroFree {θ δ : ℝ} (half : 1 / 2 ≤ θ) (one : θ < 1)
    (width : 0 < δ) :
    SmallExcessMean θ δ ↔ ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 :=
  ⟨zeroFree_of_excessMean half one width,
   fun hz => excessMean_of_primeCentreBudget (by linarith) width
     (primeCentreBudget_of_zeroFree half one width hz)⟩

/-- **Riemann Hypothesis Equivalence at `θ = 1/2`:**
For any `δ > 0`, `RiemannHypothesis` is equivalent to `SmallPrimeCentreBudget (1/2) δ`. -/
theorem rh_iff_smallPrimeCentreBudget_half {δ : ℝ} (width : 0 < δ) :
    RiemannHypothesis ↔ SmallPrimeCentreBudget (1 / 2) δ := by
  have hrh : RiemannHypothesis ↔ ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0 :=
    DirectRampEquivalence.rh_iff_ordinaryWindowUnit_above_half.trans
      (DirectRampEquivalence.ordinaryWindow_three_way_iff ⟨le_rfl, by norm_num⟩).1
  exact hrh.trans (smallPrimeCentreBudget_iff_zeroFree le_rfl (by norm_num) width).symm

/-- **Riemann Hypothesis Equivalence Across `(1/2, 1)`:**
For any `δ > 0`, `RiemannHypothesis` is equivalent to `SmallPrimeCentreBudget θ δ` holding for
all `θ ∈ (1/2, 1)`. -/
theorem rh_iff_all_smallPrimeCentreBudget {δ : ℝ} (width : 0 < δ) :
    RiemannHypothesis ↔ ∀ θ ∈ Set.Ioo (1 / 2 : ℝ) 1, SmallPrimeCentreBudget θ δ := by
  have hrh : RiemannHypothesis ↔ ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0 :=
    DirectRampEquivalence.rh_iff_ordinaryWindowUnit_above_half.trans
      (DirectRampEquivalence.ordinaryWindow_three_way_iff ⟨le_rfl, by norm_num⟩).1
  rw [hrh]
  refine ⟨fun hz θ hθ => primeCentreBudget_of_zeroFree hθ.1.le hθ.2 width
    (fun s hs => hz s (hθ.1.trans hs)), fun hall s hs => ?_⟩
  rcases le_or_gt 1 s.re with hs1 | hs1
  · exact riemannZeta_ne_zero_of_one_le_re hs1
  · let θ : ℝ := (1 / 2 + s.re) / 2
    have hθ : θ ∈ Set.Ioo (1 / 2 : ℝ) 1 := ⟨by dsimp [θ]; linarith, by dsimp [θ]; linarith⟩
    exact (smallPrimeCentreBudget_iff_zeroFree hθ.1.le hθ.2 width).mp (hall θ hθ) s
      (by dsimp [θ]; linarith)

end PrimeCentreMean
