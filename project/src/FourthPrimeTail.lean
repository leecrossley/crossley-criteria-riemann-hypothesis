import AnchorIdentity
import FourthPowerSparseRH
import Mathlib.NumberTheory.Chebyshev

open Finset IndependentLandau
open scoped ArithmeticFunction.vonMangoldt

noncomputable section
namespace FourthPrimeTail
open SparseAnchor
open FourthPowerSparseRH

def primeLog (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

/-- The ordinary-prime deficit above the square root at the actual fourth-power sample. -/
def tail (k : ℕ) : ℝ :=
  ∑ n ∈ Ioc (k ^ 2) (k ^ 4), (1 - primeLog n) * weight (k ^ 4) n

private theorem primeLog_bounds (n : ℕ) : 0 ≤ primeLog n ∧ primeLog n ≤ Λ n := by
  by_cases p : n.Prime
  · rw [primeLog, if_pos p, ArithmeticFunction.vonMangoldt_apply_prime p]
    exact ⟨Real.log_nonneg (by exact_mod_cast p.one_lt.le), le_rfl⟩
  · simp [primeLog, p, ArithmeticFunction.vonMangoldt_nonneg]

private theorem fourth_center {k : ℕ} (hk : 1 ≤ k) :
    |rampG ((k : ℝ) ^ 4) - deficit (k ^ 4) 0| ≤ 6 * (k : ℝ) ^ 2 := by
  have kp : 0 < k := by omega
  have kr : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have fact : k ^ 2 * k ^ 2 = k ^ 4 := (pow_add k 2 2).symm
  have center := weight_center (u := k ^ 2) (v := k ^ 2) (pow_pos kp 2) (pow_pos kp 2)
  simp only [fact, Nat.cast_pow] at center
  have lg := logError_bounds (X := k ^ 4) (one_le_pow₀ hk)
  have one : 1 ≤ (k : ℝ) ^ 2 := one_le_pow₀ kr
  have linear : (k : ℝ) ≤ (k : ℝ) ^ 2 := le_self_pow₀ kr (by decide)
  have logk := Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one kr)
  rw [← Nat.cast_pow k 4, ramp_identity]
  apply (abs_add_le _ _).trans
  rw [abs_of_nonneg (by linarith only [lg.1] : 0 ≤ logError (k ^ 4))]
  have upper := lg.2
  simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at upper ⊢
  linarith only [center, upper, one, linear, logk]

private theorem chebyshev_remainder (X : ℕ) :
    Chebyshev.psi X - Chebyshev.theta X ≤ 21 * Real.sqrt X := by
  have term (j : ℝ) (hj : 2 ≤ j) :
      Chebyshev.psi ((X : ℝ) ^ (1 / j)) ≤ 7 * Real.sqrt X := by
    have est := Chebyshev.psi_le_const_mul_self (x := (X : ℝ) ^ (1 / j)) (by positivity)
    have log4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    have exp : 1 / j ≤ (1 / 2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hj
    by_cases hX : X = 0
    · subst X
      have pos : 0 < 1 / j := by positivity
      have zero : ((0 : ℕ) : ℝ) ^ (1/j) = 0 := by simpa using Real.zero_rpow pos.ne'
      rw [zero] at est ⊢
      simpa only [Nat.cast_zero, mul_zero, Real.sqrt_zero] using est
    · have xpos : 1 ≤ (X : ℝ) := by exact_mod_cast (show 1 ≤ X by omega)
      have shell := Real.rpow_le_rpow_of_exponent_le xpos exp
      rw [← Real.sqrt_eq_rpow] at shell
      nlinarith only [est, shell, log4, Real.rpow_nonneg (Nat.cast_nonneg X) (1/j)]
  linarith only [Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi (X : ℝ),
    term 2 le_rfl, term 3 (by norm_num), term 5 (by norm_num)]

private theorem replace_by_primes (X D : ℕ) :
    0 ≤ (∑ n ∈ Ioc D X, (1 - primeLog n) * weight X n) - deficit X D ∧
    (∑ n ∈ Ioc D X, (1 - primeLog n) * weight X n) - deficit X D ≤
      Chebyshev.psi X - Chebyshev.theta X := by
  have same : (∑ n ∈ Ioc D X, (1 - primeLog n) * weight X n) - deficit X D =
      ∑ n ∈ Ioc D X, (Λ n - primeLog n) * weight X n := by
    rw [deficit, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [same]
  constructor
  · exact sum_nonneg fun n hn => mul_nonneg (sub_nonneg.mpr (primeLog_bounds n).2)
      (weight_bounds X ((Nat.zero_le D).trans_lt (mem_Ioc.mp hn).1)).1
  · calc
      _ ≤ ∑ n ∈ Ioc D X, (Λ n - primeLog n) :=
        sum_le_sum fun n hn => mul_le_of_le_one_right (sub_nonneg.mpr (primeLog_bounds n).2)
          (weight_bounds X ((Nat.zero_le D).trans_lt (mem_Ioc.mp hn).1)).2
      _ ≤ ∑ n ∈ Ioc 0 X, (Λ n - primeLog n) := by
        apply sum_le_sum_of_subset_of_nonneg
        · exact Ioc_subset_Ioc_left (Nat.zero_le D)
        · exact fun n _ _ => sub_nonneg.mpr (primeLog_bounds n).2
      _ = _ := by
        rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, sum_filter, ← one_Icc]
        exact sum_congr rfl fun n _ => by
          by_cases p : n.Prime
          · simp [p, primeLog, ArithmeticFunction.vonMangoldt_apply_prime p]
          · simp [p, primeLog]

private theorem head_bound {X D : ℕ} (dX : D ≤ X) :
    |deficit X 0 - deficit X D| ≤ 8 * D := by
  have sumHead : deficit X 0 - deficit X D = ∑ n ∈ Ioc 0 D, (1 - Λ n) * weight X n := by
    unfold deficit
    rw [← sum_Ioc_consecutive _ (Nat.zero_le D) dX, add_sub_cancel_right]
  rw [sumHead]
  calc
    _ ≤ ∑ n ∈ Ioc 0 D, |(1 - Λ n) * weight X n| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Ioc 0 D, (1 + Λ n) := by
      refine sum_le_sum fun n hn => ?_
      have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
      obtain ⟨w0, w1⟩ := weight_bounds X (mem_Ioc.mp hn).1
      rw [abs_mul, abs_of_nonneg w0]
      refine (mul_le_of_le_one_right (abs_nonneg _) w1).trans (abs_le.mpr ⟨?_, ?_⟩) <;>
        linarith only [hΛ]
    _ ≤ _ := by
      have psi : Chebyshev.psi D = ∑ n ∈ Ioc 0 D, Λ n := by
        rw [Chebyshev.psi, Nat.floor_natCast]
      rw [sum_add_distrib, ← psi, ← one_Icc]
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
      have h := Chebyshev.psi_le_const_mul_self (x := (D : ℝ)) (Nat.cast_nonneg D)
      have log4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      nlinarith only [h, log4, Nat.cast_nonneg (α := ℝ) D]

/-- The replacement costs O(√x) uniformly at the actual fourth powers x = k⁴. -/
theorem ramp_tail_error {k : ℕ} (hk : 1 ≤ k) :
    |rampG ((k : ℝ) ^ 4) - tail k| ≤ 35 * (k : ℝ) ^ 2 := by
  have dX : k ^ 2 ≤ k ^ 4 := pow_le_pow_right₀ hk (by decide)
  have head := head_bound dX
  have prime := replace_by_primes (k ^ 4) (k ^ 2)
  have bound := chebyshev_remainder (k ^ 4)
  have sr : Real.sqrt ((k : ℝ) ^ 4) = (k : ℝ) ^ 2 := by
    rw [show (k : ℝ) ^ 4 = ((k : ℝ) ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg _)]
  simp only [Nat.cast_pow, sr] at head bound
  change 0 ≤ tail k - deficit (k ^ 4) (k ^ 2) ∧
    tail k - deficit (k ^ 4) (k ^ 2) ≤ Chebyshev.psi ↑(k ^ 4) - Chebyshev.theta ↑(k ^ 4) at prime
  simp only [Nat.cast_pow] at prime
  exact abs_le.mpr ⟨by linarith only [(abs_le.mp (fourth_center hk)).1, (abs_le.mp head).1, prime.2, bound],
    by linarith only [(abs_le.mp (fourth_center hk)).2, (abs_le.mp head).2, prime.1,
      sq_nonneg (k : ℝ)]⟩

def tailFailures (θ c : ℝ) (L : ℕ) : ℕ :=
  ((Icc (L ^ 2) (L ^ 3)).filter (fun k : ℕ => c * ((k : ℝ) ^ 4) ^ θ < tail k)).card

/-- All comparisons use the same block, with neither endpoints nor samples removed. -/
theorem failure_sandwich {θ c : ℝ} (hθ : 1 / 2 < θ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ L ≥ N,
      fourthPowerFailures θ (2*c) L ≤ tailFailures θ c L ∧
      tailFailures θ c L ≤ fourthPowerFailures θ (c/2) L := by
  obtain ⟨W, room⟩ := ArchiveFreeBadMeasure.eventual_power_absorption hθ (70/c)
  refine ⟨max 1 ⌈W⌉₊, fun L hL => ?_⟩
  have l1 : 1 ≤ L := (le_max_left _ _).trans hL
  have compare (k : ℕ) (hk : k ∈ Icc (L ^ 2) (L ^ 3)) :
      |rampG ((k : ℝ) ^ 4) - tail k| ≤ (c/2) * ((k : ℝ) ^ 4) ^ θ := by
    have lk : L ≤ k := (le_self_pow₀ l1 (by decide : 2 ≠ 0)).trans (mem_Icc.mp hk).1
    have k1 := l1.trans lk
    have kr : 1 ≤ (k : ℝ) := by exact_mod_cast k1
    have wk : (⌈W⌉₊ : ℝ) ≤ k := by
      exact_mod_cast ((le_max_right 1 ⌈W⌉₊).trans (hL.trans lk))
    have wx : W ≤ (k : ℝ) ^ 4 :=
      (Nat.le_ceil W).trans (wk.trans (le_self_pow₀ kr (by decide)))
    have scale : ((k : ℝ) ^ 4) ^ (1 / 2 : ℝ) = (k : ℝ) ^ 2 := by
      rw [← Real.sqrt_eq_rpow, show (k : ℝ) ^ 4 = ((k : ℝ) ^ 2) ^ 2 by ring,
        Real.sqrt_sq (sq_nonneg _)]
    have paid := room _ wx (one_le_pow₀ kr)
    rw [scale] at paid
    refine (ramp_tail_error k1).trans ?_
    calc
      _ = (c/2) * (70/c * (k:ℝ)^2) := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left paid (div_nonneg hc.le (by norm_num))
  unfold fourthPowerFailures tailFailures
  constructor <;> apply card_le_card <;> intro k hk
  · obtain ⟨hk, above⟩ := mem_filter.mp hk
    refine mem_filter.mpr ⟨hk, ?_⟩
    linarith only [above, (abs_le.mp (compare k hk)).2,
      mul_nonneg hc.le (Real.rpow_nonneg (by positivity : 0 ≤ (k:ℝ)^4) θ)]
  · obtain ⟨hk, above⟩ := mem_filter.mp hk
    exact mem_filter.mpr ⟨hk, by linarith only [above, (abs_le.mp (compare k hk)).1]⟩

theorem rh_iff_cofinal_prime_tail {c ε : ℝ} (hc : 0 < c) (he : ε ∈ Set.Ioo (0 : ℝ) 3) :
    RiemannHypothesis ↔ ∀ θ ∈ Set.Ioo (1/2 : ℝ) 1, ∀ A : ℕ, ∃ L ≥ A,
      (tailFailures θ c L : ℝ) ≤ (L : ℝ) ^ (3-ε) := by
  constructor
  · intro rh θ hθ A
    obtain ⟨N, between⟩ := failure_sandwich hθ.1 hc
    obtain ⟨L, big, few⟩ := (rh_iff_fourthPower_sparse_failures_fixed (half_pos hc) he).mp rh
      θ hθ (max A N)
    have count := (between L ((le_max_right _ _).trans big)).2
    exact ⟨L, (le_max_left _ _).trans big, (Nat.cast_le.mpr count).trans few⟩
  · intro h
    apply (rh_iff_fourthPower_sparse_failures_fixed (mul_pos (by norm_num : (0:ℝ)<2) hc) he).mpr
    intro θ hθ A
    obtain ⟨N, between⟩ := failure_sandwich hθ.1 hc
    obtain ⟨L, big, few⟩ := h θ hθ (max A N)
    have count := (between L ((le_max_right _ _).trans big)).1
    exact ⟨L, (le_max_left _ _).trans big, (Nat.cast_le.mpr count).trans few⟩

#print axioms ramp_tail_error
#print axioms rh_iff_cofinal_prime_tail

end FourthPrimeTail
