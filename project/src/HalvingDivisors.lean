import HalvingIntervals

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset ArithmeticFunction RiemannReduction.ThirdBridge
open scoped ArithmeticFunction.Moebius

def layerDivisors (b n j i : ℕ) : Finset ℕ :=
  Ioc (max b (bandLo n j)/2^i) (bandHi n j/2^i)

def layerTerm (n i d : ℕ) : ℝ :=
  (μ d:ℝ)*surviving ((n:ℝ)^4/(2:ℝ)^i/d)

theorem clipped_net_sum_terms (b n j i : ℕ) :
    clippedBandNet b n j i = ∑ d ∈ layerDivisors b n j i, layerTerm n i d := rfl

/-- Halving an even index moves it to the next depth of exactly the
same clipped bin, with the integer endpoints rounded as in the original sum. -/
theorem double_row_at_next_depth (b n j i d : ℕ) :
    2*d ∈ layerDivisors b n j i ↔ d ∈ layerDivisors b n j (i+1) := by
  simp only [layerDivisors,mem_Ioc,pow_succ,←Nat.div_div_eq_div_mul]
  omega

/-- Inside a single depth of a dyadic divisor bin, the largest permitted
index is strictly below twice every permitted index. -/
theorem layer_divisors_lt_double {b n j i d e : ℕ}
    (hd : d ∈ layerDivisors b n j i) (he : e ∈ layerDivisors b n j i) : e < 2*d := by
  have ip : 0<(2:ℕ)^i := by positivity
  have jp : 0<(2:ℕ)^j := by positivity
  have lo := (Nat.div_lt_iff_lt_mul ip).mp (mem_Ioc.mp hd).1
  have lower : n^4/2^(j+1) < d*2^i :=
    (le_max_right _ _).trans_lt ((le_max_right b (bandLo n j)).trans_lt lo)
  have low := (Nat.div_lt_iff_lt_mul (by positivity : 0<(2:ℕ)^(j+1))).mp lower
  have hi := (Nat.le_div_iff_mul_le ip).mp (mem_Ioc.mp he).2
  have high := (Nat.le_div_iff_mul_le jp).mp (hi.trans (min_le_right ..))
  by_contra! large
  have scaled := Nat.mul_le_mul_right (2^j) (Nat.mul_le_mul_right (2^i) large)
  rw [pow_succ (2:ℕ) j] at low
  nlinarith only [low,high,scaled]

theorem doubled_divisor_absent {b n j i d : ℕ} (hd : d ∈ layerDivisors b n j i)
    (r : ℕ) (hr : 1≤r) : 2^r*d ∉ layerDivisors b n j i := by
  intro he
  have p : (2:ℕ)≤2^r := by simpa using Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hr
  exact (not_lt_of_ge (Nat.mul_le_mul_right d p)) (layer_divisors_lt_double hd he)

/-- The Möbius sign really does cancel for an odd index and its double.
The two terms occur at different depths and have exactly the same kernel argument. -/
theorem odd_double_cancels_across_depths (n i d : ℕ) (hd : Odd d) :
    layerTerm n i (2*d) + layerTerm n (i+1) d = 0 := by
  have sign : (μ (2*d):ℝ) = -(μ d:ℝ) := by
    rw [isMultiplicative_moebius.map_mul_of_coprime hd.coprime_two_left,
      moebius_apply_prime Nat.prime_two]
    push_cast
    ring
  unfold layerTerm
  simp only [sign,Nat.cast_mul,Nat.cast_ofNat,pow_succ,div_div,mul_assoc]
  ring

end RiemannReduction.ShortTail.LossFrequency
