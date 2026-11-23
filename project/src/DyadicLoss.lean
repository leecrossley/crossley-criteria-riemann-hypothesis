import PaymentCriterion
import PaymentAtEachTerm

/-! Weak and strong harmonic sums for the actual signed Möbius loss. -/

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Filter Real SignPairs

def excess (n : ℕ) : ℝ := max (-core n) 0
def score (n : ℕ) : ℝ := excess n/(n:ℝ)^2

def frequency (z : ℕ → ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Icc m (m^2), if t < z n then (n:ℝ)⁻¹ else 0

def weighted (z : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ n ∈ Icc m (m^2), z n*(n:ℝ)⁻¹

def sameBlockWeak (z : ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C > (0:ℝ), ∀ A : ℕ, ∃ m ≥ A, ∀ j : ℕ,
    (2:ℝ)^j * frequency z m ((2:ℝ)^j) ≤ C*(m:ℝ)^δ

theorem score_is_paid_loss {n : ℕ} (hn : 100000 ≤ n) :
    score n = unpaid n (allocation n (funds n))/(n:ℝ)^2 := by
  rw [full_payment hn]
  rfl

theorem score_nonneg (n : ℕ) : 0 ≤ score n :=
  div_nonneg (le_max_right _ _) (sq_nonneg _)

theorem weighted_score (m : ℕ) : weighted score m = loss core m := by
  unfold weighted loss window score excess
  apply sum_congr rfl
  intro n _
  dsimp only
  ring_nf

theorem weighted_score_eq_outstanding {m : ℕ} (hm : 100000 ≤ m) : weighted score m = outstanding m := by
  rw [←allocation_window hm,weighted_score]
  unfold loss window
  apply sum_congr rfl
  intro n hn
  dsimp only
  rw [full_payment (hm.trans (mem_Icc.mp hn).1)]

theorem weak_le_weighted {z : ℕ → ℝ} (hz : ∀ n, 0 ≤ z n) (m : ℕ) (t : ℝ) :
    t * frequency z m t ≤ weighted z m := by
  unfold frequency weighted
  rw [mul_sum]
  apply sum_le_sum
  intro n _
  split
  · rename_i h
    exact mul_le_mul_of_nonneg_right h.le (by positivity)
  · simpa only [mul_zero] using mul_nonneg (hz n) (by positivity : 0 ≤ (n:ℝ)⁻¹)

private theorem level_majorant (x : ℝ) (J : ℕ) :
    min x ((2:ℝ)^J) ≤ 1+∑ j ∈ range J, if (2:ℝ)^j < x then (2:ℝ)^j else 0 := by
  induction J with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ,pow_succ]
    by_cases h : (2:ℝ)^j < x
    · rw [if_pos h,min_eq_right h.le] at *
      linarith only [ih,min_le_right x ((2:ℝ)^j*2)]
    · rw [if_neg h,add_zero]
      have hj : x ≤ (2:ℝ)^j := le_of_not_gt h
      rw [min_eq_left hj] at ih
      exact (min_le_left _ _).trans ih

theorem weighted_le_levels (z : ℕ → ℝ) (m J : ℕ)
    (cap : ∀ n ∈ Icc m (m^2), z n ≤ (2:ℝ)^J) :
    weighted z m ≤ (∑ n ∈ Icc m (m^2), (n:ℝ)⁻¹) +
      ∑ j ∈ range J, (2:ℝ)^j * frequency z m ((2:ℝ)^j) := by
  calc
    _ ≤ ∑ n ∈ Icc m (m^2), (1+∑ j ∈ range J, if (2:ℝ)^j < z n then (2:ℝ)^j else 0)*(n:ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      have h := level_majorant (z n) J
      rw [min_eq_left (cap n hn)] at h
      exact mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := by
      simp only [add_mul,one_mul,sum_add_distrib,sum_mul]
      congr 1
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      unfold frequency
      rw [mul_sum]
      apply sum_congr rfl
      intro n _
      split_ifs <;> simp

theorem score_polynomial : ∀ᶠ n : ℕ in atTop, score n ≤ (n:ℝ)^2 := by
  filter_upwards [payment_at_each_sample 1 zero_lt_one,eventually_ge_atTop (100000:ℕ)] with n close hn
  have paid0 := (show 0 ≤ (n:ℝ)^4/20000000 by positivity).trans (covered_weight hn).1
  have cr : credit n = selectedGain n - paid n := by simp [credit,selectedGain,paid,sum_add_distrib]
  have np : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have p := (abs_le.mp close).2
  unfold score excess
  apply (div_le_iff₀ (pow_pos np 2)).mpr
  apply max_le _ (by positivity)
  nlinarith only [p,decompose hn,cr,paid0,selected_gain_upper hn,show 0 ≤ (n:ℝ)^4 by positivity]

end RiemannReduction.ShortTail.LossFrequency
