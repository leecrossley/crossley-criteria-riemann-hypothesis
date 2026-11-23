import FourthPrimeTail

open Finset IndependentLandau
noncomputable section
namespace FourthPrimeTail

def retained (k Y : ℕ) : ℝ :=
  ∑ n ∈ Ioc Y (k ^ 4), (1 - primeLog n) * SparseAnchor.weight (k ^ 4) n

def bandDeficit (k Y : ℕ) : ℝ :=
  ∑ n ∈ Ioc (k ^ 2) Y, (1 - primeLog n)

/-- The right-continuous sawtooth at integer quotients is -1/2. -/
def sawtooth (X n : ℕ) : ℝ := (X : ℝ) / n - ((X / n : ℕ) : ℝ) - 1/2

def oscillatingBand (k Y : ℕ) : ℝ :=
  ∑ n ∈ Ioc (k ^ 2) Y, (1 - primeLog n) * sawtooth (k ^ 4) n

theorem split_at_cutoff {k Y : ℕ} (lo : k ^ 2 ≤ Y) (hi : Y ≤ k ^ 4) :
    tail k = retained k Y + bandDeficit k Y / 2 - oscillatingBand k Y := by
  unfold tail retained bandDeficit oscillatingBand
  rw [← sum_Ioc_consecutive _ lo hi]
  have split :
      (∑ n ∈ Ioc (k ^ 2) Y, (1 - primeLog n) * SparseAnchor.weight (k ^ 4) n) =
        (∑ n ∈ Ioc (k ^ 2) Y, (1 - primeLog n)) / 2 -
        ∑ n ∈ Ioc (k ^ 2) Y, (1 - primeLog n) * sawtooth (k ^ 4) n := by
    rw [div_eq_mul_inv, sum_mul, ← sum_sub_distrib]
    exact sum_congr rfl fun _ _ => by unfold SparseAnchor.weight sawtooth; ring
  rw [split]
  ring

theorem bandDeficit_eq_chebyshev {k Y : ℕ} (lo : k ^ 2 ≤ Y) :
    bandDeficit k Y =
      ((Y : ℝ) - Chebyshev.theta Y) -
      (((k ^ 2 : ℕ) : ℝ) - Chebyshev.theta ((k ^ 2 : ℕ) : ℝ)) := by
  have sumPrime (d : ℕ) : (∑ n ∈ Ioc 0 d, primeLog n) = Chebyshev.theta d := by
    rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, sum_filter,
      ← add_sum_Ioc_eq_sum_Icc (by omega : 0 ≤ d)]
    simp [primeLog]
  have fromZero (d : ℕ) :
      (∑ n ∈ Ioc 0 d, (1 - primeLog n)) = (d : ℝ) - Chebyshev.theta d := by
    rw [sum_sub_distrib, sumPrime, ← SparseAnchor.one_Icc]
    simp
  have partition := sum_Ioc_consecutive (fun n => 1 - primeLog n) (Nat.zero_le (k ^ 2)) lo
  rw [fromZero, ← bandDeficit, fromZero] at partition
  linarith only [partition]

/-- Consumes a bound on the signed oscillating term on the actual finite band. -/
theorem comparison_of_oscillation {k Y : ℕ} (hk : 1 ≤ k)
    (lo : k ^ 2 ≤ Y) (hi : Y ≤ k ^ 4) {A : ℝ} (osc : |oscillatingBand k Y| ≤ A) :
    |rampG ((k : ℝ) ^ 4) - (retained k Y + bandDeficit k Y / 2)| ≤
      35 * (k : ℝ) ^ 2 + A := by
  have eq := split_at_cutoff lo hi
  have old := abs_le.mp (ramp_tail_error hk)
  obtain ⟨down, up⟩ := abs_le.mp osc
  exact abs_le.mpr ⟨by linarith only [eq, old.1, up], by linarith only [eq, old.2, down]⟩

#print axioms split_at_cutoff
#print axioms bandDeficit_eq_chebyshev
#print axioms comparison_of_oscillation

end FourthPrimeTail
