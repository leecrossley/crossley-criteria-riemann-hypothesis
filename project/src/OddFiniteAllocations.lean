import OddGeometricBudget

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset

/-- These are exactly the finite comparisons checked by the interval replay. -/
def allocationComparisons : Prop := ∀ n ∈ Icc 16 256,
  separatedScore n ≤ 1 ∧ (geometricEvent n 1 ↔ n=44) ∧ ¬geometricEvent n 2

private theorem geometric_antitone (n : ℕ) {u v : ℝ} (uv : u ≤ v) (hit : geometricEvent n v) :
    geometricEvent n u := by
  obtain ⟨j,hj,jp,h⟩ := hit
  have le : u*(n:ℝ)^2/(2:ℝ)^(j+1) ≤ v*(n:ℝ)^2/(2:ℝ)^(j+1) := by gcongr
  exact ⟨j,hj,jp,h.imp (fun e => e.trans_le (neg_le_neg le)) (fun e => le.trans_lt e)⟩

theorem finite_allocated_frequency (cert : allocationComparisons) (j : ℕ) :
    (2:ℝ)^j*eventMass geometricEvent 16 ((2:ℝ)^j)=(if j=0 then 1/44 else 0) ∧
    frequency separatedScore 16 ((2:ℝ)^j)=0 ∧ frequency score 16 ((2:ℝ)^j)=0 := by
  classical
  have span : (16:ℕ)^2=256 := by decide
  have level : 1≤(2:ℝ)^j := one_le_pow₀ (by norm_num)
  have zero (z : ℕ → ℝ) (cap : ∀ n ∈ Icc 16 256, z n ≤ 1) : frequency z 16 ((2:ℝ)^j)=0 := by
    unfold frequency
    rw [span]
    apply sum_eq_zero
    intro n hn
    exact if_neg (not_lt.mpr ((cap n hn).trans level))
  refine ⟨?_,zero _ (fun _ hn => (cert _ hn).1),zero _ (fun n hn => (score_le_separated n).trans (cert _ hn).1)⟩
  unfold eventMass
  rw [span]
  cases j with
  | zero =>
    simp only [pow_zero,one_mul]
    calc _ = ∑ n ∈ Icc (16:ℕ) 256, if n=44 then (n:ℝ)⁻¹ else 0 := by
                apply sum_congr rfl
                intro n hn
                rw [(cert n hn).2.1]
                split_ifs <;> rfl
         _ = _ := by norm_num [sum_ite_eq']
  | succ j =>
    have high : 2 ≤ (2:ℝ)^(j+1) := by
      rw [pow_succ]
      linarith only [one_le_pow₀ (n:=j) (by norm_num : (1:ℝ)≤2)]
    have empty (n : ℕ) (hn : n ∈ Icc 16 256) : ¬geometricEvent n ((2:ℝ)^(j+1)) := fun hit =>
      (cert n hn).2.2 (geometric_antitone _ high hit)
    rw [sum_eq_zero (fun n hn => if_neg (empty n hn)),mul_zero,if_neg (by omega)]

end RiemannReduction.ShortTail.LossFrequency
