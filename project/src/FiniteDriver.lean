import FiniteAnnulus

/-! Domination of the frequency by a positive signed annulus on the
finite-height domain. Both sides use the same samples and harmonic weights. -/

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Real RiemannReduction.DivisorBand

def annularScore (n : ℕ) : ℝ := max (annulus n (n^3/1000)) 0/(n:ℝ)^2

theorem finite_frequency_annulus
    (published : ∀ x : ℝ, 1024 ≤ x → x ≤ (FiniteFifth.cap:ℝ)^2 → |D x| < sqrt x/5)
    {m : ℕ} (lo : 100000 ≤ m) (hi : m ≤ 161245) :
    ∀ t : ℝ, 1 ≤ t → frequency score m t ≤ frequency annularScore m (t/2) := by
  intro t ht
  apply sum_le_sum
  intro n hn
  have nl := lo.trans (mem_Icc.mp hn).1
  have nh := (mem_Icc.mp hn).2.trans ((Nat.pow_le_pow_left hi 2).trans (by decide : 161245^2 ≤ (26:ℕ)*10^9))
  have np : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  by_cases hit : t < score n
  · have band := finite_annulus published nl nh ht hit
    have forced : t/2 < annularScore n := (lt_div_iff₀ (pow_pos np 2)).mpr
      ((show t/2*(n:ℝ)^2=t*(n:ℝ)^2/2 by ring).trans_lt (band.trans_le (le_max_left _ _)))
    simp only [if_pos hit,if_pos forced,le_refl]
  · simp only [if_neg hit]
    split <;> positivity

end RiemannReduction.ShortTail.LossFrequency
