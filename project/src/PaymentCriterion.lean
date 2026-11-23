import SurplusAllocation
import FourthSignedCriterion

/-! Allow the amounts to be split arbitrarily within a sample and a different
choice of payments on each block. The published criterion still applies. -/

noncomputable section
namespace RiemannReduction.ShortTail.SignPairs
open Finset Filter RiemannReduction.DivisorBand.FourthMass

def admitsPayment (m : ℕ) (budget : ℝ) : Prop :=
  ∃ p : ℕ → ℕ → ℝ, (∀ n ∈ Icc m (m^2), feasible n (funds n) (p n)) ∧
    window (fun n => unpaid n (p n)) m ≤ budget

/-- Even a rule chosen after seeing the whole block attains the budget
exactly when the existing signed shortfall attains it. -/
theorem admitsPayment_iff {m : ℕ} (hm : 100000 ≤ m) (budget : ℝ) :
    admitsPayment m budget ↔ outstanding m ≤ budget := by
  rw [←allocation_window hm]
  constructor
  · rintro ⟨p,legal,pass⟩
    apply le_trans _ pass
    apply sum_le_sum
    intro n hn
    have lo := hm.trans (mem_Icc.mp hn).1
    exact div_le_div_of_nonneg_right ((allocation_optimal n (funds_nonneg lo)).2 (p n) (legal n hn)) (by positivity)
  · intro hp
    exact ⟨fun n => allocation n (funds n),
      fun n hn => allocation_feasible n (funds_nonneg (hm.trans (mem_Icc.mp hn).1)),hp⟩

/-- This theorem states the equivalence. It supplies neither direction's premise. -/
theorem rh_iff_cofinal_payments :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∀ A : ℕ, ∃ m ≥ A, admitsPayment m ((m:ℝ)^ε) := by
  have criterion : RiemannHypothesis ↔ cofinalSubpower outstanding :=
    (rh_iff_subpower_quartic_budget (-1) (Or.inr rfl)).trans original_iff_outstanding
  apply criterion.trans
  constructor <;> intro h ε ep A <;>
    obtain ⟨m,large,pass⟩ := h ε ep (max 100000 A) <;>
    have hm := (le_max_left 100000 A).trans large <;>
    refine ⟨m,(le_max_right _ _).trans large,?_⟩
  · exact (admitsPayment_iff hm _).mpr pass
  · exact (admitsPayment_iff hm _).mp pass

end RiemannReduction.ShortTail.SignPairs
