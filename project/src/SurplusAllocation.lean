import PairingAtEachSample

/-! Fractional payments on the unused indices of a single fourth-power sample. -/

noncomputable section
namespace RiemannReduction.ShortTail.SignPairs
open Finset Filter

def unused (n : ℕ) := late n \ selected n
def debt (n d : ℕ) : ℝ := max (-term n d) 0
def unusedDebt (n : ℕ) : ℝ := ∑ d ∈ unused n, debt n d
def unusedGain (n : ℕ) : ℝ := ∑ d ∈ unused n, max (term n d) 0
def funds (n : ℕ) : ℝ := credit n + unusedGain n

theorem unused_balance (n : ℕ) : rest n = unusedGain n - unusedDebt n := by
  unfold rest unusedGain unusedDebt unused debt
  rw [←sum_sub_distrib]
  apply sum_congr rfl
  intro d _
  by_cases h : 0 ≤ term n d
  · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
  · have h' := le_of_not_ge h
    simp [max_eq_right h', max_eq_left (neg_nonneg.mpr h')]

theorem funds_nonneg {n : ℕ} (hn : 100000 ≤ n) : 0 ≤ funds n := by
  have hc := (covered_weight hn).2
  have hg : 0 ≤ unusedGain n := sum_nonneg fun _ _ => le_max_right _ _
  exact add_nonneg ((by positivity : 0 ≤ (n:ℝ)^4 / 1600000000).trans hc) hg

/-- A budget can be split among different amounts at this sample. -/
def feasible (n : ℕ) (budget : ℝ) (p : ℕ → ℝ) : Prop :=
  (∀ d ∈ unused n, 0 ≤ p d ∧ p d ≤ debt n d) ∧ ∑ d ∈ unused n, p d ≤ budget

def unpaid (n : ℕ) (p : ℕ → ℝ) : ℝ := ∑ d ∈ unused n, (debt n d - p d)

def fraction (n : ℕ) (budget : ℝ) : ℝ :=
  if unusedDebt n = 0 then 0 else min (unusedDebt n) budget / unusedDebt n

def allocation (n : ℕ) (budget : ℝ) (d : ℕ) : ℝ := debt n d * fraction n budget

private theorem debt_nonneg (n : ℕ) : 0 ≤ unusedDebt n :=
  sum_nonneg fun _ _ => le_max_right _ _

private theorem fraction_bounds (n : ℕ) {budget : ℝ} (hb : 0 ≤ budget) :
    0 ≤ fraction n budget ∧ fraction n budget ≤ 1 := by
  unfold fraction
  split
  · exact ⟨le_rfl, zero_le_one⟩
  · rename_i h
    have pos := lt_of_le_of_ne (debt_nonneg n) (Ne.symm h)
    exact ⟨div_nonneg (le_min pos.le hb) pos.le,
      (div_le_one pos).mpr (min_le_left _ _)⟩

private theorem total_allocated (n : ℕ) {budget : ℝ} (hb : 0 ≤ budget) :
    ∑ d ∈ unused n, allocation n budget d = min (unusedDebt n) budget := by
  simp only [allocation, ←sum_mul]
  change unusedDebt n * fraction n budget = _
  unfold fraction
  split
  · rename_i h
    simp [h, min_eq_left hb]
  · rename_i h
    field_simp

theorem allocation_feasible (n : ℕ) {budget : ℝ} (hb : 0 ≤ budget) :
    feasible n budget (allocation n budget) := by
  refine ⟨fun d _ => ?_, (total_allocated n hb).le.trans (min_le_right _ _)⟩
  have hd : 0 ≤ debt n d := le_max_right _ _
  obtain ⟨lo,hi⟩ := fraction_bounds n hb
  exact ⟨mul_nonneg hd lo,(mul_le_mul_of_nonneg_left hi hd).trans_eq (mul_one _)⟩

/-- The allocation achieves the least possible unpaid amount at this sample. -/
theorem allocation_optimal (n : ℕ) {budget : ℝ} (hb : 0 ≤ budget) :
    unpaid n (allocation n budget) = max (unusedDebt n-budget) 0 ∧
    ∀ p, feasible n budget p → unpaid n (allocation n budget) ≤ unpaid n p := by
  have bal (p : ℕ → ℝ) : unpaid n p = unusedDebt n - ∑ d ∈ unused n, p d :=
    sum_sub_distrib _ _
  have eqn : unpaid n (allocation n budget) = max (unusedDebt n-budget) 0 := by
    rw [bal, total_allocated n hb]
    by_cases h : unusedDebt n ≤ budget
    · simp [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
    · have h' := le_of_not_ge h
      simp [min_eq_right h', max_eq_left (sub_nonneg.mpr h')]
  refine ⟨eqn,fun p hp => ?_⟩
  rw [bal,bal,total_allocated n hb]
  exact sub_le_sub_left (le_min (sum_le_sum fun d hd => (hp.1 d hd).2) hp.2) _

theorem full_payment {n : ℕ} (hn : 100000 ≤ n) :
    unpaid n (allocation n (funds n)) = max (-core n) 0 := by
  rw [(allocation_optimal n (funds_nonneg hn)).1]
  congr 1
  rw [decompose hn,unused_balance]
  unfold funds
  ring

/-- The actual finite allocation produces exactly the audited net shortfall on a block. -/
theorem allocation_window {m : ℕ} (hm : 100000 ≤ m) :
    window (fun n => unpaid n (allocation n (funds n))) m = outstanding m := by
  unfold window outstanding
  apply sum_congr rfl
  intro n hn
  have h := hm.trans (mem_Icc.mp hn).1
  dsimp only
  rw [full_payment h,decompose h,show -(credit n + rest n) = -rest n - credit n by ring]

end RiemannReduction.ShortTail.SignPairs
