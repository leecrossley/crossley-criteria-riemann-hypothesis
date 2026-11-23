import Mathlib
import IndependentLandau.Defs

/-! The centred ramp sum over prime powers: definitions, measurability and a crude growth bound. -/

open scoped ArithmeticFunction.vonMangoldt
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace IndependentLandau

/-- The centred ramp: Σ_{n ≤ y} Λ(n) (y/n − 1) − y log y + (1 + γ) y, γ Euler's constant. -/
def rampG (y : ℝ) : ℝ :=
  (∑ n ∈ Finset.range (⌊y⌋₊ + 1), Λ n * max (y / n - 1) 0)
    - y * Real.log y + (1 + Real.eulerMascheroniConstant) * y

/-- Zeros of zeta in the open right half-plane. -/
def zetaZeros : Set ℂ := {ρ | 0 < ρ.re ∧ riemannZeta ρ = 0}

/-- A single term of the ramp sum. -/
def rampT (n : ℕ) (y : ℝ) : ℝ := Λ n * max (y / n - 1) 0

/-- The sum part of the ramp. -/
def rampS (y : ℝ) : ℝ := ∑ n ∈ Finset.range (⌊y⌋₊ + 1), rampT n y

lemma rampG_eq (y : ℝ) :
    rampG y = rampS y - y * Real.log y + (1 + Real.eulerMascheroniConstant) * y := rfl

lemma rampT_nonneg (n : ℕ) (y : ℝ) : 0 ≤ rampT n y :=
  mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_max_right _ _)

lemma rampT_zero (y : ℝ) : rampT 0 y = 0 := by simp [rampT]

lemma rampT_eq_zero_of_floor_lt {n : ℕ} {y : ℝ} (h : ⌊y⌋₊ < n) : rampT n y = 0 := by
  have hy : y < n := Nat.lt_of_floor_lt h
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_le _).trans_lt h
  have : y / n - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one hn]; exact hy.le
  simp [rampT, max_eq_right this]

lemma rampS_eq_tsum (y : ℝ) : rampS y = ∑' n, rampT n y := by
  rw [rampS]
  refine (tsum_eq_sum fun n hn => ?_).symm
  apply rampT_eq_zero_of_floor_lt
  simpa [Finset.mem_range, Nat.lt_succ_iff] using hn

lemma rampS_nonneg (y : ℝ) : 0 ≤ rampS y :=
  Finset.sum_nonneg fun n _ => rampT_nonneg n y

lemma rampT_le {n : ℕ} {y : ℝ} (hy : 0 ≤ y) : rampT n y ≤ y := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa [rampT_zero] using hy
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : Λ n ≤ n := by
    refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
    have := Real.log_le_sub_one_of_pos hn'
    linarith
  have h2 : max (y / n - 1) 0 ≤ y / n := by
    refine max_le (by linarith) (div_nonneg hy hn'.le)
  calc rampT n y = Λ n * max (y / n - 1) 0 := rfl
    _ ≤ n * (y / n) := by
        exact mul_le_mul h1 h2 (le_max_right _ _) hn'.le
    _ = y := by field_simp

lemma rampS_le {y : ℝ} (hy : 0 ≤ y) : rampS y ≤ (y + 1) * y := by
  calc rampS y ≤ ∑ _n ∈ Finset.range (⌊y⌋₊ + 1), y :=
        Finset.sum_le_sum fun n _ => rampT_le hy
    _ = ((⌊y⌋₊ : ℝ) + 1) * y := by simp
    _ ≤ (y + 1) * y := by
        have := Nat.floor_le hy
        gcongr

lemma measurable_rampS : Measurable rampS := by
  have h : Measurable (fun p : ℕ × ℝ => ∑ n ∈ Finset.range (p.1 + 1), rampT n p.2) := by
    apply measurable_from_prod_countable_right
    intro k
    show Measurable (fun y : ℝ => ∑ n ∈ Finset.range (k + 1), rampT n y)
    refine Finset.measurable_fun_sum (f := fun n y => rampT n y) _ fun n _ => ?_
    unfold rampT
    exact (((measurable_id.div_const _).sub_const _).max measurable_const).const_mul _
  exact h.comp (Nat.measurable_floor.prodMk measurable_id)

lemma measurable_rampG : Measurable rampG := by
  have : rampG = fun y => rampS y - y * Real.log y + (1 + Real.eulerMascheroniConstant) * y :=
    funext rampG_eq
  rw [this]
  exact (measurable_rampS.sub (measurable_id.mul Real.measurable_log)).add
    (measurable_id.const_mul _)

lemma measurable_rampG_exp : Measurable (fun u : ℝ => rampG (Real.exp u)) :=
  measurable_rampG.comp Real.measurable_exp

lemma abs_rampG_exp_le {u : ℝ} (hu : 0 ≤ u) :
    |rampG (Real.exp u)| ≤ 5 * Real.exp (2 * u) := by
  have hy1 : 1 ≤ Real.exp u := Real.one_le_exp hu
  have huy : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hS0 := rampS_nonneg (Real.exp u)
  have hS := rampS_le (y := Real.exp u) (by linarith)
  have hγ0 := Real.one_half_lt_eulerMascheroniConstant
  have hγ1 := Real.eulerMascheroniConstant_lt_two_thirds
  have he : Real.exp (2 * u) = Real.exp u * Real.exp u := by
    rw [← Real.exp_add]; ring_nf
  rw [rampG_eq, Real.log_exp, he]
  set y := Real.exp u
  set γ := Real.eulerMascheroniConstant
  have hyy : y ≤ y * y := by nlinarith
  have hyu : y * u ≤ y * y := by nlinarith
  have hyu0 : 0 ≤ y * u := by nlinarith
  have hγy : γ * y ≤ y := by nlinarith
  have hγy0 : 0 ≤ γ * y := by nlinarith
  rw [abs_le]
  constructor <;> nlinarith

end IndependentLandau
