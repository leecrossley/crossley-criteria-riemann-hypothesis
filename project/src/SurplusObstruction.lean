import SurplusAllocation

/-! The selected surplus alone cannot cover the unused negative terms, even
with divisible payments chosen independently at every sample. -/

noncomputable section
namespace RiemannReduction.ShortTail.SignPairs
open Finset Filter Real RiemannGaussian.AlpogeMined
open scoped ArithmeticFunction.Moebius

def selectedGain (n : ℕ) : ℝ := ∑ r ∈ cofactors n, term n (leftIndex r)

private theorem credit_eq_selected_sub_paid (n : ℕ) : credit n = selectedGain n - paid n := by
  simp [credit,selectedGain,paid,sum_add_distrib]

/-- Spending the credit against gross debt is the same as subtracting all
selected positive rows from the negative mass of the entire retained sum. -/
theorem credit_account {n : ℕ} (hn : 100000 ≤ n) :
    unusedDebt n - credit n = negativeTerms n - selectedGain n := by
  have selectedDebt : ∑ d ∈ selected n, debt n d = paid n := by
    unfold selected paid
    rw [sum_biUnion (disjoint_pairs n)]
    apply sum_congr rfl
    intro r hr
    obtain ⟨neg,pos⟩ := pair_credit hn hr
    have sep : leftIndex r ≠ rightIndex r := by
      intro eqn
      rw [eqn] at pos
      linarith only [neg,pos]
    have l : -term n (leftIndex r) ≤ 0 := by linarith only [neg,pos]
    have h : 0 ≤ -term n (rightIndex r) := by linarith only [neg]
    simp [pair,sep,debt,max_eq_right l,max_eq_left h]
  have total : unusedDebt n + paid n = negativeTerms n := by
    rw [←selectedDebt]
    exact sum_sdiff (selected_inside hn)
  linarith only [total,credit_eq_selected_sub_paid n]

private theorem weight_upper {z : ℝ} (lo : 9/8 ≤ z) (hi : z ≤ 5/4) : weight z ≤ 2 := by
  have one : 1 ≤ z := by linarith
  have logtwo := log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  have coef : 2*(1-eulerMascheroniConstant)+4*log 2+1 ≤ 8 := by
    linarith [one_half_lt_eulerMascheroniConstant]
  have a := mul_le_mul_of_nonneg_left coef (sub_nonneg.mpr one)
  have b := mul_nonpos_of_nonpos_of_nonneg (show 3-4*z ≤ 0 by linarith) (log_nonneg one)
  unfold weight
  rw [fixedBandHalfKernel_second one (by linarith)]
  linarith only [a,b,hi]

theorem selected_gain_upper {n : ℕ} (hn : 100000 ≤ n) : selectedGain n ≤ (n:ℝ)^4/95000 := by
  have each (r : ℕ) (hr : r ∈ cofactors n) : term n (leftIndex r) ≤ 2 := by
    have hf : leftFactor r ∈ ({389,391,397}:Finset ℕ) := by
      unfold leftFactor
      split <;> decide
    have z := z_bounds (by omega : 0 < n) (in_shell hn (cofactor_data hr).1 hf)
    rw [term_eq,(mobius_pair_signs hr).1,Int.cast_one,one_mul]
    exact weight_upper z.1 z.2
  have size : (cofactors n).card ≤ scale n := by
    have sub : cofactors n ⊆ band n := fun _ h => (cofactor_data h).1
    simpa [band] using card_le_card sub
  have cap : (scale n:ℝ)*190000 ≤ (n:ℝ)^4 := by exact_mod_cast (scale_bounds n).1
  have est := sum_le_sum (s:=cofactors n) each
  change selectedGain n ≤ _ at est
  simp only [sum_const,nsmul_eq_mul] at est
  linarith only [est, Nat.cast_le (α:=ℝ).mpr size,cap]

private theorem core_absolute_at_sample :
    ∀ᶠ n : ℕ in atTop, (n:ℝ)^4/4000 ≤ coreAbs n := by
  have grow := (tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 4000
  filter_upwards [early_window_subpower (1/2) (by norm_num),grow,eventually_ge_atTop (32:ℕ)]
    with n earlyBound big hn
  change 4000 ≤ sqrt (n:ℝ) at big
  have np : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have member : n ∈ Icc n (n^2) := mem_Icc.mpr ⟨le_rfl,Nat.le_self_pow (by decide) _⟩
  have one : earlyAbs n/(n:ℝ)^3 ≤ window earlyAbs n :=
    single_le_sum (f:=fun k : ℕ => earlyAbs k/(k:ℝ)^3)
      (fun k _ => div_nonneg (sum_nonneg fun _ _ => abs_nonneg _) (by positivity)) member
  have point := one.trans earlyBound
  rw [←sqrt_eq_rpow] at point
  have rt : sqrt (n:ℝ) ≤ (n:ℝ)/4000 := by
    nlinarith only [mul_le_mul_of_nonneg_right big (sqrt_nonneg (n:ℝ)),sq_sqrt np.le]
  have small := ((div_le_iff₀ (pow_pos np 3)).mp point).trans
    (mul_le_mul_of_nonneg_right rt (by positivity : 0 ≤ (n:ℝ)^3))
  linarith only [small,absolute_split n,fixedBandHalfTail_absolute_lower hn]

/-- A positive fraction of n⁴ is left if the only money is the selected surplus. -/
theorem surplus_alone_at_sample :
    ∀ᶠ n : ℕ in atTop, (n:ℝ)^4/10000 ≤ unusedDebt n - credit n := by
  filter_upwards [core_absolute_at_sample,payment_at_each_sample 1 zero_lt_one,
    eventually_ge_atTop (100000:ℕ)] with n raw net hn
  have paid0 := (show 0 ≤ (n:ℝ)^4 / 20000000 by positivity).trans (covered_weight hn).1
  have hc : credit n ≤ selectedGain n := by
    linarith only [paid0,credit_eq_selected_sub_paid n]
  have coreUpper : core n ≤ credit n := by
    rw [one_mul] at net
    have l := (abs_le.mp net).1
    linarith only [decompose hn,l]
  have split : coreAbs n = core n + 2*negativeTerms n := by
    unfold coreAbs core negativeTerms
    rw [mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro d _
    by_cases h : 0 ≤ term n d
    · simp [abs_of_nonneg h,max_eq_right (neg_nonpos.mpr h)]
    · have h' := le_of_not_ge h
      rw [abs_of_nonpos h',max_eq_left (neg_nonneg.mpr h')]
      ring
  rw [credit_account hn]
  linarith only [raw,hc,coreUpper,split,selected_gain_upper hn,show 0 ≤ (n:ℝ)^4 by positivity]

/-- No payment plan restricted to C_n can improve the preceding bound. -/
theorem all_surplus_only_payments :
    ∀ᶠ n : ℕ in atTop, ∀ p, feasible n (credit n) p → (n:ℝ)^4/10000 ≤ unpaid n p := by
  filter_upwards [surplus_alone_at_sample] with n lo p hp
  unfold unpaid
  rw [sum_sub_distrib]
  exact lo.trans (sub_le_sub_left hp.2 _)

private theorem window_indices {m : ℕ} (hm : 2 ≤ m) : (m:ℝ)^4/4 ≤ ∑ n ∈ Icc m (m^2), (n:ℝ) := by
  let M := m^2
  have low : m ≤ M/2 := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    ((Nat.mul_le_mul_left m hm).trans_eq (by simp [M,pow_two]))
  have sub : Ioc (M/2) M ⊆ Icc m M := fun _ h =>
    mem_Icc.mpr ⟨low.trans (mem_Ioc.mp h).1.le,(mem_Ioc.mp h).2⟩
  have count : (M:ℝ)/2 ≤ ((Ioc (M/2) M).card:ℝ) := by
    rw [Nat.card_Ioc]
    have h : (M:ℝ) ≤ 2*((M-M/2:ℕ):ℝ) := by exact_mod_cast (show M ≤ 2*(M-M/2) by omega)
    linarith
  calc
    (m:ℝ)^4/4 = ((M:ℝ)/2)*((M:ℝ)/2) := by dsimp [M]; push_cast; ring
    _ ≤ ((Ioc (M/2) M).card:ℝ)*((M:ℝ)/2) := mul_le_mul_of_nonneg_right count (by positivity)
    _ = ∑ _n ∈ Ioc (M/2) M, (M:ℝ)/2 := by simp
    _ ≤ ∑ n ∈ Ioc (M/2) M, (n:ℝ) := by
      apply sum_le_sum
      intro n hn
      have h := (mem_Ioc.mp hn).1
      have h' : (M:ℝ) ≤ 2*(n:ℝ) := by exact_mod_cast (show M ≤ 2*n by omega)
      linarith
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg sub fun n _ _ => Nat.cast_nonneg n

/-- The obstruction holds on every sufficiently late complete square block,
uniformly over the choices of individual payments at all samples. -/
theorem surplus_alone_on_blocks :
    ∀ᶠ m : ℕ in atTop, ∀ p : ℕ → ℕ → ℝ,
      (∀ n ∈ Icc m (m^2), feasible n (credit n) (p n)) →
      (m:ℝ)^4/40000 ≤ window (fun n => unpaid n (p n)) m := by
  obtain ⟨A,hA⟩ := eventually_atTop.mp all_surplus_only_payments
  filter_upwards [eventually_ge_atTop A,eventually_ge_atTop (2:ℕ)] with m hm hm2 p legal
  calc
    (m:ℝ)^4/40000 = ((m:ℝ)^4/4)/10000 := by ring
    _ ≤ (∑ n ∈ Icc m (m^2), (n:ℝ))/10000 := div_le_div_of_nonneg_right (window_indices hm2) (by norm_num)
    _ = ∑ n ∈ Icc m (m^2), (n:ℝ)/10000 := sum_div ..
    _ ≤ _ := by
      apply sum_le_sum
      intro n hn
      have mn := (mem_Icc.mp hn).1
      have np : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
      apply (le_div_iff₀ (pow_pos np 3)).mpr
      exact (show (n:ℝ)/10000*(n:ℝ)^3=(n:ℝ)^4/10000 by ring).le.trans
        (hA n (hm.trans mn) (p n) (legal n hn))

/-- For each exponent below four, every sufficiently late block fails
for every rule whose only budget at a sample is the selected surplus. -/
theorem surplus_alone_exceeds {ε : ℝ} (he : ε < 4) :
    ∀ᶠ m : ℕ in atTop, ∀ p : ℕ → ℕ → ℝ,
      (∀ n ∈ Icc m (m^2), feasible n (credit n) (p n)) →
      (m:ℝ)^ε < window (fun n => unpaid n (p n)) m := by
  have grow := ((tendsto_rpow_atTop (sub_pos.mpr he)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_gt_atTop 40000
  filter_upwards [surplus_alone_on_blocks,grow,eventually_ge_atTop (1:ℕ)] with m bound large one p legal
  change 40000 < (m:ℝ)^(4-ε) at large
  have mp : 0 < (m:ℝ) := Nat.cast_pos.mpr (by omega)
  have eqn : (m:ℝ)^(4-ε)*(m:ℝ)^ε = (m:ℝ)^4 := by
    rw [←rpow_add mp,sub_add_cancel]
    norm_cast
  have h := mul_lt_mul_of_pos_right large (rpow_pos_of_pos mp ε)
  rw [eqn] at h
  linarith only [h,bound p legal]

end RiemannReduction.ShortTail.SignPairs
