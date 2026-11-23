import OddDilation
import OddTailCriterion

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset RiemannReduction.ThirdBridge
open scoped ArithmeticFunction.Moebius

/-- All signed Möbius rows of Sanftenberg's corrected kernel on (a,b]. -/
def intervalNet (x : ℝ) (a b : ℕ) : ℝ :=
  ∑ d ∈ Ioc a b, (μ d:ℝ)*surviving (x/d)

/-- The odd signed rows on the same interval. -/
def intervalOdd (x : ℝ) (a b : ℕ) : ℝ :=
  ∑ d ∈ (Ioc a b).filter (fun r => r%2=1), (μ d:ℝ)*surviving (x/d)

theorem interval_odd_complete (x : ℝ) : intervalOdd x 0 ⌊x/2⌋₊ = completeOddReal x := rfl

/-- An even row and its half evaluate the kernel at the same quotient. -/
theorem interval_odd_halve (x : ℝ) (a b : ℕ) :
    intervalOdd x a b = intervalNet x a b + intervalOdd (x/2) (a/2) (b/2) := by
  have f := fold_signed_rows (Ioc a b) (fun d : ℕ => surviving (x/d))
  simp only [cofactor_interval,Nat.cast_mul,Nat.cast_ofNat,←div_div] at f
  exact eq_add_of_sub_eq (show intervalOdd x a b-intervalOdd (x/2) (a/2) (b/2)=intervalNet x a b from f.symm)

/-- The net on the interval after i halvings of its scale and both endpoints. -/
def halvedNet (x : ℝ) (a b i : ℕ) : ℝ := intervalNet (x/(2:ℝ)^i) (a/2^i) (b/2^i)

theorem interval_odd_telescope (x : ℝ) (a b h : ℕ) :
    intervalOdd x a b = (∑ i ∈ range h, halvedNet x a b i) +
      intervalOdd (x/(2:ℝ)^h) (a/2^h) (b/2^h) := by
  induction h with
  | zero => simp
  | succ h ih =>
    have step := interval_odd_halve (x/(2:ℝ)^h) (a/2^h) (b/2^h)
    simp only [div_div,Nat.div_div_eq_div_mul,←pow_succ] at step
    rw [sum_range_succ]
    change intervalOdd x a b = _ + intervalNet (x/(2:ℝ)^h) (a/2^h) (b/2^h) + _
    linarith only [ih,step]

theorem interval_odd_at_cut (x : ℝ) (a b h : ℕ) (empty : b/2^h=0) :
    intervalOdd x a b = ∑ i ∈ range h, halvedNet x a b i := by
  have cut := interval_odd_telescope x a b h
  rw [empty,show intervalOdd (x/(2:ℝ)^h) (a/2^h) 0=0 by simp [intervalOdd],add_zero] at cut
  exact cut

/-- All interval rows are exhausted after at most 1+floor(log₂ b) steps. -/
theorem interval_odd_log_telescope (x : ℝ) (a b : ℕ) :
    intervalOdd x a b = ∑ i ∈ range (Nat.log 2 b+1), halvedNet x a b i :=
  interval_odd_at_cut x a b _ (Nat.div_eq_of_lt (Nat.lt_pow_succ_log_self (by decide) b))

def bandNet (n j i : ℕ) := halvedNet ((n:ℝ)^4) (bandLo n j) (bandHi n j) i

/-- The divisor component uses all the signed nets. Its cofactor component
uses the same list with the initial net removed, including all floor endpoints. -/
theorem band_parity_net_sums (n j : ℕ) :
    oddSum n (quotientBandRows n 0 j) =
      ∑ i ∈ range (Nat.log 2 (bandHi n j)+1), bandNet n j i ∧
    cofactorSum n (quotientBandRows n 0 j) =
      ∑ i ∈ range (Nat.log 2 (bandHi n j)), bandNet n j (i+1) := by
  let x := (n:ℝ)^4
  let a := bandLo n j
  let b := bandHi n j
  have sums := interval_odd_log_telescope x a b
  have original : oddSum n (quotientBandRows n 0 j) = intervalOdd x a b := by
    rw [quotient_rows_interval]
    simp only [oddSum,intervalOdd,rowWeight,surviving,Nat.cast_pow,x,a,b]
  have cofactor : cofactorSum n (quotientBandRows n 0 j) = intervalOdd (x/2) (a/2) (b/2) := by
    rw [quotient_rows_interval,cofactorSum,cofactor_interval]
    simp only [intervalOdd,rowWeight,surviving,Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat,div_div,x,a,b]
  constructor
  · exact original.trans sums
  · rw [cofactor]
    have split := interval_odd_halve x a b
    rw [sum_range_succ'] at sums
    change intervalOdd x a b = (∑ i ∈ range (Nat.log 2 b), halvedNet x a b (i+1)) + halvedNet x a b 0 at sums
    simp only [halvedNet,pow_zero,div_one,Nat.div_one] at sums
    change intervalOdd (x/2) (a/2) (b/2) = ∑ i ∈ range (Nat.log 2 b), halvedNet x a b (i+1)
    unfold halvedNet
    linarith only [sums,split]

/-- A signed net crosses its share of the band threshold at a single halving. -/
def signedNetAlarm (n j : ℕ) (t : ℝ) : Prop :=
    (∃ i < Nat.log 2 (bandHi n j)+1,
      bandNet n j i < -share n 0 t/((Nat.log 2 (bandHi n j)+1:ℕ):ℝ)) ∨
    (∃ i, 1 ≤ i ∧ i < Nat.log 2 (bandHi n j)+1 ∧
      share n 0 t/((Nat.log 2 (bandHi n j)+1:ℕ):ℝ) < bandNet n j i)

/-- A negative divisor alarm forces a negative individual net. A positive
cofactor alarm forces a positive net after one or more halvings. -/
theorem band_alarm_signed_net {n j : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (alarm : signEvent n t (quotientBandRows n 0 j)) :
    signedNetAlarm n j t := by
  unfold signedNetAlarm
  let k := Nat.log 2 (bandHi n j)
  let s := share n 0 t
  have s0 : 0 ≤ s := by unfold s share; positivity
  have h0 : (0:ℝ) < ((k+1:ℕ):ℝ) := by positivity
  have pay : ((k+1:ℕ):ℝ)*(s/((k+1:ℕ):ℝ)) = s := by field_simp
  obtain ⟨odd,cof⟩ := band_parity_net_sums n j
  rcases alarm with bad|bad
  · left
    by_contra! miss
    have point (i:ℕ) (hi:i∈range (k+1)) : -(s/((k+1:ℕ):ℝ)) ≤ bandNet n j i := by
      simpa only [neg_div] using miss i (mem_range.mp hi)
    have total := sum_le_sum point
    rw [sum_const,card_range,nsmul_eq_mul,mul_neg,pay,←odd] at total
    linarith only [bad,total]
  · right
    by_contra! miss
    have point (i:ℕ) (hi:i∈range k) : bandNet n j (i+1) ≤ s/((k+1:ℕ):ℝ) :=
      miss (i+1) (by omega) (by have := mem_range.mp hi; change i+1 < k+1; omega)
    have total := sum_le_sum point
    rw [sum_const,card_range,nsmul_eq_mul,←cof] at total
    have upper : (k:ℝ)*(s/((k+1:ℕ):ℝ)) ≤ s := by
      calc _ ≤ ((k+1:ℕ):ℝ)*(s/((k+1:ℕ):ℝ)) := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ k) (div_nonneg s0 h0.le)
           _ = s := pay
    linarith only [bad,total,upper]

/-- Every large value of the original loss has an explicit band, halving and
sign witness among ordinary (unrestricted-parity) Möbius sums. -/
theorem score_signed_net_witness {n : ℕ} {t : ℝ} (hn : 2 ≤ n) (tp : 0 < t)
    (hit : t < score n) : ∃ j < bandCount n 0, signedNetAlarm n j t := by
  have small : envelope n*((0:ℕ):ℝ)^2 ≤ t*(n:ℝ)^2/2 := by
    rw [Nat.cast_zero,zero_pow (by decide : 2≠0),mul_zero]
    positivity
  obtain ⟨j,range,alarm⟩ := odd_band_driving_hit hn tp hit small
  exact ⟨j,range,band_alarm_signed_net tp.le alarm⟩

def signedNetEvent (n : ℕ) (t : ℝ) : Prop :=
  ∃ j < bandCount n 0, signedNetAlarm n j t

theorem signed_net_event_of_odd_alarm {n : ℕ} {t : ℝ} (tp : 0 ≤ t) :
    oddAlarm n t → signedNetEvent n t := by
  rintro ⟨j,hj,alarm⟩
  exact ⟨j,hj,band_alarm_signed_net tp alarm⟩

/-- The total weight of the original alarms is bounded on the identical
block, for every nonnegative real threshold. -/
theorem signed_net_event_mass_covers (m : ℕ) {t : ℝ} (tp : 0 ≤ t) :
    eventMass oddAlarm m t ≤ eventMass signedNetEvent m t := by
  classical
  unfold eventMass
  apply sum_le_sum
  intro n _
  by_cases alarm : oddAlarm n t
  · simp [alarm,signed_net_event_of_odd_alarm tp alarm]
  · simp only [if_neg alarm]
    split <;> positivity

/-- The constant, arbitrarily late blocks and all their simultaneous dyadic
thresholds carry from the ordinary signed nets to the original odd alarms. -/
theorem odd_frequency_of_signed_nets {δ : ℝ} (bound : sharedEventBound signedNetEvent δ) :
    sharedEventBound oddAlarm δ := by
  obtain ⟨C,cp,late⟩ := bound
  refine ⟨C,cp,fun A => ?_⟩
  obtain ⟨m,hm,all⟩ := late A
  refine ⟨m,hm,fun i => ?_⟩
  exact (mul_le_mul_of_nonneg_left
    (signed_net_event_mass_covers m (show 0 ≤ (2:ℝ)^i by positivity)) (by positivity)).trans (all i)

end RiemannReduction.ShortTail.LossFrequency
