import OddMertensFold
import FrequencyCriterion

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Filter Real RiemannGaussian.AlpogeMined
open scoped ArithmeticFunction.Moebius

def earlyRows (n j b : ℕ) := (quotientBandRows n 0 j).filter (· ≤ b)
def laterRows (n j b : ℕ) := (quotientBandRows n 0 j).filter (fun d => ¬d ≤ b)

def signEvent (n : ℕ) (t : ℝ) (S : Finset ℕ) : Prop :=
  oddSum n S < -share n 0 t ∨ share n 0 t < cofactorSum n S

def earlyEvent (b n : ℕ) (t : ℝ) : Prop := ∃ j < bandCount n 0, signEvent n t (earlyRows n j b)
def laterEvent (b n : ℕ) (t : ℝ) : Prop := ∃ j < bandCount n 0, signEvent n t (laterRows n j b)

open Classical in
def eventMass (test : ℕ → ℝ → Prop) (m : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Icc m (m^2), if test n t then (n:ℝ)⁻¹ else 0

def powerCut (a : ℝ) (n : ℕ) : ℕ := ⌊(n:ℝ)^3*(n:ℝ)^a⌋₊

private theorem odd_indicator (n : ℕ) (S : Finset ℕ) :
    oddSum n S=∑ d ∈ S, if d%2=1 then term n d else 0 := by
  rw [oddSum,sum_filter]
  rfl

private theorem cofactor_even (n : ℕ) (S : Finset ℕ) :
    cofactorSum n S = -(∑ d ∈ S.filter (fun d => ¬ d%2=1), term n d) := by
  have fold : (∑ d ∈ S, term n d)=oddSum n S-cofactorSum n S :=
    fold_signed_rows S (rowWeight n)
  have split := sum_filter_add_sum_filter_not S (fun d => d%2=1) (term n)
  change oddSum n S + _ = _ at split
  linarith only [fold,split]

theorem odd_components_abs (n : ℕ) (S : Finset ℕ) :
    |oddSum n S| ≤ ∑ d ∈ S, |term n d| ∧ |cofactorSum n S| ≤ ∑ d ∈ S, |term n d| := by
  have filtered (p : ℕ → Prop) [DecidablePred p] :
      |∑ d ∈ S.filter p, term n d| ≤ ∑ d ∈ S, |term n d| :=
    (abs_sum_le_sum_abs ..).trans (sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => abs_nonneg _))
  constructor
  · exact filtered (fun d => d%2=1)
  · rw [cofactor_even,abs_neg]
    exact filtered _

theorem sign_split (n b j : ℕ) :
    oddSum n (earlyRows n j b)+oddSum n (laterRows n j b)=oddSum n (quotientBandRows n 0 j) ∧
    cofactorSum n (earlyRows n j b)+cofactorSum n (laterRows n j b)=cofactorSum n (quotientBandRows n 0 j) := by
  constructor
  · simp only [odd_indicator,earlyRows,laterRows]
    exact sum_filter_add_sum_filter_not .. 
  · simp only [cofactor_even,sum_filter,earlyRows,laterRows]
    have split := sum_filter_add_sum_filter_not (quotientBandRows n 0 j) (· ≤ b)
      (fun d => if ¬d%2=1 then term n d else 0)
    simp only [sum_filter] at split
    linarith only [split]

theorem event_split {n : ℕ} (b : ℕ) {t : ℝ} (hit : oddAlarm n t) :
    earlyEvent b n (t/2) ∨ laterEvent b n (t/2) := by
  obtain ⟨j,hj,bad⟩ := hit
  have ⟨odd,half⟩ := sign_split n b j
  have scale : share n 0 (t/2)=share n 0 t/2 := by unfold share; ring
  by_cases e : signEvent n (t/2) (earlyRows n j b)
  · exact Or.inl ⟨j,hj,e⟩
  · refine Or.inr ⟨j,hj,?_⟩
    unfold signEvent at e ⊢
    rw [scale] at e ⊢
    push Not at e
    rcases bad with a|a
    · exact Or.inl (by linarith only [a,e.1,odd])
    · exact Or.inr (by linarith only [a,e.2,half])

theorem event_mass_split (m : ℕ) (b : ℕ → ℕ) (t : ℝ) :
    eventMass oddAlarm m t ≤ eventMass (fun n => earlyEvent (b n) n) m (t/2) +
      eventMass (fun n => laterEvent (b n) n) m (t/2) := by
  classical
  unfold eventMass
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro n _
  by_cases h : oddAlarm n t
  · rw [if_pos h]
    rcases event_split (b n) h with early|later
    · rw [if_pos early]
      split <;> simp
    · rw [if_pos later]
      split <;> simp
  · rw [if_neg h]
    split_ifs <;> positivity

private theorem early_threshold {b n : ℕ} {t : ℝ} (hn : 2≤n) (h : earlyEvent b n t) :
    t*(n:ℝ)^2 < 4*(bandCount n 0:ℝ)*(envelope n*(b:ℝ)^2) := by
  obtain ⟨j,_,alarm⟩ := h
  let S := earlyRows n j b
  have half : S ⊆ Ioc 0 (n^4/2) := by
    intro d hd
    have hband := (mem_filter.mp hd).1
    have hlate := (mem_filter.mp (mem_filter.mp hband).1).1
    have v := mem_Ioc.mp (mem_filter.mp hlate).1
    exact mem_Ioc.mpr ⟨by omega,v.2⟩
  have small : S ⊆ Ioc 0 b := fun d hd =>
    mem_Ioc.mpr ⟨(mem_Ioc.mp (half hd)).1,(mem_filter.mp hd).2⟩
  have budget := cut_absolute hn S half small
  obtain ⟨odd,cof⟩ := odd_components_abs n S
  have less : share n 0 t < envelope n*(b:ℝ)^2 := by
    rcases alarm with a|a
    · exact lt_of_lt_of_le (show share n 0 t < -oddSum n S by change oddSum n S < -_ at a; linarith only [a]) (by
        change -oddSum n S ≤ _
        exact (neg_le_abs _).trans (odd.trans budget))
    · exact a.trans_le ((le_abs_self _).trans (cof.trans budget))
  have cp : 0 < (bandCount n 0:ℝ) := by unfold bandCount; positivity
  have pos := mul_lt_mul_of_pos_right less (show 0<4*(bandCount n 0:ℝ) by positivity)
  have eq : share n 0 t*(4*(bandCount n 0:ℝ))=t*(n:ℝ)^2 := by unfold share; field_simp; ring
  linarith only [pos,eq]

theorem band_count_log {n : ℕ} (hn : 1≤n) : (bandCount n 0:ℝ) ≤ 1+8*log n := by
  let J := Nat.log 2 (n^4)
  have p : (2:ℝ)^J ≤ (n:ℝ)^4 := by exact_mod_cast Nat.pow_log_le_self 2 (show n^4≠0 by positivity)
  have l := log_le_log (by positivity : 0<(2:ℝ)^J) p
  rw [log_pow,log_pow] at l
  norm_num only [Nat.cast_ofNat] at l
  have c := one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at c
  simp only [bandCount,zero_add,Nat.div_one,Nat.cast_add,Nat.cast_one]
  change (J:ℝ)+1 ≤ _
  linarith only [l,mul_le_mul_of_nonneg_left c (Nat.cast_nonneg (α:=ℝ) J)]

theorem absorb_log_square (C : ℝ) (hc : 0≤C) {η : ℝ} (ep : 0<η) :
    ∀ᶠ n : ℕ in atTop, C*(1+8*log n)^2 ≤ (n:ℝ)^η := by
  have grow := (isLittleO_log_rpow_rpow_atTop 2 ep).const_mul_left (81*C)
  have est := (grow.comp_tendsto (tendsto_natCast_atTop_atTop (R:=ℝ))).bound (c:=1) zero_lt_one
  filter_upwards [est,(tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1] with n h hn
  change 1 ≤ log n at hn
  change ‖81*C*(log n)^(2:ℝ)‖ ≤ 1*‖(n:ℝ)^η‖ at h
  rw [rpow_two,Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (rpow_nonneg (Nat.cast_nonneg _) _),one_mul] at h
  have sq := pow_le_pow_left₀ (by linarith : 0≤1+8*log n) (by linarith : 1+8*log n ≤ 9*log n) 2
  linarith only [h,mul_le_mul_of_nonneg_left sq hc]

/-- Only the original divisors up to n³ n^a enter this frequency. Both signs
are bounded on every sufficiently late complete block at every threshold. -/
theorem prefix_event_frequency {a δ : ℝ} (ha : 0≤a) (gap : 4*a<δ) :
    ∀ᶠ m : ℕ in atTop, ∀ t : ℝ, 0<t →
      t*eventMass (fun n => earlyEvent (powerCut a n) n) m t ≤ (m:ℝ)^δ := by
  let η := (δ-4*a)/3
  have ep : 0<η := by dsimp [η]; linarith
  have coeff := absorb_log_square (4*kernelConstant) (by positivity [kernelConstant_nonneg]) ep
  have one := absorb_log_square 1 zero_le_one ep
  obtain ⟨A,all⟩ := eventually_atTop.mp coeff
  filter_upwards [eventually_ge_atTop (max A 2),one] with m hm hmLog t ht
  have mp : 0<(m:ℝ) := Nat.cast_pos.mpr (by omega)
  have uniform (n : ℕ) (hn : n ∈ Icc m (m^2)) (hit : earlyEvent (powerCut a n) n t) :
      t ≤ (m:ℝ)^(2*(2*a+η)) := by
    obtain ⟨mn,nm⟩ := mem_Icc.mp hn
    have np : 0<(n:ℝ) := Nat.cast_pos.mpr (by omega)
    let B : ℝ := bandCount n 0
    have bound := early_threshold (by omega : 2≤n) hit
    change t*(n:ℝ)^2 < 4*B*(envelope n*(powerCut a n:ℝ)^2) at bound
    have floor := Nat.floor_le (show 0 ≤ (n:ℝ)^3*(n:ℝ)^a by positivity)
    change (powerCut a n:ℝ) ≤ _ at floor
    have env : 0≤ envelope n := by unfold envelope; positivity [kernelConstant_nonneg,log_natCast_nonneg (n^4)]
    have large := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) floor 2)
      (show 0≤4*B*envelope n by dsimp [B]; positivity)
    have logn := log_natCast_nonneg n
    have product := mul_le_mul (band_count_log (by omega : 1≤n))
      (show 1+4*log n ≤ 1+8*log n by linarith) (by linarith) (by linarith)
    have inc := mul_le_mul_of_nonneg_left product (show 0≤4*kernelConstant by positivity [kernelConstant_nonneg])
    have c : 4*B*kernelConstant*(1+4*log n) ≤ (n:ℝ)^η := by
      apply le_trans _ (all n (by omega))
      dsimp [B]
      linarith only [inc]
    have power : ((n:ℝ)^a)^2=(n:ℝ)^(2*a) := by rw [pow_two,←rpow_add np,two_mul]
    have rearrange : 4*B*envelope n*((n:ℝ)^3*(n:ℝ)^a)^2 =
        (4*B*kernelConstant*(1+4*log n))*(n:ℝ)^(2*a)*(n:ℝ)^2 := by
      unfold envelope
      rw [Nat.cast_pow,log_pow,←power]
      norm_num only [Nat.cast_ofNat]
      field_simp
    have raw : t*(n:ℝ)^2 ≤ (n:ℝ)^η*(n:ℝ)^(2*a)*(n:ℝ)^2 := by
      calc
        _ ≤ 4*B*envelope n*((powerCut a n:ℝ)^2) := by linarith only [bound]
        _ ≤ _ := large
        _ = _ := rearrange
        _ ≤ _ := by gcongr
    have atn := le_of_mul_le_mul_right raw (pow_pos np 2)
    rw [←rpow_add np,add_comm η] at atn
    have hmn : (n:ℝ) ≤ (m:ℝ)^2 := by exact_mod_cast nm
    have p := rpow_le_rpow np.le hmn (by linarith : 0≤2*a+η)
    rw [←rpow_natCast_mul mp.le] at p
    exact atn.trans (by simpa using p)
  classical
  unfold eventMass
  rw [mul_sum]
  have each (n : ℕ) (hn : n ∈ Icc m (m^2)) :
      t*(if earlyEvent (powerCut a n) n t then (n:ℝ)⁻¹ else 0) ≤ (m:ℝ)^(2*(2*a+η))*(n:ℝ)⁻¹ := by
    split_ifs with hit
    · exact mul_le_mul_of_nonneg_right (uniform n hn hit) (by positivity)
    · rw [mul_zero]; positivity
  apply (sum_le_sum each).trans
  rw [←mul_sum]
  have hsum : (∑ n ∈ Icc m (m^2), (n:ℝ)⁻¹) ≤ (m:ℝ)^η := by
    have h := harmonic_window (by omega : 1 ≤ m)
    nlinarith only [h,hmLog,log_natCast_nonneg m,sq_nonneg (log m)]
  calc _ ≤ (m:ℝ)^(2*(2*a+η))*(m:ℝ)^η := mul_le_mul_of_nonneg_left hsum (by positivity)
       _ = _ := by rw [←rpow_add mp]; congr 1; dsimp [η]; ring

end RiemannReduction.ShortTail.LossFrequency
