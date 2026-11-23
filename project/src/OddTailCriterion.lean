import OddAlarmCut

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Filter Real

def sharedEventBound (test : ℕ → ℝ → Prop) (δ : ℝ) : Prop :=
  ∃ C > (0:ℝ), ∀ A : ℕ, ∃ m ≥ A, ∀ j : ℕ,
    (2:ℝ)^j*eventMass test m ((2:ℝ)^j) ≤ C*(m:ℝ)^δ

/-- This consequence does not assert the converse for the separated alarms. -/
theorem rh_of_odd_event_bounds (h : ∀ δ > (0:ℝ), sharedEventBound oddAlarm δ) :
    RiemannHypothesis := by
  apply rh_iff_frequency.mpr
  intro δ ep
  obtain ⟨C,cp,blocks⟩ := h δ ep
  refine ⟨C,cp,fun A => ?_⟩
  obtain ⟨m,hm,all⟩ := blocks (max A 2)
  refine ⟨m,(le_max_left ..).trans hm,fun j => ?_⟩
  have cover := frequency_odd_witness ((le_max_right ..).trans hm) (by positivity : 0 < (2:ℝ)^j)
  exact (mul_le_mul_of_nonneg_left cover (by positivity)).trans (all j)

private theorem original_through_fourth (n j : ℕ) :
    earlyRows n j (powerCut 1 n)=quotientBandRows n 0 j := by
  have cut : powerCut 1 n=n^4 := by
    rw [powerCut,rpow_one,show (n:ℝ)^3*n=((n^4:ℕ):ℝ) by push_cast; ring,Nat.floor_natCast]
  rw [earlyRows,filter_eq_self]
  intro d hd
  have l := (mem_filter.mp (mem_filter.mp hd).1).1
  rw [cut]
  exact (mem_Ioc.mp (mem_filter.mp l).1).2.trans (Nat.div_le_self ..)

theorem full_odd_above_four {δ : ℝ} (hδ : 4 < δ) :
    ∀ᶠ m : ℕ in atTop, ∀ t : ℝ, 0<t → t*eventMass oddAlarm m t ≤ (m:ℝ)^δ := by
  have eq : (fun n => earlyEvent (powerCut 1 n) n)=oddAlarm := by
    funext n t
    simp only [earlyEvent,original_through_fourth,oddAlarm,signEvent]
  have bound := prefix_event_frequency (a:=1) zero_le_one (by simpa using hδ)
  rwa [eq] at bound

/-- The high-divisor bound is needed only above n³ n^(δ/8). A common block
for all its dyadic thresholds transfers to a common block for the full event. -/
theorem odd_frequency_of_tail {δ : ℝ} (ep : 0<δ)
    (tail : sharedEventBound (fun n => laterEvent (powerCut (δ/8) n) n) δ) :
    sharedEventBound oddAlarm δ := by
  obtain ⟨C,cp,late⟩ := tail
  have early := prefix_event_frequency (a:=δ/8) (by positivity) (by linarith : 4*(δ/8)<δ)
  have low := low_thresholds (fun _ : ℕ => (2:ℝ)) ep
  have grow := ((tendsto_rpow_atTop (half_pos ep)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  obtain ⟨B,uniform⟩ := eventually_atTop.mp (early.and (low.and grow))
  refine ⟨2*(1+C),by positivity,fun A => ?_⟩
  obtain ⟨m,hm,all⟩ := late (max A B)
  obtain ⟨small,harmonic,big⟩ := uniform m ((le_max_right ..).trans hm)
  refine ⟨m,(le_max_left ..).trans hm,fun j => ?_⟩
  cases j with
  | zero =>
    classical
    have triv := harmonic 1 zero_le_one big
    simp only [frequency,show (1:ℝ)<2 by norm_num,if_true,one_mul] at triv
    have mass : eventMass oddAlarm m 1 ≤ ∑ n ∈ Icc m (m^2), (n:ℝ)⁻¹ := by
      apply sum_le_sum
      intro n _
      split <;> simp
    simp only [pow_zero,one_mul]
    linarith only [mass,triv,rpow_nonneg (Nat.cast_nonneg (α:=ℝ) m) δ,
      mul_nonneg cp.le (rpow_nonneg (Nat.cast_nonneg (α:=ℝ) m) δ)]
  | succ j =>
    have split := event_mass_split m (powerCut (δ/8)) ((2:ℝ)^(j+1))
    rw [pow_succ,mul_div_cancel_right₀ _ (by norm_num)] at split
    have mul := mul_le_mul_of_nonneg_left split (by positivity : 0≤(2:ℝ)^j)
    rw [pow_succ]
    linarith only [mul,small _ (by positivity : 0<(2:ℝ)^j),all j]

end RiemannReduction.ShortTail.LossFrequency
