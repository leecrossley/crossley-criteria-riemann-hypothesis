import FirstLayerCriterion
import ShallowRemainder

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Filter Real

/-- A negative first net in a bin below the paid quotient boundary. Both
inequalities concern the same bin, with its original full band share. -/
def shallowFirstEvent (b : ℕ→ℕ) (α : ℝ) (n : ℕ) (t : ℝ) : Prop :=
  ∃ j < bandCount n 0, (2:ℝ)^(2*j) < (n:ℝ)^(2-α) ∧
    clippedBandNet (b n) n j 0 < -share n 0 t

def residualFirstEvent (δ : ℝ) :=
  shallowFirstEvent (powerCut (δ/8)) (3*δ/8)

/-- A divisor beyond n³ n^β automatically has quotient 2^j < n^(1−β).
This follows from the definition of its bin, without any cancellation. -/
theorem clipped_divisor_quotient_range {n j d : ℕ} (hn : 1 ≤ n) {β : ℝ}
    (hd : d ∈ laterRows n j (powerCut β n)) :
    (2:ℝ)^j < (n:ℝ)^(1-β) := by
  rw [later_rows_interval,mem_Ioc,max_lt_iff] at hd
  have cut := hd.1.1
  unfold powerCut at cut
  have lower := (Nat.floor_lt (by positivity : 0 ≤ (n:ℝ)^3*(n:ℝ)^β)).mp cut
  have up : d ≤ n^4/2^j := hd.2.trans (min_le_right ..)
  have height : (d:ℝ)*(2:ℝ)^j ≤ (n:ℝ)^4 := by
    exact_mod_cast (Nat.le_div_iff_mul_le (by positivity : 0 < (2:ℕ)^j)).mp up
  have scale := mul_lt_mul_of_pos_right lower (by positivity : 0 < (2:ℝ)^j)
  have strict : (2:ℝ)^j*(n:ℝ)^β < (n:ℝ) := by
    by_contra! contra
    have wrong := mul_le_mul_of_nonneg_right contra (by positivity : 0 ≤ (n:ℝ)^3)
    linarith only [scale,height,wrong]
  have pos : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  rw [rpow_sub pos,rpow_one]
  exact (lt_div_iff₀ (rpow_pos_of_pos pos _)).mpr strict

/-- At the original δ/8 divisor cutoff the δ/4 first-layer mask is
automatic. A larger α is needed to narrow the first-layer criterion. -/
theorem quarter_shallow_first_iff {n : ℕ} (hn : 1 ≤ n) (δ : ℝ) {t : ℝ} (tp : 0 ≤ t) :
    shallowFirstEvent (powerCut (δ/8)) (δ/4) n t ↔ firstLayerEvent (powerCut (δ/8)) n t := by
  constructor
  · rintro ⟨j,hj,_,bad⟩
    exact ⟨j,hj,bad⟩
  · rintro ⟨j,hj,bad⟩
    have share0 : 0 ≤ share n 0 t := by unfold share; positivity
    have neg := bad.trans_le (neg_nonpos.mpr share0)
    have rows : (laterRows n j (powerCut (δ/8) n)).Nonempty := by
      by_contra! empty
      rw [later_rows_interval] at empty
      simp only [clippedBandNet,halvedNet,intervalNet,pow_zero,Nat.div_one,div_one,empty,sum_empty] at neg
      exact (lt_irrefl _ neg)
    obtain ⟨d,hd⟩ := rows
    have bound := clipped_divisor_quotient_range hn hd
    refine ⟨j,hj,?_,bad⟩
    calc (2:ℝ)^(2*j) = ((2:ℝ)^j)^2 := by rw [←pow_mul,Nat.mul_comm]
         _ < ((n:ℝ)^(1-δ/8))^2 := by gcongr
         _ = (n:ℝ)^(2-δ/4) := by
           rw [←rpow_two,←rpow_mul (Nat.cast_nonneg _)]
           congr 1
           ring

/-- At depth zero a full-share crossing is also an individual adverse
layer. Only the negative alternative is used. -/
theorem deep_first_layer_cover {b : ℕ→ℕ} {α t : ℝ} {n j : ℕ}
    (tp : 0 ≤ t) (hj : j < bandCount n 0) (deep : deepLayer α n j 0)
    (crossing : clippedBandNet (b n) n j 0 < -share n 0 t) :
    selectedLayerEvent b (deepLayer α) n t := by
  have one : (1:ℝ) ≤ (halvingCount n j:ℝ) := by unfold halvingCount; exact_mod_cast Nat.le_add_left 1 _
  have nonneg : 0 ≤ share n 0 t := by unfold share; positivity
  have less : layerShare n j t ≤ share n 0 t := div_le_self nonneg one
  exact ⟨j,hj,0,by unfold halvingCount; omega,deep,Or.inl (crossing.trans_le (neg_le_neg less))⟩

theorem first_layer_shallow_or_paid {b : ℕ→ℕ} {α t : ℝ} {n : ℕ} (tp : 0 ≤ t)
    (hit : firstLayerEvent b n t) :
    shallowFirstEvent b α n t ∨ selectedLayerEvent b (deepLayer α) n t := by
  obtain ⟨j,hj,bad⟩ := hit
  by_cases paid : deepLayer α n j 0
  · exact Or.inr (deep_first_layer_cover tp hj paid bad)
  · refine Or.inl ⟨j,hj,?_,bad⟩
    simpa only [deepLayer,zero_add,not_le] using paid

theorem first_layer_shallow_mass (b : ℕ→ℕ) (α : ℝ) (m : ℕ) {t : ℝ} (tp : 0 ≤ t) :
    eventMass (firstLayerEvent b) m t ≤ eventMass (shallowFirstEvent b α) m t +
      eventMass (selectedLayerEvent b (deepLayer α)) m t := by
  classical
  unfold eventMass
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro n _
  by_cases hit : firstLayerEvent b n t
  · rw [if_pos hit]
    rcases first_layer_shallow_or_paid (α:=α) tp hit with shallow|deep
    · rw [if_pos shallow]
      split <;> simp
    · rw [if_pos deep]
      split <;> simp
  · rw [if_neg hit]
    split_ifs <;> positivity

/-- The deep layers pass on every sufficiently late block. The block
selected by the shallow negative first nets therefore serves both estimates. -/
theorem first_frequency_of_shallow {δ α : ℝ} (ha : 0 ≤ α) (gap : 2*α < δ) (b : ℕ→ℕ)
    (remaining : sharedEventBound (shallowFirstEvent b α) δ) : sharedEventBound (firstLayerEvent b) δ := by
  obtain ⟨C,cp,blocks⟩ := remaining
  obtain ⟨N,deep⟩ := eventually_atTop.mp (deep_layer_subpower ha gap b)
  refine ⟨C+1,by linarith,fun A => ?_⟩
  obtain ⟨m,hm,all⟩ := blocks (max A N)
  refine ⟨m,(le_max_left ..).trans hm,fun j => ?_⟩
  have tp : 0 < (2:ℝ)^j := by positivity
  have paid := deep m ((le_max_right ..).trans hm) _ tp
  have mass := mul_le_mul_of_nonneg_left (first_layer_shallow_mass b α m tp.le) tp.le
  linarith only [mass,paid,all j]

theorem first_frequency_of_residual {δ : ℝ} (ep : 0 < δ)
    (remaining : sharedEventBound (residualFirstEvent δ) δ) :
    sharedEventBound (firstLayerEvent (powerCut (δ/8))) δ :=
  first_frequency_of_shallow (α:=3*δ/8) (by positivity) (by linarith) _ remaining

/-- It suffices to count the negative *unhalved* nets beyond the original
divisor cutoff in the bins 2^(2j) < n^(2−3δ/8). -/
theorem rh_of_residual_first
    (h : ∀ δ > (0:ℝ), sharedEventBound (residualFirstEvent δ) δ) : RiemannHypothesis :=
  rh_of_first_layer_frequency fun δ ep => first_frequency_of_residual ep (h δ ep)

private theorem mass_nonnegative (test : ℕ→ℝ→Prop) (m : ℕ) (t : ℝ) : 0 ≤ eventMass test m t := by
  classical
  unfold eventMass
  apply sum_nonneg
  intro n _
  split <;> positivity

/-- The harmonic mass alone pays all tests simultaneously below threshold
one on every sufficiently late block. -/
theorem event_mass_below_one {δ : ℝ} (ep : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, ∀ (test : ℕ→ℝ→Prop) (t : ℝ), t ≤ 1 →
      t*eventMass test m t ≤ (m:ℝ)^δ := by
  classical
  have grow := ((tendsto_rpow_atTop (half_pos ep)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  filter_upwards [low_thresholds (fun _ : ℕ => (2:ℝ)) ep,grow] with m low big test t ht
  have total := low 1 zero_le_one big
  simp only [frequency,show (1:ℝ)<2 by norm_num,if_true,one_mul] at total
  have size : eventMass test m t ≤ ∑ n ∈ Icc m (m^2), (n:ℝ)⁻¹ := by
    unfold eventMass
    apply sum_le_sum
    intro n _
    split <;> simp
  exact (mul_le_of_le_one_left (mass_nonnegative test m t) ht).trans (size.trans total)

private theorem residual_first_mass_antitone (δ : ℝ) (m : ℕ) {s t : ℝ} (st : s ≤ t) :
    eventMass (residualFirstEvent δ) m t ≤ eventMass (residualFirstEvent δ) m s := by
  classical
  unfold eventMass
  apply sum_le_sum
  intro n _
  by_cases hit : residualFirstEvent δ n t
  · have smaller : residualFirstEvent δ n s := by
      obtain ⟨j,hj,shallow,bad⟩ := hit
      have ordered : share n 0 s ≤ share n 0 t := by
        unfold share
        gcongr
      exact ⟨j,hj,shallow,bad.trans_le (neg_le_neg ordered)⟩
    simp [hit,smaller]
  · simp only [if_neg hit]
    split <;> positivity

/-- Rounding down to a dyadic threshold preserves the original common
block. For thresholds at least one the multiplicative cost is at most two. -/
theorem residual_first_real_thresholds {δ : ℝ} (ep : 0 < δ)
    (dyadic : sharedEventBound (residualFirstEvent δ) δ) :
    ∃ C > (0:ℝ), ∀ A : ℕ, ∃ m ≥ A, ∀ t : ℝ, 0 < t →
      t*eventMass (residualFirstEvent δ) m t ≤ C*(m:ℝ)^δ := by
  obtain ⟨K,kp,blocks⟩ := dyadic
  obtain ⟨N,low⟩ := eventually_atTop.mp (event_mass_below_one ep)
  refine ⟨1+2*K,by linarith,fun A => ?_⟩
  obtain ⟨m,hm,all⟩ := blocks (max A N)
  refine ⟨m,(le_max_left ..).trans hm,fun t _ => ?_⟩
  have pos := rpow_nonneg (Nat.cast_nonneg (α:=ℝ) m) δ
  by_cases small : t ≤ 1
  · have pass := low m ((le_max_right ..).trans hm) (residualFirstEvent δ) t small
    linarith only [pass,mul_nonneg kp.le pos]
  · obtain ⟨j,left,right⟩ := exists_nat_pow_near (le_of_lt (lt_of_not_ge small)) (by norm_num : (1:ℝ)<2)
    rw [pow_succ] at right
    have pay := mul_le_mul right.le (residual_first_mass_antitone δ m left)
      (mass_nonnegative _ _ _) (show 0 ≤ (2:ℝ)^j*2 by positivity)
    have bin := all j
    linarith only [pay,bin,pos]

end RiemannReduction.ShortTail.LossFrequency
