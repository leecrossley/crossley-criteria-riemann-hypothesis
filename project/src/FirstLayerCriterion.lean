import HalvingOrientation

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Filter Real

/-- Once the first net is sufficiently negative, every possible choice of
the remaining signs leaves an alarm. This is a lower frequency bound. -/
theorem first_layer_forces_clipped (b : ℕ→ℕ) (m : ℕ) (t : ℝ) :
    eventMass (firstLayerEvent b) m (2*t) ≤ eventMass (fun n => laterEvent (b n) n) m t := by
  classical
  unfold eventMass
  apply sum_le_sum
  intro n _
  by_cases first : firstLayerEvent b n (2*t)
  · have hit : laterEvent (b n) n t := by
      obtain ⟨j,hj,neg⟩ := first
      refine ⟨j,hj,(clipped_sign_event_exact _ _ _ _).mpr (Or.inl ?_)⟩
      rw [show share n 0 (2*t)=2*share n 0 t by unfold share; ring] at neg
      linarith only [neg]
    simp [first,hit]
  · simp only [if_neg first]
    split <;> positivity

/-- A genuine retained loss can be charged to an early contribution or to
the negative unhalved net of one clipped bin. The test for this first
layer uses the entire band share, without division by the depth count. -/
theorem score_to_early_or_first {n : ℕ} (hn : 2 ≤ n) (b : ℕ→ℕ) {t : ℝ} (tp : 0<t)
    (hit : t<score n) : earlyEvent (b n) n (t/2) ∨ firstLayerEvent b n t := by
  have zero : envelope n*((0:ℕ):ℝ)^2 ≤ t*(n:ℝ)^2/2 := by
    rw [Nat.cast_zero,zero_pow (by decide : 2≠0),mul_zero]
    positivity
  obtain ⟨j,hj,net⟩ := band_driving_hit hn tp hit zero
  by_cases paid : earlyEvent (b n) n (t/2)
  · exact Or.inl paid
  · have quiet : ¬signEvent n (t/2) (earlyRows n j (b n)) := fun h => paid ⟨j,hj,h⟩
    have o : -share n 0 (t/2) ≤ oddSum n (earlyRows n j (b n)) :=
      le_of_not_gt (fun h => quiet (Or.inl h))
    have c : cofactorSum n (earlyRows n j (b n)) ≤ share n 0 (t/2) :=
      le_of_not_gt (fun h => quiet (Or.inr h))
    have half : share n 0 (t/2)=share n 0 t/2 := by unfold share; ring
    have scaled : -(t*(n:ℝ)^2)/(2*(bandCount n 0:ℝ)) = -2*share n 0 t := by unfold share; ring
    rw [scaled] at net
    rw [half] at o c
    have fold : bandSum n 0 j=oddSum n (quotientBandRows n 0 j)-cofactorSum n (quotientBandRows n 0 j) :=
      fold_signed_rows _ (rowWeight n)
    obtain ⟨left,right⟩ := sign_split n (b n) j
    refine Or.inr ⟨j,hj,?_⟩
    rw [first_layer_difference]
    linarith only [o,c,fold,left,right,net]

theorem score_frequency_first_layer (b : ℕ→ℕ) {m : ℕ} (hm : 2 ≤ m) {t : ℝ} (tp : 0<t) :
    frequency score m t ≤ eventMass (fun n => earlyEvent (b n) n) m (t/2) +
      eventMass (firstLayerEvent b) m t := by
  classical
  unfold frequency eventMass
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro n hn
  by_cases hit : t<score n
  · rw [if_pos hit]
    rcases score_to_early_or_first (hm.trans (mem_Icc.mp hn).1) b tp hit with early|first
    · rw [if_pos early]
      split <;> simp
    · rw [if_pos first]
      split <;> simp
  · rw [if_neg hit]
    split_ifs <;> positivity

/-- Frequency of negative depth-zero nets alone is already sufficient for
RH. Later halvings and positive first-layer nets never enter the premise.
The denominator in firstLayerEvent is 4B_n, even if the band has many layers. -/
theorem rh_of_first_layer_frequency
    (h : ∀ δ > (0:ℝ), sharedEventBound (firstLayerEvent (powerCut (δ/8))) δ) :
    RiemannHypothesis := by
  apply rh_iff_frequency.mpr
  intro δ ep
  obtain ⟨C,cp,blocks⟩ := h δ ep
  obtain ⟨N,early⟩ := eventually_atTop.mp
    (prefix_event_frequency (a:=δ/8) (by positivity) (by linarith : 4*(δ/8)<δ))
  refine ⟨2+C,by linarith,fun A => ?_⟩
  obtain ⟨m,hm,first⟩ := blocks (max A (max N 2))
  have mlarge := (le_max_right A (max N 2)).trans hm
  refine ⟨m,(le_max_left ..).trans hm,fun j => ?_⟩
  have tp : 0<(2:ℝ)^j := by positivity
  have cover := mul_le_mul_of_nonneg_left
    (score_frequency_first_layer (powerCut (δ/8)) ((le_max_right N 2).trans mlarge) tp) tp.le
  have paid := early m ((le_max_left N 2).trans mlarge) ((2:ℝ)^j/2) (by positivity)
  linarith only [paid,cover,first j]

end RiemannReduction.ShortTail.LossFrequency
