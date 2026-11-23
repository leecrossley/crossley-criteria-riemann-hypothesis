import HalvingFrequency

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Filter

private theorem split_layer_mass (b : ℕ → ℕ) (α : ℝ) (m : ℕ) (t : ℝ) :
    eventMass (selectedLayerEvent b (fun _ _ _ => True)) m t ≤
      eventMass (selectedLayerEvent b (deepLayer α)) m t +
      eventMass (selectedLayerEvent b (fun n j i => ¬deepLayer α n j i)) m t := by
  classical
  unfold eventMass
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro n _
  by_cases hit : selectedLayerEvent b (fun _ _ _ => True) n t
  · rw [if_pos hit]
    obtain ⟨j,hj,i,hi,_,bad⟩ := hit
    by_cases deep : deepLayer α n j i
    · have good : selectedLayerEvent b (deepLayer α) n t := ⟨j,hj,i,hi,deep,bad⟩
      rw [if_pos good]
      split <;> simp
    · have good : selectedLayerEvent b (fun n j i => ¬deepLayer α n j i) n t := ⟨j,hj,i,hi,deep,bad⟩
      rw [if_pos good]
      split <;> simp
  · rw [if_neg hit]
    split_ifs <;> positivity

/-- Only the clipped layers below the depth/quotient cutoff require a
common-block arithmetic estimate. All other layers already pass on every
sufficiently late block. -/
theorem all_layers_of_shallow {α δ : ℝ} (ha : 0≤α) (gap : 2*α<δ) (b : ℕ→ℕ)
    (small : sharedEventBound (selectedLayerEvent b (fun n j i => ¬deepLayer α n j i)) δ) :
    sharedEventBound (selectedLayerEvent b (fun _ _ _ => True)) δ := by
  obtain ⟨C,cp,blocks⟩ := small
  obtain ⟨N,paid⟩ := eventually_atTop.mp (deep_layer_subpower ha gap b)
  refine ⟨1+C,by linarith,fun A => ?_⟩
  obtain ⟨m,hm,all⟩ := blocks (max A N)
  refine ⟨m,(le_max_left ..).trans hm,fun k => ?_⟩
  have tp : 0<(2:ℝ)^k := by positivity
  have d := paid m ((le_max_right ..).trans hm) _ tp
  have add := mul_le_mul_of_nonneg_left (split_layer_mass b α m ((2:ℝ)^k)) tp.le
  linarith only [add,d,all k]

/-- The remaining original divisors exceed n^(3+δ/8), and the remaining
depths satisfy 2^(i+2j)<n^(2−δ/4). The block may depend on δ alone among
the exponents and thresholds used in this statement. -/
def residualSignedEvent (δ : ℝ) :=
  selectedLayerEvent (powerCut (δ/8)) (fun n j i => ¬deepLayer (δ/4) n j i)

theorem odd_frequency_of_residual_signed {δ : ℝ} (ep : 0<δ)
    (remaining : sharedEventBound (residualSignedEvent δ) δ) :
    sharedEventBound oddAlarm δ :=
  odd_frequency_of_clipped_layers ep
    (all_layers_of_shallow (α:=δ/4) (by positivity) (by linarith) _ remaining)

/-- A proof of the residual signed frequency for all δ gives ordinary RH. -/
theorem rh_of_residual_signed (h : ∀ δ > (0:ℝ), sharedEventBound (residualSignedEvent δ) δ) :
    RiemannHypothesis :=
  rh_of_odd_event_bounds fun δ ep => odd_frequency_of_residual_signed ep (h δ ep)

end RiemannReduction.ShortTail.LossFrequency
