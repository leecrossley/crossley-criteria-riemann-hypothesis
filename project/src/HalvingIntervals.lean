import OddBandDilation

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset RiemannReduction.ThirdBridge

def clippedBandNet (b n j i : ℕ) :=
  halvedNet ((n:ℝ)^4) (max b (bandLo n j)) (bandHi n j) i

def halvingCount (n j : ℕ) := Nat.log 2 (bandHi n j)+1

def layerShare (n j : ℕ) (t : ℝ) := share n 0 t/(halvingCount n j:ℝ)

def adverseLayer (b n j i : ℕ) (t : ℝ) : Prop :=
  clippedBandNet b n j i < -layerShare n j t ∨
    (1 ≤ i ∧ layerShare n j t < clippedBandNet b n j i)

def selectedLayerEvent (b : ℕ→ℕ) (keep : ℕ→ℕ→ℕ→Prop) (n : ℕ) (t : ℝ) : Prop :=
  ∃ j < bandCount n 0, ∃ i < halvingCount n j, keep n j i ∧ adverseLayer (b n) n j i t

theorem later_rows_interval (n j b : ℕ) :
    laterRows n j b = Ioc (max b (bandLo n j)) (bandHi n j) := by
  rw [laterRows,quotient_rows_interval]
  ext d
  simp only [mem_filter,mem_Ioc,max_lt_iff]
  omega

/-- The divisor component uses all the signed nets. Its cofactor component
uses the same list with the initial net removed, including all floor endpoints. -/
theorem clipped_parity_net_sums (b n j : ℕ) :
    oddSum n (laterRows n j b) =
      ∑ i ∈ range (halvingCount n j), clippedBandNet b n j i ∧
    cofactorSum n (laterRows n j b) =
      ∑ i ∈ range (Nat.log 2 (bandHi n j)), clippedBandNet b n j (i+1) := by
  let x := (n:ℝ)^4
  let a := max b (bandLo n j)
  let u := bandHi n j
  have sums := interval_odd_log_telescope x a u
  have original : oddSum n (laterRows n j b) = intervalOdd x a u := by
    rw [later_rows_interval]
    simp only [oddSum,intervalOdd,rowWeight,surviving,Nat.cast_pow,x,a,u]
  have cofactor : cofactorSum n (laterRows n j b) = intervalOdd (x/2) (a/2) (u/2) := by
    rw [later_rows_interval,cofactorSum,cofactor_interval]
    simp only [intervalOdd,rowWeight,surviving,Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat,div_div,x,a,u]
  constructor
  · exact original.trans sums
  · rw [cofactor]
    have split := interval_odd_halve x a u
    rw [sum_range_succ'] at sums
    change intervalOdd x a u = (∑ i ∈ range (Nat.log 2 u), halvedNet x a u (i+1)) + halvedNet x a u 0 at sums
    simp only [halvedNet,pow_zero,div_one,Nat.div_one] at sums
    change intervalOdd (x/2) (a/2) (u/2) = ∑ i ∈ range (Nat.log 2 u), halvedNet x a u (i+1)
    unfold halvedNet
    linarith only [sums,split]

private theorem layer_share_nonneg (n j : ℕ) {t : ℝ} (tp : 0 ≤ t) : 0 ≤ layerShare n j t := by
  unfold layerShare share
  positivity

private theorem share_sum (n j : ℕ) (t : ℝ) :
    (∑ _i ∈ range (halvingCount n j), layerShare n j t) = share n 0 t := by
  rw [sum_const,card_range,nsmul_eq_mul,layerShare]
  have pos : (0:ℝ) < (halvingCount n j:ℝ) := by unfold halvingCount; positivity
  field_simp

/-- The cofactor sum has the same bounds as the divisor sum after padding the
initial layer with zero. -/
private theorem clipped_cofactor_pad (b n j : ℕ) :
    (∑ i ∈ range (halvingCount n j), if i=0 then 0 else clippedBandNet b n j i) =
      cofactorSum n (laterRows n j b) := by
  rw [halvingCount,sum_range_succ',(clipped_parity_net_sums b n j).2]
  simp

theorem adverse_layer_of_clipped_alarm {b n j : ℕ} {t : ℝ} (tp : 0 ≤ t)
    (alarm : signEvent n t (laterRows n j b)) : ∃ i < halvingCount n j, adverseLayer b n j i t := by
  have paid := share_sum n j t
  rcases alarm with bad|bad
  · have h : (∑ i ∈ range (halvingCount n j), clippedBandNet b n j i) <
        ∑ _i ∈ range (halvingCount n j), -layerShare n j t := by
      rw [sum_neg_distrib,paid,←(clipped_parity_net_sums b n j).1]
      exact bad
    obtain ⟨i,hi,adverse⟩ := exists_lt_of_sum_lt h
    exact ⟨i,mem_range.mp hi,Or.inl adverse⟩
  · have h : (∑ _i ∈ range (halvingCount n j), layerShare n j t) <
        ∑ i ∈ range (halvingCount n j), if i=0 then 0 else clippedBandNet b n j i := by
      rw [paid,clipped_cofactor_pad]
      exact bad
    obtain ⟨i,hi,adverse⟩ := exists_lt_of_sum_lt h
    have nz : i≠0 := by
      rintro rfl
      change layerShare n j t < 0 at adverse
      exact (not_lt_of_ge (layer_share_nonneg n j tp)) adverse
    rw [if_neg nz] at adverse
    exact ⟨i,mem_range.mp hi,Or.inr ⟨by omega,adverse⟩⟩

theorem selected_layers_of_later_event {b : ℕ→ℕ} {n : ℕ} {t : ℝ} (tp : 0 ≤ t)
    (event : laterEvent (b n) n t) : selectedLayerEvent b (fun _ _ _ => True) n t := by
  obtain ⟨j,hj,alarm⟩ := event
  obtain ⟨i,hi,bad⟩ := adverse_layer_of_clipped_alarm tp alarm
  exact ⟨j,hj,i,hi,trivial,bad⟩

private theorem covered_mass {u v : ℕ→ℝ→Prop} (m : ℕ) (t : ℝ)
    (cover : ∀ n, u n t → v n t) : eventMass u m t ≤ eventMass v m t := by
  classical
  unfold eventMass
  apply sum_le_sum
  intro n _
  by_cases hit : u n t
  · simp [hit,cover n hit]
  · simp only [if_neg hit]
    split <;> positivity

private theorem covered_frequency {u v : ℕ→ℝ→Prop} {δ : ℝ}
    (cover : ∀ n {t : ℝ}, 0 ≤ t → u n t → v n t)
    (bound : sharedEventBound v δ) : sharedEventBound u δ := by
  obtain ⟨C,cp,late⟩ := bound
  refine ⟨C,cp,fun A => ?_⟩
  obtain ⟨m,hm,all⟩ := late A
  refine ⟨m,hm,fun i => ?_⟩
  exact (mul_le_mul_of_nonneg_left
    (covered_mass m ((2:ℝ)^i) (fun n => cover n (by positivity))) (by positivity)).trans (all i)

theorem clipped_layer_mass_covers (b : ℕ→ℕ) (m : ℕ) {t : ℝ} (tp : 0 ≤ t) :
    eventMass (fun n => laterEvent (b n) n) m t ≤
      eventMass (selectedLayerEvent b (fun _ _ _ => True)) m t :=
  covered_mass m t fun _ => selected_layers_of_later_event tp

/-- Clipping at a variable divisor leaves the block, constant and thresholds
unchanged when the signed layer count is transferred to the actual tail. -/
theorem later_frequency_of_clipped_layers {b : ℕ→ℕ} {δ : ℝ}
    (bound : sharedEventBound (selectedLayerEvent b (fun _ _ _ => True)) δ) :
    sharedEventBound (fun n => laterEvent (b n) n) δ :=
  covered_frequency (fun _ _ tp => selected_layers_of_later_event tp) bound

theorem odd_frequency_of_clipped_layers {δ : ℝ} (ep : 0 < δ)
    (bound : sharedEventBound (selectedLayerEvent (powerCut (δ/8)) (fun _ _ _ => True)) δ) :
    sharedEventBound oddAlarm δ :=
  odd_frequency_of_tail ep (later_frequency_of_clipped_layers bound)

/-- A run of consecutive signed layers has just two uncancelled odd sums,
one at each endpoint. -/
theorem consecutive_net_endpoints (x : ℝ) (a b i k : ℕ) :
    (∑ q ∈ range k, halvedNet x a b (i+q)) =
      intervalOdd (x/(2:ℝ)^i) (a/2^i) (b/2^i) -
      intervalOdd (x/(2:ℝ)^(i+k)) (a/2^(i+k)) (b/2^(i+k)) := by
  have run := interval_odd_telescope (x/(2:ℝ)^i) (a/2^i) (b/2^i) k
  simp only [halvedNet,div_div,Nat.div_div_eq_div_mul,←pow_add] at run ⊢
  linarith only [run]

/-- Depth zero stands alone. The remaining depths are consecutive groups
of the indicated width, with a short final group when needed. -/
def halvingGroupIndex (width : ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => i/(max 1 width)+1

def halvingGroupRows (width h g : ℕ) : Finset ℕ :=
  (range h).filter (fun i => halvingGroupIndex width i=g)

private theorem group_index_le (w i : ℕ) : halvingGroupIndex w i ≤ i := by
  cases i with
  | zero => rfl
  | succ i => exact Nat.succ_le_succ (Nat.div_le_self ..)

private theorem group_index_zero (w i : ℕ) : halvingGroupIndex w i=0 ↔ i=0 := by
  cases i <;> simp [halvingGroupIndex]

private theorem regroup_layers (w h : ℕ) (f : ℕ→ℝ) :
    (∑ g ∈ range h, ∑ i ∈ halvingGroupRows w h g, f i) = ∑ i ∈ range h, f i := by
  simp only [halvingGroupRows,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  have mem : halvingGroupIndex w i ∈ range h :=
    mem_range.mpr ((group_index_le w i).trans_lt (mem_range.mp hi))
  simp [mem]

private theorem group_above {w h : ℕ} {f : ℕ→ℝ} {s : ℝ}
    (large : (∑ _i ∈ range h, s) < ∑ i ∈ range h, f i) :
    ∃ g < h, (#(halvingGroupRows w h g):ℝ)*s < ∑ i ∈ halvingGroupRows w h g, f i := by
  rw [←regroup_layers w h (fun _ => s),←regroup_layers w h f] at large
  obtain ⟨g,hg,big⟩ := exists_lt_of_sum_lt large
  exact ⟨g,mem_range.mp hg,by simpa only [sum_const,nsmul_eq_mul] using big⟩

/-- Charge the signed sum of a group only after cancellation inside its
consecutive halving depths. Its budget is the sum of their layer shares. -/
def adverseHalvingGroup (w b n j g : ℕ) (t : ℝ) : Prop :=
  let S := halvingGroupRows w (halvingCount n j) g
  let charge := (#S:ℝ)*layerShare n j t
  let net := ∑ i ∈ S, clippedBandNet b n j i
  net < -charge ∨ (1 ≤ g ∧ charge < net)

def groupedLayerEvent (b : ℕ→ℕ) (width : ℕ→ℕ→ℕ) (n : ℕ) (t : ℝ) : Prop :=
  ∃ j < bandCount n 0, ∃ g < halvingCount n j, adverseHalvingGroup (width n j) (b n) n j g t

theorem adverse_group_of_clipped_alarm (w : ℕ) {b n j : ℕ} {t : ℝ} (tp : 0 ≤ t)
    (alarm : signEvent n t (laterRows n j b)) :
    ∃ g < halvingCount n j, adverseHalvingGroup w b n j g t := by
  let q := layerShare n j t
  let h := halvingCount n j
  let f := clippedBandNet b n j
  have paid := share_sum n j t
  rcases alarm with bad|bad
  · have big : (∑ _i ∈ range h, q) < ∑ i ∈ range h, -f i := by
      dsimp only [q,h,f]
      rw [sum_neg_distrib,paid,←(clipped_parity_net_sums b n j).1]
      linarith only [bad]
    obtain ⟨g,hg,excess⟩ := group_above (w:=w) big
    rw [sum_neg_distrib] at excess
    refine ⟨g,hg,Or.inl ?_⟩
    change (∑ i ∈ halvingGroupRows w h g, f i) < -((#(halvingGroupRows w h g):ℝ)*q)
    linarith only [excess]
  · have big : (∑ _i ∈ range h, q) < ∑ i ∈ range h, if i=0 then 0 else f i := by
      dsimp only [q,h,f]
      rw [paid,clipped_cofactor_pad]
      exact bad
    obtain ⟨g,hg,excess⟩ := group_above (w:=w) big
    let S := halvingGroupRows w h g
    change (#S:ℝ)*q < ∑ i ∈ S, if i=0 then 0 else f i at excess
    have gp : 1 ≤ g := by
      by_contra! zero
      have zg : g=0 := by omega
      have none : (∑ i ∈ S, if i=0 then 0 else f i)=0 := by
        apply sum_eq_zero
        intro i hi
        have fact : halvingGroupIndex w i=g := (mem_filter.mp hi).2
        rw [if_pos ((group_index_zero w i).mp (fact.trans zg))]
      rw [none] at excess
      exact (not_lt_of_ge (mul_nonneg (Nat.cast_nonneg _) (layer_share_nonneg n j tp))) excess
    have nonzero (i : ℕ) (hi : i∈S) : i≠0 := by
      have fact : halvingGroupIndex w i=g := (mem_filter.mp hi).2
      rintro rfl
      simp only [halvingGroupIndex] at fact
      omega
    have same : (∑ i ∈ S, if i=0 then 0 else f i) = ∑ i ∈ S, f i :=
      sum_congr rfl (fun i hi => if_neg (nonzero i hi))
    rw [same] at excess
    exact ⟨g,hg,Or.inr ⟨gp,excess⟩⟩

theorem adverse_layer_in_group {w b n j g : ℕ} {t : ℝ}
    (hit : adverseHalvingGroup w b n j g t) :
    ∃ i ∈ halvingGroupRows w (halvingCount n j) g, adverseLayer b n j i t := by
  let S := halvingGroupRows w (halvingCount n j) g
  let f := clippedBandNet b n j
  let q := layerShare n j t
  rcases hit with low | ⟨gp,high⟩
  · have h : (∑ i ∈ S, f i) < ∑ _i ∈ S, -q := by
      rw [sum_const,nsmul_eq_mul,mul_neg]
      exact low
    obtain ⟨i,hi,excess⟩ := exists_lt_of_sum_lt h
    exact ⟨i,hi,Or.inl excess⟩
  · have h : (∑ _i ∈ S, q) < ∑ i ∈ S, f i := by
      rw [sum_const,nsmul_eq_mul]
      exact high
    obtain ⟨i,hi,excess⟩ := exists_lt_of_sum_lt h
    have level : halvingGroupIndex w i=g := (mem_filter.mp hi).2
    exact ⟨i,hi,Or.inr ⟨gp.trans (level ▸ group_index_le w i),excess⟩⟩

theorem grouped_layers_of_later_event (width : ℕ→ℕ→ℕ) {b : ℕ→ℕ} {n : ℕ} {t : ℝ}
    (tp : 0 ≤ t) (event : laterEvent (b n) n t) : groupedLayerEvent b width n t := by
  obtain ⟨j,hj,alarm⟩ := event
  obtain ⟨g,hg,bad⟩ := adverse_group_of_clipped_alarm (width n j) tp alarm
  exact ⟨j,hj,g,hg,bad⟩

theorem individual_layer_of_grouped_event {width : ℕ→ℕ→ℕ} {b : ℕ→ℕ} {n : ℕ} {t : ℝ}
    (event : groupedLayerEvent b width n t) : selectedLayerEvent b (fun _ _ _ => True) n t := by
  obtain ⟨j,hj,g,_,alarm⟩ := event
  obtain ⟨i,hi,bad⟩ := adverse_layer_in_group alarm
  exact ⟨j,hj,i,mem_range.mp (mem_filter.mp hi).1,trivial,bad⟩

/-- Grouping retains all actual parity alarms and can discard opposing
individual excursions, on the same block at the same real threshold. -/
theorem grouped_layer_mass_bounds (b : ℕ→ℕ) (width : ℕ→ℕ→ℕ) (m : ℕ) {t : ℝ} (tp : 0 ≤ t) :
    eventMass (fun n => laterEvent (b n) n) m t ≤ eventMass (groupedLayerEvent b width) m t ∧
    eventMass (groupedLayerEvent b width) m t ≤ eventMass (selectedLayerEvent b (fun _ _ _ => True)) m t :=
  ⟨covered_mass m t (fun _ => grouped_layers_of_later_event width tp),
   covered_mass m t (fun _ => individual_layer_of_grouped_event)⟩

theorem odd_frequency_of_grouped_halvings {δ : ℝ} (ep : 0 < δ) {width : ℕ→ℕ→ℕ}
    (bound : sharedEventBound (groupedLayerEvent (powerCut (δ/8)) width) δ) :
    sharedEventBound oddAlarm δ :=
  odd_frequency_of_tail ep (covered_frequency (fun _ _ tp => grouped_layers_of_later_event width tp) bound)

/-- At the fourth-power scale 625, the singleton divisor 256 has two
opposite halving contributions of magnitude at least 1/5. A consecutive
pair cancels them exactly. This example is for the interval (255,256]. -/
theorem fourth_power_paired_cancellation :
    halvedNet ((5:ℝ)^4) 255 256 7 ≤ -(1/5) ∧
    1/5 ≤ halvedNet ((5:ℝ)^4) 255 256 8 ∧
    (∑ i ∈ halvingGroupRows 2 9 4, halvedNet ((5:ℝ)^4) 255 256 i)=0 := by
  let w := surviving ((625:ℝ)/256)
  have lower := RiemannGaussian.AlpogeMined.fixedBandHalfKernel_second_lower
    (z:=(625:ℝ)/512) (by norm_num) (by norm_num)
  change (1:ℝ)/5 ≤ surviving (2*(625/512)) at lower
  rw [show (2:ℝ)*(625/512)=625/256 by norm_num] at lower
  have left : halvedNet ((5:ℝ)^4) 255 256 7 = -w := by
    unfold halvedNet intervalNet
    rw [show Ioc (255/2^7:ℕ) (256/2^7)=({2}:Finset ℕ) by decide,sum_singleton,
        ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    norm_num [w]
  have right : halvedNet ((5:ℝ)^4) 255 256 8 = w := by
    unfold halvedNet intervalNet
    rw [show Ioc (255/2^8:ℕ) (256/2^8)=({1}:Finset ℕ) by decide,sum_singleton]
    norm_num [w]
  rw [left,right,show halvingGroupRows 2 9 4=({7,8}:Finset ℕ) by decide]
  simp only [sum_insert (by decide : (7:ℕ) ∉ ({8}:Finset ℕ)),sum_singleton,left,right,neg_add_cancel]
  exact ⟨neg_le_neg lower,lower,trivial⟩

end RiemannReduction.ShortTail.LossFrequency
