import HalvingIntervals

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Real

/-- Only the first depth has a one-sided individual threshold. -/
theorem adverse_layer_zero (b n j : ℕ) (t : ℝ) :
    adverseLayer b n j 0 t ↔ clippedBandNet b n j 0 < -layerShare n j t := by
  simp [adverseLayer]

theorem adverse_layer_positive_depth {i : ℕ} (hi : 1 ≤ i) (b n j : ℕ) (t : ℝ) :
    adverseLayer b n j i t ↔ layerShare n j t < |clippedBandNet b n j i| := by
  rw [adverseLayer,lt_abs]
  simp only [hi,true_and]
  constructor
  · rintro (h|h)
    · exact Or.inr (by linarith only [h])
    · exact Or.inl h
  · rintro (h|h)
    · exact Or.inr h
    · exact Or.inl (by linarith only [h])

theorem first_layer_difference (b n j : ℕ) :
    clippedBandNet b n j 0 = oddSum n (laterRows n j b)-cofactorSum n (laterRows n j b) := by
  obtain ⟨odd,cof⟩ := clipped_parity_net_sums b n j
  rw [halvingCount,sum_range_succ'] at odd
  linarith only [odd,cof]

/-- The two original sums share every halving after the first. Their joint
alarm has two exact branches, a negative initial gap or a signed product. -/
theorem joint_alarm_factorization (u v s : ℝ) :
    (u < -s ∨ s < v) ↔ u-v < -2*s ∨ s*(s+u-v)<u*v := by
  constructor
  · intro alarm
    by_cases gap : u-v < -2*s
    · exact Or.inl gap
    · right
      rcases alarm with lo|hi
      · have p := mul_pos_of_neg_of_neg (show v-s<0 by linarith only [lo,le_of_not_gt gap])
            (show u+s<0 by linarith only [lo])
        linarith only [p]
      · have p := mul_pos (sub_pos.mpr hi) (show 0<u+s by linarith only [hi,le_of_not_gt gap])
        linarith only [p]
  · intro h
    by_contra! quiet
    have p := mul_nonpos_of_nonpos_of_nonneg (show v-s ≤ 0 by linarith only [quiet.2])
      (show 0 ≤ u+s by linarith only [quiet.1])
    rcases h with gap|prod
    · linarith only [gap,quiet.1,quiet.2]
    · linarith only [prod,p]

theorem clipped_sign_event_exact (b n j : ℕ) (t : ℝ) :
    signEvent n t (laterRows n j b) ↔
      clippedBandNet b n j 0 < -2*share n 0 t ∨
        share n 0 t*(share n 0 t+clippedBandNet b n j 0) <
          oddSum n (laterRows n j b)*cofactorSum n (laterRows n j b) := by
  rw [signEvent,first_layer_difference,joint_alarm_factorization]
  ring_nf

/-- Away from a negative first-layer crossing, a genuine alarm requires
a positive product of the two complete signed sums on that bin. -/
theorem first_or_joint_product {u v s : ℝ} (sp : 0 ≤ s) (hit : u < -s ∨ s < v) :
    u-v < -(s/2) ∨ s^2/2 < u*v := by
  by_cases gap : u-v < -(s/2)
  · exact Or.inl gap
  · right
    rcases (joint_alarm_factorization u v s).mp hit with big|prod
    · linarith only [big,sp,le_of_not_gt gap]
    · have p := mul_le_mul_of_nonneg_left (show s/2 ≤ s+u-v by linarith only [le_of_not_gt gap]) sp
      linarith only [p,prod]

def firstLayerEvent (b : ℕ→ℕ) (n : ℕ) (t : ℝ) : Prop :=
  ∃ j < bandCount n 0, clippedBandNet (b n) n j 0 < -share n 0 t

/-- Cross terms keep their signs inside every product. Only after an entire
bin is summed is its positive part charged. -/
def overlapAt (b n : ℕ) : ℝ :=
  (∑ j ∈ range (bandCount n 0),
    max (oddSum n (laterRows n j b)*cofactorSum n (laterRows n j b)) 0)/(share n 0 1)^2

def overlapBlock (b : ℕ→ℕ) (m : ℕ) : ℝ :=
  ∑ n ∈ Icc m (m^2), overlapAt (b n) n*(n:ℝ)⁻¹

theorem overlap_nonneg (b n : ℕ) : 0 ≤ overlapAt b n := by
  apply div_nonneg (sum_nonneg (fun j _ => le_max_right _ _)) (sq_nonneg _)

private theorem charge_overlap {b : ℕ→ℕ} {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (tp : 0 ≤ t)
    (hit : laterEvent (b n) n t) (quiet : ¬firstLayerEvent b n (t/2)) :
    t^2 ≤ 2*overlapAt (b n) n := by
  obtain ⟨j,hj,one⟩ := hit
  let u := oddSum n (laterRows n j (b n))
  let v := cofactorSum n (laterRows n j (b n))
  let s := share n 0 t
  have sp : 0 ≤ s := by dsimp [s,share]; positivity
  have part := first_or_joint_product (u:=u) (v:=v) sp one
  have grow : 0<share n 0 1 := by
    have np : 0<(n:ℝ) := Nat.cast_pos.mpr (by omega)
    unfold share bandCount
    positivity
  have scale : s=t*share n 0 1 := by dsimp [s,share]; ring
  have half : share n 0 (t/2)=s/2 := by dsimp [s,share]; ring
  rcases part with gap|prod
  · exact (quiet ⟨j,hj,by rw [first_layer_difference,half]; exact gap⟩).elim
  · let F (j : ℕ) := max (oddSum n (laterRows n j (b n))*cofactorSum n (laterRows n j (b n))) 0
    have Fpos (i : ℕ) (_ : i ∈ range (bandCount n 0)) : 0 ≤ F i := le_max_right _ 0
    have upper : u*v ≤ ∑ i ∈ range (bandCount n 0), F i :=
      (show u*v ≤ F j from le_max_left _ 0).trans (single_le_sum Fpos (mem_range.mpr hj))
    unfold overlapAt
    change t^2 ≤ 2*((∑ i ∈ range (bandCount n 0), F i)/(share n 0 1)^2)
    rw [←mul_div_assoc]
    apply (le_div_iff₀ (pow_pos grow 2)).mpr
    rw [scale] at prod
    linarith only [prod,upper]

/-- A sign-aware frequency inequality, valid on every full block. Once the
first-layer term is accounted for the remaining cost decays as 1/t². -/
theorem clipped_frequency_of_overlap (b : ℕ→ℕ) {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (tp : 0 ≤ t) :
    t^2*eventMass (fun n => laterEvent (b n) n) m t ≤ 
      t^2*eventMass (firstLayerEvent b) m (t/2) + 2*overlapBlock b m := by
  classical
  unfold eventMass overlapBlock
  simp only [mul_sum,←sum_add_distrib]
  apply sum_le_sum
  intro n hn
  have non := overlap_nonneg (b n) n
  have pos : 0 ≤ (n:ℝ)⁻¹ := by positivity
  by_cases hit : laterEvent (b n) n t
  · by_cases early : firstLayerEvent b n (t/2)
    · simp only [if_pos hit,if_pos early]
      linarith only [mul_nonneg non pos]
    · have charge := mul_le_mul_of_nonneg_right (charge_overlap (hm.trans (mem_Icc.mp hn).1) tp hit early) pos
      simp only [if_pos hit,if_neg early,mul_zero,zero_add]
      linarith only [charge]
  · simp only [if_neg hit,mul_zero]
    split <;> positivity

end RiemannReduction.ShortTail.LossFrequency
