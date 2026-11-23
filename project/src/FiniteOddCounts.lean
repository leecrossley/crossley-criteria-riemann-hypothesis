import QuotientSignFold

/-! Exact arithmetic for the observed odd-sign alarms on [16,256]. The input
`CertificateBridge` connects the flags obtained from interval arithmetic
with the arithmetic predicate. Its finite five thresholds are explicit. -/

namespace RiemannReduction.ShortTail.LossFrequency.FiniteOdd
open Finset

/-- At each n from 16 through 256 this records the number of dyadic thresholds
1, 2, 4, 8, 16 strictly below the externally enclosed maximum excess. -/
def levels : List ℕ :=
  [0,2,4,2,2,1,0,1,0,0,3,3,2,3,2,3,2,4,3,0,2,3,
   4,3,3,3,2,2,4,1,2,3,2,4,2,3,3,3,4,3,3,3,1,3,
   4,3,3,2,2,2,1,3,4,2,2,3,3,3,1,2,2,3,2,3,4,3,
   1,2,3,2,2,2,2,3,4,1,3,3,3,3,3,1,1,2,3,3,2,0,
   2,4,3,3,2,4,4,4,3,3,0,2,1,3,2,4,4,3,3,1,2,4,
   3,3,3,3,3,3,3,2,3,3,2,3,4,4,3,3,3,3,3,4,4,3,
   2,3,2,3,3,3,3,3,2,3,3,3,2,2,3,4,4,4,3,3,3,3,
   3,3,3,4,4,4,2,3,0,1,4,2,2,3,3,3,3,4,3,3,3,4,
   4,3,3,4,3,3,2,2,3,3,3,3,2,2,3,3,3,3,4,3,2,4,
   4,4,4,4,4,3,3,4,4,3,3,2,2,3,3,3,3,3,2,2,3,2,
   4,3,1,3,2,2,1,2,4,4,3,4,4,3,3,4,3,3,3,3,4]

def bucket (n : ℕ) : ℕ := levels[n-16]?.getD 0
def indices (j : ℕ) : Finset ℕ := (Icc 16 256).filter (fun n => j<bucket n)

/-- A common denominator for the 241 individual reciprocal weights. -/
def denominator : ℕ := 16674490806895842671659008751776385350270324508909651849955453691538889375930032935391666564679008085339616000

def numerator (j : ℕ) : ℕ := ∑ n ∈ indices j, denominator / n

private theorem table_size : levels.length=241 := by decide +kernel
private theorem capped : ∀ n ∈ Icc 16 256, bucket n ≤ 4 := by decide +kernel
private theorem denominator_positive : 0<denominator := by decide +kernel
private theorem divisible : ∀ n ∈ Icc 16 256, n ∣ denominator := by decide +kernel

theorem exact_counts :
    (indices 0).card=233 ∧ (indices 1).card=218 ∧
    (indices 2).card=163 ∧ (indices 3).card=48 ∧ (indices 4).card=0 := by
  decide +kernel

/-- All sums of weights use the same positive denominator. -/
theorem exact_numerators :
    numerator 0=42750471118496751433815329724516430548919677315582093184518891406332918522224360296322448387769948137751414777 ∧
    numerator 1=38855398327060593802980143706031753239260463848577266483674034106111202766892307125753538533815549179716353977 ∧
    numerator 2=26198583225162628152977651050506078564999011212498206774981270388817209662268997694677335250223474639638768877 ∧
    numerator 3=7512977067285789343085979610697531944372875896452082209362854783690243699562638417143258706515520575241935623 := by
  decide +kernel

theorem no_later_indices {j : ℕ} (hj : 4≤j) : indices j=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨span,level⟩ := mem_filter.mp hn
  exact (not_lt_of_ge ((capped n span).trans hj)) level

private theorem small_bound (j : ℕ) (hj : j<4) :
    10*2^j*numerator j≤63*denominator := by
  obtain ⟨a,b,c,d⟩ := exact_numerators
  interval_cases j <;> simp only [a,b,c,d] <;> decide +kernel

theorem integer_bound (j : ℕ) : 10*2^j*numerator j≤63*denominator := by
  by_cases low : j<4
  · exact small_bound j low
  · simp [numerator,no_later_indices (le_of_not_gt low)]

/-- The enclosure computation establishes the flags only through t=16.
Monotonicity of the original arithmetic predicate supplies every larger t. -/
def CertificateBridge : Prop :=
  ∀ n ∈ Icc 16 256, ∀ j ≤ 4,
    oddAlarm n ((2:ℝ)^j) ↔ j < bucket n

private theorem alarm_antitone (n : ℕ) {u v : ℝ} (uv : u≤v) (hit : oddAlarm n v) :
    oddAlarm n u := by
  have scale : share n 0 u ≤ share n 0 v := by unfold share; gcongr
  obtain ⟨j,ok,left|right⟩ := hit
  · exact ⟨j,ok,Or.inl (left.trans_le (neg_le_neg scale))⟩
  · exact ⟨j,ok,Or.inr (scale.trans_lt right)⟩

theorem all_flags (cert : CertificateBridge) {n : ℕ} (span : n ∈ Icc 16 256)
    (j : ℕ) : oddAlarm n ((2:ℝ)^j) ↔ j<bucket n := by
  by_cases low : j≤4
  · exact cert n span j low
  · have ge : 4≤j := by omega
    have impossible : ¬oddAlarm n ((2:ℝ)^4) := fun h =>
      (not_lt_of_ge (capped n span)) ((cert n span 4 le_rfl).mp h)
    have larger : (2:ℝ)^4≤2^j := pow_le_pow_right₀ (by norm_num) ge
    exact iff_of_false (fun h => impossible (alarm_antitone n larger h))
      (not_lt_of_ge ((capped n span).trans ge))

open Classical in
theorem actual_indices (cert : CertificateBridge) (j : ℕ) :
    (Icc 16 256).filter (fun n => oddAlarm n ((2:ℝ)^j)) = indices j := by
  ext n
  by_cases span : n∈Icc 16 256
  · simp only [indices,mem_filter,span,true_and]
    exact all_flags cert span j
  · simp [indices,span]

open Classical in
noncomputable def actualFrequency (j : ℕ) : ℝ :=
  ∑ n ∈ Icc 16 256, if oddAlarm n ((2:ℝ)^j) then (n:ℝ)⁻¹ else 0

theorem exact_frequency (cert : CertificateBridge) (j : ℕ) :
    actualFrequency j=(numerator j:ℝ)/denominator := by
  classical
  rw [actualFrequency,←sum_filter,actual_indices cert j,numerator,Nat.cast_sum,Finset.sum_div]
  apply sum_congr rfl
  intro n hn
  have span := (mem_filter.mp hn).1
  have np : (n:ℝ)≠0 := by
    have lo := (mem_Icc.mp span).1
    exact_mod_cast (show n≠0 by omega)
  have dp : (denominator:ℝ)≠0 := by exact_mod_cast denominator_positive.ne'
  have prod : ((denominator/n:ℕ):ℝ)*n=denominator := by
    exact_mod_cast Nat.div_mul_cancel (divisible n span)
  field_simp [np,dp]
  linarith only [prod]

/-- Finite conditional certificate on this one entire block. All dyadic
thresholds have one bound, with exact harmonic weights. -/
theorem all_dyadic (cert : CertificateBridge) (j : ℕ) :
    (2:ℝ)^j*actualFrequency j ≤ 63/10 := by
  rw [exact_frequency cert j,mul_div_assoc']
  have dp : 0<(denominator:ℝ) := by exact_mod_cast denominator_positive
  apply (div_le_iff₀ dp).mpr
  have bound : (10:ℝ)*2^j*(numerator j:ℝ)≤63*(denominator:ℝ) := by
    exact_mod_cast integer_bound j
  linarith only [bound]

end RiemannReduction.ShortTail.LossFrequency.FiniteOdd
