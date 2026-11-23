import OddKernelCells
import OddTailCriterion

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Real

/-- The summation-by-parts prefixes start at a, the excluded left endpoint.
The coefficient of that endpoint therefore vanishes. -/
theorem odd_abel_anchored_identity {a b : ℕ} (ab : a<b) (w : ℕ → ℝ) :
    oddWeighted a b w = w b*(oddPrefix b-oddPrefix a) -
      ∑ k ∈ Ioc a (b-1), (w (k+1)-w k)*(oddPrefix k-oddPrefix a) := by
  have base := sum_Ioc_by_parts w oddMu ab
  simp only [smul_eq_mul] at base
  have standard : oddWeighted a b w = w b*oddPrefix b-w (a+1)*oddPrefix a -
      ∑ k ∈ Ioc a (b-1), (w (k+1)-w k)*oddPrefix k := by
    unfold oddPrefix
    rw [←base]
    exact sum_congr rfl fun _ _ => mul_comm ..
  have ranges : Ioc a (b-1) = Ico (a+1) b := by
    ext k
    simp only [mem_Ioc,mem_Ico]
    omega
  have telescopes : (∑ k ∈ Ioc a (b-1), (w (k+1)-w k))=w b-w (a+1) := by
    rw [ranges,sum_Ico_eq_sub _ ab,sum_range_sub,sum_range_sub]
    ring
  rw [standard]
  simp only [mul_sub,sum_sub_distrib,←sum_mul,telescopes]
  ring

theorem odd_abel_anchored_bound {a b : ℕ} (w : ℕ → ℝ) {H : ℝ} (hp : 0≤H)
    (control : ∀ k ∈ Ioc a b, |oddPrefix k-oddPrefix a| ≤ H) :
    |oddWeighted a b w| ≤ H*(|w b|+∑ k ∈ Ioc a (b-1), |w (k+1)-w k|) := by
  by_cases ab : a<b
  · have edge : |w b*(oddPrefix b-oddPrefix a)| ≤ |w b| * H := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (control _ (mem_Ioc.mpr ⟨ab,le_rfl⟩)) (abs_nonneg _)
    have mid := (abs_sum_le_sum_abs (fun k => (w (k+1)-w k)*(oddPrefix k-oddPrefix a))
      (Ioc a (b-1))).trans (sum_le_sum (g:=fun k => |w (k+1)-w k| * H) (by
        intro k hk
        rw [abs_mul]
        obtain ⟨lo,hi⟩ := mem_Ioc.mp hk
        exact mul_le_mul_of_nonneg_left (control k (mem_Ioc.mpr ⟨lo,by omega⟩)) (abs_nonneg _)))
    rw [←sum_mul] at mid
    rw [odd_abel_anchored_identity ab]
    exact ((abs_sub ..).trans (add_le_add edge mid)).trans_eq (by ring)
  · rw [oddWeighted,Ioc_eq_empty_of_le (le_of_not_gt ab),sum_empty,abs_zero]
    positivity

def oscillationCost (j : ℕ) : ℝ := 10*kernelConstant*(1+log (2*((2^j:ℕ):ℝ)))

private theorem oscillationCost_pos (j : ℕ) : 0<oscillationCost j := by
  have q : (1:ℝ) ≤ ((2^j:ℕ):ℝ) := by exact_mod_cast Nat.one_le_pow j 2 (by decide)
  have lg : 0≤log (2*((2^j:ℕ):ℝ)) := log_nonneg (by linarith)
  unfold oscillationCost kernelConstant
  positivity

/-- The two upper bounds use only oscillations of the odd Möbius prefix
inside the corresponding actual divisor interval and its halved interval. -/
theorem both_signed_of_local_oscillations {n j : ℕ} {U V : ℝ} (up : 0≤U) (vp : 0≤V)
    (original : ∀ k ∈ Ioc (bandLo n j) (bandHi n j), |oddPrefix k-oddPrefix (bandLo n j)|≤U)
    (halved : ∀ k ∈ Ioc (bandLo n j/2) (bandHi n j/2), |oddPrefix k-oddPrefix (bandLo n j/2)|≤V) :
    |oddSum n (quotientBandRows n 0 j)| ≤ U*oscillationCost j ∧
    |cofactorSum n (quotientBandRows n 0 j)| ≤ V*oscillationCost j := by
  rw [(odd_rows_abel_input n j).1,(odd_rows_abel_input n j).2]
  have applyBand (a b : ℕ) (p : ℕ → ℕ) (H : ℝ) (hp : 0≤H) (pm : Monotone p)
      (source : Set.MapsTo p (Set.Icc (a+1) b) (Set.Icc (bandLo n j+1) (bandHi n j)))
      (bound : ∀ k ∈ Ioc a b, |oddPrefix k-oddPrefix a|≤H) :
      |oddWeighted a b (fun k => rowWeight n (p k))| ≤ H*oscillationCost j := by
    by_cases ab : a<b
    · let w := fun k => rowWeight n (p k)
      have shape := variation_on_original_samples ab pm source signed_kernel_quotient_cells
      have oneEdge : |w b|+(∑ k ∈ Ioc a (b-1), |w (k+1)-w k|) ≤ endpointVariation a b w := by
        unfold endpointVariation
        linarith only [abs_nonneg (w (a+1))]
      exact (odd_abel_anchored_bound w hp bound).trans
        (mul_le_mul_of_nonneg_left (oneEdge.trans shape) hp)
    · rw [oddWeighted,Ioc_eq_empty_of_le (by omega),sum_empty,abs_zero]
      exact mul_nonneg hp (oscillationCost_pos j).le
  constructor
  · exact applyBand _ _ id U up monotone_id (fun _ h => h) original
  · apply applyBand _ _ (fun k => 2*k) V vp (fun _ _ h => Nat.mul_le_mul_left 2 h) _ halved
    intro k hk
    rcases hk with ⟨lo,hi⟩
    change bandLo n j+1≤2*k ∧ 2*k≤bandHi n j
    exact ⟨by omega,by omega⟩

/-- An excursion of the ordinary odd Möbius prefix from the excluded
endpoint. All samples of either channel stay inside its own interval. -/
def hasLocalExcursion (a b : ℕ) (z : ℝ) : Prop :=
  ∃ k ∈ Ioc a b, z < |oddPrefix k-oddPrefix a|

def oddLocalEvent (n : ℕ) (t : ℝ) : Prop :=
  ∃ j < bandCount n 0,
    hasLocalExcursion (bandLo n j) (bandHi n j) (share n 0 t/oscillationCost j) ∨
    hasLocalExcursion (bandLo n j/2) (bandHi n j/2) (share n 0 t/oscillationCost j)

/-- Every original signed alarm has a local prefix witness in the same
sample and the same original quotient bin. -/
theorem local_event_of_odd_alarm {n : ℕ} {t : ℝ} (tp : 0≤t) (hit : oddAlarm n t) :
    oddLocalEvent n t := by
  obtain ⟨j,hj,large⟩ := hit
  refine ⟨j,hj,?_⟩
  by_contra none
  have src := not_or.mp none
  let z := share n 0 t/oscillationCost j
  have zp : 0≤z := by dsimp [z,share]; positivity [(oscillationCost_pos j).le]
  have bounds {a b : ℕ} (no : ¬hasLocalExcursion a b z) :
      ∀ k ∈ Ioc a b, |oddPrefix k-oddPrefix a|≤z :=
    fun k hk => le_of_not_gt fun high => no ⟨k,hk,high⟩
  obtain ⟨orig,half⟩ := both_signed_of_local_oscillations zp zp (bounds src.1) (bounds src.2)
  have cancel : z*oscillationCost j=share n 0 t := div_mul_cancel₀ _ (oscillationCost_pos j).ne'
  rw [cancel] at orig half
  rcases large with left|right
  · linarith only [left,(neg_le_abs _).trans orig]
  · linarith only [right,(le_abs_self _).trans half]

/-- A common, slightly lower excursion threshold, explicit in n and
independent of j. -/
def normalizedExcursionThreshold (n : ℕ) (t : ℝ) : ℝ :=
  t*(n:ℝ)^2/(80*kernelConstant*(1+8*log n)^2)

theorem normalized_threshold_le {n j : ℕ} (hn : 1≤n) (hj : j<bandCount n 0)
    {t : ℝ} (tp : 0≤t) :
    normalizedExcursionThreshold n t ≤ share n 0 t/oscillationCost j := by
  let Q := (2:ℕ)^j
  have qp : 0<Q := by dsimp [Q]; positivity
  have jr : j≤Nat.log 2 (n^4) := by simpa [bandCount] using hj
  have qn : Q≤n^4 := (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) jr).trans
    (Nat.pow_log_le_self _ (by positivity))
  have qR : (0:ℝ)<Q := by exact_mod_cast qp
  have nR : (Q:ℝ)≤(n:ℝ)^4 := by exact_mod_cast qn
  have L := log_le_log qR nR
  rw [log_pow,Nat.cast_ofNat] at L
  have ln := log_natCast_nonneg n
  have p := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have budget : oscillationCost j ≤ 20*kernelConstant*(1+8*log n) := by
    change 10*kernelConstant*(1+log (2*(Q:ℝ))) ≤ _
    rw [log_mul (by norm_num) qR.ne']
    have h := mul_le_mul_of_nonneg_left (show 1+(log 2+log (Q:ℝ))≤2*(1+8*log n) by linarith only [L,p,ln])
      (show 0≤10*kernelConstant by positivity [kernelConstant_nonneg])
    linarith only [h]
  have bp : (0:ℝ)<bandCount n 0 := by unfold bandCount; positivity
  have total : (4*(bandCount n 0:ℝ))*oscillationCost j ≤ 80*kernelConstant*(1+8*log n)^2 := by
    calc
      _ ≤ (4*(1+8*log n))*(20*kernelConstant*(1+8*log n)) := mul_le_mul
        (by linarith only [band_count_log hn]) budget (oscillationCost_pos j).le (by positivity)
      _ = _ := by ring
  unfold normalizedExcursionThreshold share
  simp only [div_div]
  rw [show 2*(bandCount n 0:ℝ)*2 = 4*(bandCount n 0:ℝ) by ring]
  exact div_le_div_of_nonneg_left (by positivity)
    (mul_pos (by positivity) (oscillationCost_pos j)) total

def normalizedLocalEvent (n : ℕ) (t : ℝ) : Prop :=
  ∃ j < bandCount n 0,
    hasLocalExcursion (bandLo n j) (bandHi n j) (normalizedExcursionThreshold n t) ∨
    hasLocalExcursion (bandLo n j/2) (bandHi n j/2) (normalizedExcursionThreshold n t)

theorem normalized_event_of_odd_alarm {n : ℕ} (hn : 1≤n) {t : ℝ} (tp : 0≤t) (hit : oddAlarm n t) :
    normalizedLocalEvent n t := by
  obtain ⟨j,hj,exc⟩ := local_event_of_odd_alarm tp hit
  refine ⟨j,hj,?_⟩
  have lower {a b : ℕ} : hasLocalExcursion a b (share n 0 t/oscillationCost j) →
      hasLocalExcursion a b (normalizedExcursionThreshold n t) := by
    rintro ⟨k,hk,big⟩
    exact ⟨k,hk,(normalized_threshold_le hn hj tp).trans_lt big⟩
  exact exc.imp lower lower

theorem local_event_mass_covers {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (tp : 0≤t) :
    eventMass oddAlarm m t ≤ eventMass normalizedLocalEvent m t := by
  classical
  unfold eventMass
  apply sum_le_sum
  intro n hn
  by_cases hit : oddAlarm n t
  · simp [hit,normalized_event_of_odd_alarm (hm.trans (mem_Icc.mp hn).1) tp hit]
  · simp only [if_neg hit]
    split <;> positivity

/-- A count of genuine localized odd Möbius excursions gives the original
signed frequency bound, retaining the same block and all its thresholds. -/
theorem odd_frequency_of_local_events {δ : ℝ} (bound : sharedEventBound normalizedLocalEvent δ) :
    sharedEventBound oddAlarm δ := by
  obtain ⟨C,cp,late⟩ := bound
  refine ⟨C,cp,fun A => ?_⟩
  obtain ⟨m,hm,all⟩ := late (max A 1)
  refine ⟨m,(le_max_left ..).trans hm,fun j => ?_⟩
  exact (mul_le_mul_of_nonneg_left
    (local_event_mass_covers ((le_max_right ..).trans hm) (show 0≤(2:ℝ)^j by positivity))
    (by positivity)).trans (all j)

end RiemannReduction.ShortTail.LossFrequency
