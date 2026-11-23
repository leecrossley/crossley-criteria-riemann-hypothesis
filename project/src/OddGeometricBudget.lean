import OddAlarmCut
import OddAbelBands
import DistantMobiusPairs

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Real

def separateMass (n j : ℕ) : ℝ :=
  let S := quotientBandRows n 0 j
  max (-oddSum n S) 0 + max (cofactorSum n S) 0

def separatedScore (n : ℕ) : ℝ :=
  (∑ j ∈ range (bandCount n 0), separateMass n j)/(n:ℝ)^2

def geometricEvent (n : ℕ) (t : ℝ) : Prop :=
  ∃ j < bandCount n 0, 1 ≤ j ∧
    (oddSum n (quotientBandRows n 0 j) < -(t*(n:ℝ)^2/(2:ℝ)^(j+1)) ∨
     t*(n:ℝ)^2/(2:ℝ)^(j+1) < cofactorSum n (quotientBandRows n 0 j))

private theorem zero_band (n : ℕ) : quotientBandRows n 0 0=∅ := by
  rw [quotient_rows_interval]
  apply Ioc_eq_empty_of_le
  exact (min_le_left ..).trans (by simp [bandLo])

/-- Summing the two unfavorable signs gives a pointwise majorant before
spending any threshold across the different divisor ranges. -/
theorem score_le_separated (n : ℕ) : score n ≤ separatedScore n := by
  have high : highPart n 0=late n := by
    apply filter_eq_self.mpr
    intro d hd
    have v := mem_Ioc.mp (mem_filter.mp hd).1
    omega
  have parts := band_split n 0
  rw [highSum,high] at parts
  change ∑ j ∈ range (bandCount n 0), bandSum n 0 j = core n at parts
  have bound (j : ℕ) : -bandSum n 0 j ≤ separateMass n j := by
    let S := quotientBandRows n 0 j
    have eq : bandSum n 0 j=oddSum n S-cofactorSum n S := fold_signed_rows S (rowWeight n)
    exact (by
      change -bandSum n 0 j ≤ max (-oddSum n S) 0+max (cofactorSum n S) 0
      linarith only [eq,le_max_left (-oddSum n S) 0,le_max_left (cofactorSum n S) 0])
  have nonneg (j : ℕ) : 0 ≤ separateMass n j := add_nonneg (le_max_right ..) (le_max_right ..)
  have h := sum_le_sum (s:=range (bandCount n 0)) fun j _ => bound j
  rw [sum_neg_distrib,parts] at h
  exact div_le_div_of_nonneg_right (max_le h (sum_nonneg fun j _ => nonneg j)) (sq_nonneg _)

private theorem geometric_budget (B : ℕ) :
    (∑ j ∈ range B, if 1 ≤ j then 1/(2:ℝ)^j else 0) ≤ 1 := by
  have exactSum (k : ℕ) : (∑ i ∈ range k, 1/(2:ℝ)^(i+1))=1-1/(2:ℝ)^k := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [sum_range_succ,ih,pow_succ]
      ring
  cases B with
  | zero => simp
  | succ k =>
    rw [sum_range_succ']
    simp only [Nat.le_add_left, Nat.reduceLeDiff, if_true, if_false, add_zero]
    rw [exactSum]
    exact sub_le_self _ (by positivity)

/-- The weight of band j is 2^(-j). The two signs each get half. The first
possible quotient level is j=1, so these weights already sum to at most one. -/
theorem geometric_of_separated {n : ℕ} {t : ℝ} (hn : 1 ≤ n) (tp : 0<t)
    (hit : t < separatedScore n) : geometricEvent n t := by
  have np : 0<(n:ℝ) := Nat.cast_pos.mpr (by omega)
  have neg := (lt_div_iff₀ (pow_pos np 2)).mp hit
  by_contra no
  have unit (j : ℕ) (hj : j ∈ range (bandCount n 0)) :
      separateMass n j ≤ (if 1 ≤ j then 1/(2:ℝ)^j else 0)*(t*(n:ℝ)^2) := by
    by_cases pos : 1 ≤ j
    · have ok : ¬(oddSum n (quotientBandRows n 0 j) < -(t*(n:ℝ)^2/(2:ℝ)^(j+1)) ∨
          t*(n:ℝ)^2/(2:ℝ)^(j+1) < cofactorSum n (quotientBandRows n 0 j)) := fun e =>
        no ⟨j,mem_range.mp hj,pos,e⟩
      push Not at ok
      let cost := t*(n:ℝ)^2/(2:ℝ)^(j+1)
      have c0 : 0 ≤ cost := by dsimp [cost]; positivity
      have odd : -oddSum n (quotientBandRows n 0 j) ≤ cost := by dsimp [cost]; linarith only [ok.1]
      have cof : cofactorSum n (quotientBandRows n 0 j) ≤ cost := ok.2
      rw [if_pos pos]
      apply (add_le_add (max_le odd c0) (max_le cof c0)).trans_eq
      dsimp [cost]
      rw [pow_succ]
      ring
    · have z : j=0 := by omega
      subst j
      simp [separateMass,zero_band,oddSum,cofactorSum,oddHalves]
  have complete := sum_le_sum unit
  rw [←sum_mul] at complete
  have total := mul_le_mul_of_nonneg_right (geometric_budget (bandCount n 0)) (show 0≤t*(n:ℝ)^2 by positivity)
  linarith only [complete,total,neg]

theorem geometric_covers {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (tp : 0<t) :
    frequency score m t ≤ eventMass geometricEvent m t := by
  classical
  apply sum_le_sum
  intro n hn
  by_cases hit : t<score n
  · have yes := geometric_of_separated (hm.trans (mem_Icc.mp hn).1) tp (hit.trans_le (score_le_separated n))
    simp only [if_pos hit,if_pos yes,le_refl]
  · simp only [if_neg hit]
    split <;> positivity

private theorem geometric_ceiling {n : ℕ} {t : ℝ} (hn : 2 ≤ n) (alarm : geometricEvent n t) :
    t ≤ 2*kernelConstant*(n:ℝ)^2 := by
  obtain ⟨j,_,_,hit⟩ := alarm
  let S := quotientBandRows n 0 j
  have sub : S ⊆ Ioc 0 (n^4/2^j) := by
    rw [show S=Ioc (bandLo n j) (bandHi n j) from quotient_rows_interval ..]
    exact Ioc_subset_Ioc (Nat.zero_le _) (min_le_right ..)
  have mass : (∑ d ∈ S, |term n d|) ≤ (n^4/2^j:ℕ)*kernelConstant := by
    have h := sum_le_sum (s:=S) fun d hd => row_uniform hn (mem_filter.mp (mem_filter.mp hd).1).1
    have card : (S.card:ℝ) ≤ (n^4/2^j:ℕ) := by exact_mod_cast (show S.card ≤ n^4/2^j by simpa using card_le_card sub)
    simpa using h.trans (by
      simpa using mul_le_mul_of_nonneg_right card kernelConstant_nonneg)
  obtain ⟨odd,cof⟩ := odd_components_abs n S
  have cost : t*(n:ℝ)^2/(2:ℝ)^(j+1) < (n^4/2^j:ℕ)*kernelConstant := by
    rcases hit with h|h
    · change oddSum n S < -_ at h
      linarith only [h,(neg_le_abs (oddSum n S)).trans (odd.trans mass)]
    · exact h.trans_le ((le_abs_self _).trans (cof.trans mass))
  have bound := (div_lt_iff₀ (by positivity : 0<(2:ℝ)^(j+1))).mp cost
  rw [pow_succ (2:ℝ) j] at bound
  have quotient : ((n^4/2^j:ℕ):ℝ)*(2:ℝ)^j ≤ (n:ℝ)^4 := by exact_mod_cast Nat.div_mul_le_self (n^4) (2^j)
  have h : t*(n:ℝ)^2 ≤ (2*kernelConstant*(n:ℝ)^2)*(n:ℝ)^2 := by
    have scaled := mul_le_mul_of_nonneg_left quotient (show 0≤2*kernelConstant by positivity [kernelConstant_nonneg])
    nlinarith only [bound,scaled]
  exact le_of_mul_le_mul_right h (pow_pos (Nat.cast_pos.mpr (by omega : 0<n)) 2)

/-- The geometrically allocated alarms satisfy an explicit all-threshold
quartic bound, including the endpoint exponent four, on every block m≥2. -/
theorem geometric_frequency_four {m : ℕ} (hm : 2 ≤ m) (t : ℝ) :
    t*eventMass geometricEvent m t ≤ 2*kernelConstant*(m:ℝ)^4 := by
  classical
  unfold eventMass
  rw [mul_sum]
  have each (n : ℕ) (hn : n ∈ Icc m (m^2)) :
      t*(if geometricEvent n t then (n:ℝ)⁻¹ else 0) ≤ 2*kernelConstant*(m:ℝ)^2 := by
    split_ifs with yes
    · have nl := hm.trans (mem_Icc.mp hn).1
      have pos : 0<(n:ℝ) := Nat.cast_pos.mpr (by omega)
      have nm : (n:ℝ) ≤ (m:ℝ)^2 := by exact_mod_cast (mem_Icc.mp hn).2
      rw [←div_eq_mul_inv]
      apply (div_le_iff₀ pos).mpr
      have scaled := mul_le_mul_of_nonneg_right nm (show 0≤2*kernelConstant*n by positivity [kernelConstant_nonneg])
      nlinarith only [geometric_ceiling nl yes,scaled]
    · rw [mul_zero]; positivity [kernelConstant_nonneg]
  have cnt : ((Icc m (m^2)).card:ℝ) ≤ (m:ℝ)^2 := by
    exact_mod_cast (show (Icc m (m^2)).card ≤ m^2 by rw [Nat.card_Icc]; omega)
  have total := sum_le_sum each
  simp only [sum_const,nsmul_eq_mul] at total
  apply total.trans
  nlinarith only [mul_le_mul_of_nonneg_right cnt (show 0≤2*kernelConstant*(m:ℝ)^2 by positivity [kernelConstant_nonneg])]

end RiemannReduction.ShortTail.LossFrequency
