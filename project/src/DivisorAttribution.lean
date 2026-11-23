import DyadicLoss

/-! Threshold-dependent localization in the original, unchanged divisors. -/

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Filter Real RiemannGaussian.AlpogeMined
open scoped ArithmeticFunction.Moebius

def smallPart (n b : ℕ) := (late n).filter (· ≤ b)
def highPart (n b : ℕ) := (late n).filter (fun d => ¬d ≤ b)
def highSum (n b : ℕ) := ∑ d ∈ highPart n b, term n d
def envelope (n : ℕ) : ℝ := kernelConstant*(1+log ((n^4:ℕ):ℝ))/((n^4:ℕ):ℝ)

theorem row_envelope {n d : ℕ} (hn : 2 ≤ n) (hd : d ∈ Ioc 0 (n^4/2)) :
    |term n d| ≤ envelope n*d := by
  have h := mem_Ioc.mp hd
  have dp : 0 < (d:ℝ) := Nat.cast_pos.mpr (by omega)
  have np : 0 < ((n^4:ℕ):ℝ) := Nat.cast_pos.mpr (pow_pos (by omega) _)
  let y := ((n^4:ℕ):ℝ)/d
  have yp : 0 < y := div_pos np dp
  have y2 : 2 ≤ y := (le_div_iff₀ dp).mpr (by exact_mod_cast (show 2*d ≤ n^4 by omega))
  have ly := log_nonneg (show 1 ≤ y by linarith)
  have d1 : (1:ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have lN := log_le_log yp (div_le_self np.le d1)
  have u : |(μ d:ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d)
  change |(μ d:ℝ)*(fixedBandCenteredKernel y-fixedBandFirstCorrection y)| ≤ _
  rw [abs_mul]
  apply (mul_le_of_le_one_left (abs_nonneg _) u).trans
  apply (abs_sub _ _).trans
  apply (add_le_add (fixedBandCenteredKernel_bound y2) (fixedBandFirstCorrection_decay yp)).trans
  calc
    _ ≤ kernelConstant*(1+log ((n^4:ℕ):ℝ))/y := by
      rw [←add_div]
      apply div_le_div_of_nonneg_right _ yp.le
      have inc := mul_le_mul_of_nonneg_left (add_le_add_left lN 1)
        (show 0 ≤ 72+60*|fixedBandLogConstant| by positivity)
      unfold kernelConstant
      nlinarith only [inc,ly,lN]
    _ = _ := by dsimp [envelope,y]; field_simp

theorem cut_absolute {n b : ℕ} (hn : 2 ≤ n) (S : Finset ℕ)
    (half : S ⊆ Ioc 0 (n^4/2)) (sub : S ⊆ Ioc 0 b) :
    ∑ d ∈ S, |term n d| ≤ envelope n*(b:ℝ)^2 := by
  have env : 0 ≤ envelope n := by
    unfold envelope
    exact div_nonneg (mul_nonneg kernelConstant_nonneg (by linarith [log_natCast_nonneg (n^4)])) (by positivity)
  have count : (S.card:ℝ) ≤ b := by
    exact_mod_cast (show S.card ≤ b by simpa using card_le_card sub)
  calc
    _ ≤ ∑ _d ∈ S, envelope n*b := by
      apply sum_le_sum
      intro d hd
      exact (row_envelope hn (half hd)).trans
        (mul_le_mul_of_nonneg_left (by exact_mod_cast (mem_Ioc.mp (sub hd)).2) env)
    _ = (S.card:ℝ)*(envelope n*b) := by simp
    _ ≤ (b:ℝ)*(envelope n*b) := mul_le_mul_of_nonneg_right count (by positivity)
    _ = _ := by ring

theorem prefix_absolute {n : ℕ} (hn : 2 ≤ n) (b : ℕ) :
    ∑ d ∈ smallPart n b, |term n d| ≤ envelope n*(b:ℝ)^2 := by
  apply cut_absolute hn
  · intro d hd
    obtain ⟨hd,_⟩ := mem_filter.mp hd
    have h := mem_Ioc.mp (mem_filter.mp hd).1
    exact mem_Ioc.mpr ⟨by omega,h.2⟩
  · intro d hd
    obtain ⟨hd,hb⟩ := mem_filter.mp hd
    have h := mem_Ioc.mp (mem_filter.mp hd).1
    exact mem_Ioc.mpr ⟨by omega,hb⟩

theorem high_negative {n b : ℕ} {t : ℝ} (hn : 2 ≤ n) (tp : 0 < t) (hit : t < score n)
    (small : envelope n*(b:ℝ)^2 ≤ t*(n:ℝ)^2/2) :
    highSum n b < -(t*(n:ℝ)^2/2) := by
  have np : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have bad := (lt_div_iff₀ (pow_pos np 2)).mp hit
  change t*(n:ℝ)^2 < max (-core n) 0 at bad
  have neg : t*(n:ℝ)^2 < -core n :=
    (lt_max_iff.mp bad).resolve_right (not_lt.mpr (by positivity))
  have split : (∑ d ∈ smallPart n b, term n d)+highSum n b = core n :=
    sum_filter_add_sum_filter_not (late n) (· ≤ b) (term n)
  have abs := (abs_sum_le_sum_abs (fun d => term n d) (smallPart n b)).trans ((prefix_absolute hn b).trans small)
  linarith only [(abs_le.mp abs).1,split,neg]

def quotientLevel (n d : ℕ) := Nat.log 2 (n^4/d)
def bandSum (n b j : ℕ) := ∑ d ∈ (highPart n b).filter (fun d => quotientLevel n d = j), term n d
def bandCount (n b : ℕ) := Nat.log 2 (n^4/(b+1))+1

theorem band_split (n b : ℕ) : ∑ j ∈ range (bandCount n b), bandSum n b j = highSum n b := by
  unfold bandSum highSum
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  have hdb : b < d := Nat.lt_of_not_ge (mem_filter.mp hd).2
  have cap : quotientLevel n d < bandCount n b := by
    have div : n^4/d ≤ n^4/(b+1) := Nat.div_le_div_left (by omega) (by omega)
    exact Nat.lt_succ_of_le (Nat.log_mono_right div)
  simp [eq_comm,cap]

/-- At least one actual dyadic quotient band above b must contribute with
negative sign. The pigeonhole bound counts only the possible quotient levels. -/
theorem band_driving_hit {n b : ℕ} {t : ℝ} (hn : 2 ≤ n) (tp : 0 < t) (hit : t < score n)
    (small : envelope n*(b:ℝ)^2 ≤ t*(n:ℝ)^2/2) :
    ∃ j < bandCount n b, bandSum n b j < -(t*(n:ℝ)^2)/(2*(bandCount n b:ℝ)) := by
  have h := high_negative hn tp hit small
  have cp : 0 < (bandCount n b:ℝ) := by unfold bandCount; positivity
  by_contra! every
  have s := sum_le_sum (s:=range (bandCount n b)) fun j hj => every j (mem_range.mp hj)
  rw [band_split,sum_const,card_range,nsmul_eq_mul] at s
  have e : (bandCount n b:ℝ) * (-(t*(n:ℝ)^2)/(2*(bandCount n b:ℝ))) = -(t*(n:ℝ)^2/2) := by field_simp
  linarith only [e,h,s]

end RiemannReduction.ShortTail.LossFrequency
