import Mathlib

/-! Remove the second quotient band from a finite linear Möbius sum by a correction
whose complete Möbius sum vanishes. The inputs are the exact lattice identities and
second-band formula proved by Sanftenberg. -/
noncomputable section
namespace RiemannReduction.ThirdQuotient
open Real Finset MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius

def density (G : ℝ → ℝ) (z t : ℝ) : ℝ := (4+3/t)*G (z/t)
def coefficient : ℝ := 2*(1-eulerMascheroniConstant)+4*Real.log 2
def correction (G : ℝ → ℝ) (y : ℝ) : ℝ :=
  coefficient*G (y/2) - ∫ t in (1:ℝ)..2, density G (y/2) t
def secondValue (z : ℝ) : ℝ := (z-1)*(coefficient+1)+(3-4*z)*log z
def RampOn (G : ℝ → ℝ) : Prop := ∀ {y:ℝ}, 0≤y → y≤2 → G y = max (y-1) 0
def ContinuousRanges (G : ℝ → ℝ) : Prop := ∀ Y : ℝ, ContinuousOn G (Set.Icc 0 Y)
def CompleteZero (G : ℝ → ℝ) : Prop := ∀ {x:ℝ} {N:ℕ}, 8≤x → x≤N → (∑ d ∈ Ioc 0 N, (μ d:ℝ)*G (x/d))=0

private theorem density_continuous {G : ℝ → ℝ} (contG : ContinuousRanges G) {y : ℝ} (hy : 0 ≤ y) :
    ContinuousOn (density G y) (Set.Icc 1 2) := by
  have arg : ContinuousOn (fun t : ℝ => y/t) (Set.Icc 1 2) :=
    continuousOn_const.div continuousOn_id (fun t ht => by have := ht.1; dsimp; linarith)
  have maps : Set.MapsTo (fun t : ℝ => y/t) (Set.Icc 1 2) (Set.Icc 0 y) :=
    fun t ht => ⟨div_nonneg hy (by linarith [ht.1]),div_le_self hy ht.1⟩
  have factor : ContinuousOn (fun t : ℝ => 4+3/t) (Set.Icc 1 2) :=
    continuousOn_const.add (continuousOn_const.div continuousOn_id (fun t ht => by have := ht.1; dsimp; linarith))
  exact factor.mul ((contG y).comp arg maps)

private def primitive (y t : ℝ) := (4*y-3)*log t-3*y/t-4*t
private theorem primitive_deriv (y : ℝ) {t : ℝ} (ht : 0<t) :
    HasDerivAt (primitive y) ((4+3/t)*(y/t-1)) t := by
  have scalar : (4+3/t)*(y/t-1) =
      (4*y-3)*t⁻¹-(0*t-3*y*1)/t^2-4*1 := by
    field_simp
    ring
  rw [scalar]
  exact (((Real.hasDerivAt_log ht.ne').const_mul (4*y-3)).sub
    ((hasDerivAt_const t (3*y)).div (hasDerivAt_id' t) ht.ne')).sub
    ((hasDerivAt_id' t).const_mul 4)

theorem second_band {G : ℝ → ℝ} (ramp : RampOn G) (contG : ContinuousRanges G) {y : ℝ} (h1 : 1≤y) (h2 : y≤2) :
    correction G (2*y) = secondValue y := by
  let f := density G y
  have hy := zero_lt_one.trans_le h1
  have cont := density_continuous contG hy.le
  have hi {a b : ℝ} (ha : 1 ≤ a) (hb : b ≤ 2) (hab : a ≤ b) :
      IntervalIntegrable f volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact cont.mono (Set.Icc_subset_Icc ha hb)
  have hi₁ := hi le_rfl h2 h1
  have hi₂ := hi h1 le_rfl h2
  have hz : (∫ t in y..2, f t) = 0 := by
    rw [← intervalIntegral.integral_zero (a := y) (b := 2) (E := ℝ)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le h2] at ht
    have ht₀ := hy.trans_le ht.1
    have hy₁ := (div_le_one ht₀).mpr ht.1
    dsimp only [f,density]
    rw [ramp (by positivity) (by linarith),max_eq_right (by linarith : y/t-1 ≤ 0),mul_zero]
  have hv : (∫ t in (1:ℝ)..y, f t) = primitive y y-primitive y 1 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := primitive y) _ hi₁
    intro t ht
    rw [Set.uIcc_of_le h1] at ht
    have ht₀ := zero_lt_one.trans_le ht.1
    have hlo := (one_le_div ht₀).mpr ht.2
    have hhi := (div_le_self hy.le ht.1).trans h2
    change HasDerivAt (primitive y) ((4+3/t)*G (y/t)) t
    rw [ramp (by positivity) hhi,max_eq_left (by linarith)]
    exact primitive_deriv y ht₀
  rw [correction,show 2*y/2=y by ring,ramp hy.le h2,max_eq_left (by linarith)]
  change _ - (∫ t in (1:ℝ)..2, f t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂,hz,hv]
  simp only [primitive,secondValue,log_one,mul_zero,div_one]
  field_simp
  ring

theorem below_second {G : ℝ → ℝ} (ramp : RampOn G) {y : ℝ} (hy : 0≤y) (endpt : y≤2) :
    correction G y = 0 := by
  have hz : (∫ t in (1:ℝ)..2, density G (y/2) t)=0 := by
    rw [← intervalIntegral.integral_zero (a:=(1:ℝ)) (b:=2) (E:=ℝ)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have tpos : 0 < t := zero_lt_one.trans_le ht.1
    have h : y/2/t ≤ 1 := (div_le_one tpos).mpr (by linarith [ht.1])
    rw [density,ramp (by positivity) (by linarith), max_eq_right (by linarith),mul_zero]
  rw [correction,hz,ramp (by positivity) (by linarith),max_eq_right (by linarith),mul_zero,sub_zero]

theorem decay_bound {G : ℝ → ℝ} (decay : ∀ {y:ℝ}, 0<y → |G y|≤300/y) {y:ℝ} (hy:0<y) :
    |correction G y| ≤ 12000/y := by
  have cBound : |coefficient| ≤ 6 := by
    unfold coefficient
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    have hlog0 := Real.log_nonneg (by norm_num : (1:ℝ)≤2)
    exact abs_le.mpr ⟨by linarith [eulerMascheroniConstant_lt_two_thirds],by linarith [one_half_lt_eulerMascheroniConstant]⟩
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a:=(1:ℝ)) (b:=2)
    (f:=density G (y/2)) (C:=8400/y) (by
      intro t ht
      rw [Set.uIoc_of_le (by norm_num)] at ht
      have ht0 : 0<t := zero_lt_one.trans ht.1
      have w : 4+3/t ≤ 7 := by have : 3/t ≤ 3 := (div_le_iff₀ ht0).mpr (by linarith [ht.1]); linarith
      rw [Real.norm_eq_abs,density,abs_mul,abs_of_nonneg (by positivity : 0≤4+3/t)]
      calc _ ≤ 7*(300/(y/2/t)) := mul_le_mul w (decay (by positivity)) (abs_nonneg _) (by norm_num)
           _ = (4200/y)*t := by field_simp; ring
           _ ≤ (4200/y)*2 := mul_le_mul_of_nonneg_left ht.2 (by positivity)
           _ = 8400/y := by ring)
  rw [Real.norm_eq_abs] at hi
  norm_num at hi
  rw [correction]
  apply (abs_sub _ _).trans
  rw [abs_mul]
  exact (add_le_add (mul_le_mul cBound (decay (half_pos hy)) (abs_nonneg _) (by norm_num)) hi).trans_eq (by ring)

theorem full_zero {G : ℝ → ℝ} (complete : CompleteZero G) (contG : ContinuousRanges G) {N : ℕ} (hN : 32≤N) :
    (∑ d ∈ Ioc 0 N, (μ d:ℝ)*correction G ((N:ℝ)/d))=0 := by
  have big : (32:ℝ)≤N := by exact_mod_cast hN
  let S := Ioc 0 N
  let f (d : ℕ) (t : ℝ) := (μ d:ℝ)*density G (((N:ℝ)/d)/2) t
  have hi (d : ℕ) (_ : d ∈ S) : IntervalIntegrable (f d) volume 1 2 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    exact continuousOn_const.mul (density_continuous contG (by positivity))
  have hz (t : ℝ) (ht : t ∈ Set.uIcc 1 2) : (∑ d ∈ S, f d t)=0 := by
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have ht0 : 0<t := zero_lt_one.trans_le ht.1
    have low : 8 ≤ (N:ℝ)/2/t := (le_div_iff₀ ht0).mpr (by linarith [ht.2])
    have high : (N:ℝ)/2/t≤N := (div_le_self (by positivity) ht.1).trans (by linarith)
    calc _ = (4+3/t) * ∑ d ∈ S, (μ d:ℝ)*G (((N:ℝ)/2/t)/d) := by
           rw [mul_sum]; apply sum_congr rfl; intro d _
           dsimp only [f,density]; rw [div_right_comm (N:ℝ) (d:ℝ) 2, div_right_comm ((N:ℝ)/2) (d:ℝ) t]; ring
         _ = 0 := by rw [show (∑ d ∈ S, (μ d:ℝ)*G (((N:ℝ)/2/t)/d))=0 from complete low high,mul_zero]
  calc _ = coefficient*(∑ d ∈ S, (μ d:ℝ)*G (((N:ℝ)/2)/d)) - ∑ d ∈ S, ∫ t in (1:ℝ)..2, f d t := by
         rw [mul_sum, ←sum_sub_distrib]; apply sum_congr rfl; intro d _
         dsimp only [f,correction]
         rw [intervalIntegral.integral_const_mul,div_right_comm (N:ℝ) (d:ℝ) 2]; ring
       _ = 0 := by
         rw [show (∑ d ∈ S, (μ d:ℝ)*G (((N:ℝ)/2)/d))=0 from complete (by linarith) (by linarith),
           ← intervalIntegral.integral_finsetSum hi,intervalIntegral.integral_congr hz,intervalIntegral.integral_zero,mul_zero,sub_zero]

def tail (F : ℝ→ℝ) (N K : ℕ) := ∑ d ∈ Ioc K N, (μ d:ℝ)*F ((N:ℝ)/d)
def cutThird (G F : ℝ→ℝ) (N K : ℕ) := ∑ d ∈ Ioc K (N/3), (μ d:ℝ)*(F ((N:ℝ)/d)-correction G ((N:ℝ)/d))

theorem third_tail_error {G F : ℝ→ℝ} (ramp : RampOn G) (contG : ContinuousRanges G) (complete : CompleteZero G)
    (decay : ∀ {y:ℝ}, 0<y → |G y|≤300/y) (first : ∀ {y:ℝ}, 1≤y → y≤2 → F y=0)
    (second : ∀ {z:ℝ}, 1≤z → 2*z≤3 → F (2*z)=secondValue z)
    {N K : ℕ} (hN : 32≤N) (hK : K≤N) : |tail F N K-cutThird G F N K| ≤ 12000*(K:ℝ)^2/N := by
  let w (d : ℕ) := (μ d:ℝ)*correction G ((N:ℝ)/d)
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr (by omega)
  have hsub : cutThird G F N K = ∑ d ∈ Ioc K N, (μ d:ℝ)*(F ((N:ℝ)/d)-correction G ((N:ℝ)/d)) := by
    apply sum_subset (Ioc_subset_Ioc_right (Nat.div_le_self ..))
    intro d hd outside
    obtain ⟨lower,upper⟩ := mem_Ioc.mp hd
    have dh : N/3 < d := lt_of_not_ge fun le => outside (mem_Ioc.mpr ⟨lower,le⟩)
    have dp : 0<(d:ℝ) := Nat.cast_pos.mpr (by omega)
    have left := (one_le_div dp).mpr (Nat.cast_le (α:=ℝ).mpr upper)
    have right : (N:ℝ)/d ≤ 3 := (div_le_iff₀ dp).mpr (by exact_mod_cast (show N ≤ 3*d by omega))
    by_cases low : (N:ℝ)/d≤2
    · rw [first left low,below_second ramp (by positivity) low, sub_self,mul_zero]
    · let z := ((N:ℝ)/d)/2
      have mid : (N:ℝ)/d = 2*z := by dsimp [z]; ring
      have z1 : 1≤z := by dsimp [z]; linarith
      have z3 : 2*z≤3 := mid ▸ right
      rw [mid,second z1 z3,second_band ramp contG z1 (by linarith),sub_self,mul_zero]
  have hsplit := sum_Ioc_consecutive w (Nat.zero_le K) hK
  change _ = ∑ d ∈ Ioc 0 N, (μ d:ℝ)*correction G ((N:ℝ)/d) at hsplit
  rw [full_zero complete contG hN] at hsplit
  have he : tail F N K-cutThird G F N K = -(∑ d ∈ Ioc 0 K, w d) := by
    rw [hsub,tail]
    simp only [mul_sub,sum_sub_distrib,sub_sub_cancel]
    dsimp only [w] at hsplit ⊢
    linarith only [hsplit]
  rw [he,abs_neg]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    (∑ d ∈ Ioc 0 K, |w d|) ≤ ∑ _d ∈ Ioc 0 K, (12000:ℝ)*K/N := by
      apply sum_le_sum
      intro d hd
      have hd₀ := Nat.cast_pos (α := ℝ).mpr (mem_Ioc.mp hd).1
      change |(μ d:ℝ)*correction G ((N:ℝ)/d)| ≤ _
      rw [abs_mul]
      apply (mul_le_of_le_one_left (abs_nonneg _) (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d))).trans
      apply (decay_bound decay (div_pos hn hd₀)).trans
      rw [div_div_eq_mul_div]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast (mem_Ioc.mp hd).2) (by norm_num)) hn.le
    _ = _ := by rw [sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul]; ring


#print axioms third_tail_error
end RiemannReduction.ThirdQuotient

