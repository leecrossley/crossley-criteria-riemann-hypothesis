import OddAbelBands
import FiniteAnnulus

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Real RiemannGaussian.AlpogeMined RiemannReduction.DivisorBand RiemannReduction.DyadicBands
open scoped ArithmeticFunction.Moebius

private def scaleWeight (N d : ℕ) : ℝ :=
  fixedBandCenteredKernel ((N:ℝ)/d) - fixedBandFirstCorrection ((N:ℝ)/d)

/-- The complete odd part, including the discarded prefix. -/
def completeOdd (N : ℕ) : ℝ :=
  ∑ d ∈ (Ioc 0 (N/2)).filter (fun r => r%2=1), (μ d:ℝ)*scaleWeight N d

private theorem complete_sum {N : ℕ} (large : 16 ≤ N) :
    D (N:ℝ) = ∑ d ∈ Ioc 0 (N/2), (μ d:ℝ)*scaleWeight N d := by
  rw [deficit_contrast (Nat.cast_pos.mpr (by omega : 0<N)),fixedBand_centered_identity (by omega)]
  have eq := fixedBandHalfTail_error (K:=0) large (Nat.zero_le _)
  simp only [Nat.cast_zero,zero_pow (by decide : 2≠0),mul_zero,zero_div,abs_nonpos_iff,sub_eq_zero] at eq
  exact eq

/-- The sign on each even divisor is minus the sign on its odd half. Its
kernel is the kernel at half the scale, including both floor endpoints. -/
theorem complete_odd_double {N : ℕ} (large : 8 ≤ N) :
    completeOdd (2*N)-completeOdd N = D ((2*N:ℕ):ℝ) := by
  rw [complete_sum (by omega : 16 ≤ 2*N)]
  have folded := fold_signed_rows (Ioc 0 ((2*N)/2)) (scaleWeight (2*N))
  have cuts : oddHalves (Ioc 0 ((2*N)/2)) = (Ioc 0 (N/2)).filter (fun r => r%2=1) := by
    rw [cofactor_interval]
    congr 3
    omega
  have same (r : ℕ) : scaleWeight (2*N) (2*r) = scaleWeight N r := by
    unfold scaleWeight
    push_cast
    rw [mul_div_mul_left _ _ (by norm_num : (2:ℝ)≠0)]
  simp only [cuts,same] at folded
  exact folded.symm

/-- A telescope at every integer power of two. -/
theorem complete_odd_dyadic {N : ℕ} (large : 8 ≤ N) (j : ℕ) :
    completeOdd (2^j*N)-completeOdd N =
      ∑ i ∈ range j, D ((2^(i+1)*N:ℕ):ℝ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have big : 8 ≤ 2^j*N := large.trans (Nat.le_mul_of_pos_left _ (by positivity))
    have more := complete_odd_double big
    have shift : 2*(2^j*N) = 2^(j+1)*N := by rw [pow_succ]; ring
    rw [shift] at more
    rw [sum_range_succ]
    linarith only [more,ih]

/-- Doubling the fourth-power sample uses the four intermediate prime deficits. -/
theorem complete_odd_fourth_dilation {n : ℕ} (large : 2 ≤ n) :
    completeOdd ((2*n)^4)-completeOdd (n^4) =
      D (2*(n:ℝ)^4) + D (4*(n:ℝ)^4) + D (8*(n:ℝ)^4) + D (16*(n:ℝ)^4) := by
  have hn : 8 ≤ n^4 := (by decide : 8 ≤ 2^4).trans (Nat.pow_le_pow_left large 4)
  have eq := complete_odd_dyadic hn 4
  rw [mul_pow]
  simp only [sum_range_succ,sum_empty,range_zero,zero_add,Nat.cast_mul,Nat.cast_pow,
      Nat.cast_ofNat,Nat.reduceAdd,Nat.reducePow] at eq
  norm_num at eq ⊢
  exact eq

/-- On the published finite-height domain the four prime-deficit bounds
control the signed displacement of the complete odd sum under n ↦ 2n. -/
theorem complete_odd_finite_difference
    (published : ∀ x : ℝ, 1024 ≤ x → x ≤ (FiniteFifth.cap:ℝ)^2 → |D x| < sqrt x/5)
    {n : ℕ} (lo : 5 ≤ n) (hi : n ≤ 13*10^9) :
    |completeOdd ((2*n)^4)-completeOdd (n^4)| < ((6+3*sqrt 2)/5)*(n:ℝ)^2 := by
  have each (a : ℕ) (left : 2 ≤ a) (right : a ≤ 16) :
      |D ((a:ℝ)*(n:ℝ)^4)| < sqrt a*(n:ℝ)^2/5 := by
    have lower : 1024 ≤ a*n^4 :=
      (by decide : 1024 ≤ 2*5^4).trans (Nat.mul_le_mul left (Nat.pow_le_pow_left lo 4))
    have upper : a*n^4 ≤ FiniteFifth.cap^2 :=
      (Nat.mul_le_mul right (Nat.pow_le_pow_left hi 4)).trans (by decide)
    have h := published ((a:ℝ)*(n:ℝ)^4) (by exact_mod_cast lower) (by exact_mod_cast upper)
    have root : sqrt ((n:ℝ)^4)=(n:ℝ)^2 := by rw [show (n:ℝ)^4=((n:ℝ)^2)^2 by ring,sqrt_sq (sq_nonneg _)]
    rwa [sqrt_mul (Nat.cast_nonneg _) _,root] at h
  have h2 := each 2 (by decide) (by decide)
  have h4 := each 4 (by decide) (by decide)
  have h8 := each 8 (by decide) (by decide)
  have h16 := each 16 (by decide) (by decide)
  norm_num at h2 h4 h8 h16
  have eight : sqrt 8 = 2*sqrt 2 := by rw [show (8:ℝ)=4*2 by norm_num,sqrt_mul (by norm_num)]; norm_num
  rw [eight] at h8
  rw [complete_odd_fourth_dilation (by omega)]
  apply (abs_add_le ..).trans_lt
  have left := abs_add_le (D (2*(n:ℝ)^4)) (D (4*(n:ℝ)^4))
  have middle := abs_add_le (D (2*(n:ℝ)^4) + D (4*(n:ℝ)^4)) (D (8*(n:ℝ)^4))
  linarith only [left,middle,h2,h4,h8,h16]

/-! At real heights, the triangular lattice is the integer dilation of the prime
window. Dirichlet convolution gives its logarithmic Möbius transform. The first
dyadic correction has zero transform at every real height at least sixteen. -/

open RiemannReduction.BandLog MeasureTheory intervalIntegral
open scoped ArithmeticFunction.zeta ArithmeticFunction.vonMangoldt

private theorem range_eq (b:ℕ) : Icc 1 b = Ioc 0 b := by ext d; simp only [mem_Icc,mem_Ioc]; omega

private theorem first_eq (y:ℝ) : DyadicBands.correction 1 y = fixedBandFirstCorrection y := by
  have zero : flatSum oddMangoldt G 2 y = 0 := by
    apply sum_eq_zero
    intro d hd
    have choices : d=1 ∨ d=2 := by have := mem_Ioc.mp hd; omega
    rcases choices with rfl|rfl <;> simp [oddMangoldt,oddPart]
  change _ = (1-eulerMascheroniConstant)*G y - ∫ t in (1:ℝ)..2, density G y t
  simp [DyadicBands.correction,lat,logOperator,zero]

private theorem beyond {y:ℝ} (hy:0<y) (hi:y≤2) : F y - fixedBandFirstCorrection y = 0 := by
  have h := (agrees 1 hy (by simpa using hi)).2
  rw [← first_eq,h,sub_self]

private theorem unit_dilate {y:ℝ} (hy:0≤y) :
    dilate (ζ:ArithmeticFunction ℝ) ramp y = fixedBandUnitRamp y := by
  rw [← fixedBandUnitRamp_sum hy (le_refl y)]
  unfold dilate
  rw [range_eq]
  apply sum_congr rfl
  intro d hd
  simp [ramp,(mem_Ioc.mp hd).1.ne']

private theorem unit_small {y:ℝ} (hy:y≤1) : fixedBandUnitRamp y=0 := by
  rcases lt_or_eq_of_le hy with lt|rfl
  · simp [fixedBandUnitRamp,Nat.floor_eq_zero.mpr lt]
  · norm_num [fixedBandUnitRamp,harmonic_succ]

private theorem lattice_small {y:ℝ} (hy:y≤1) : L y=0 := by
  rcases lt_or_eq_of_le hy with lt|rfl
  · simp [L,fixedBandLattice,Nat.floor_eq_zero.mpr lt]
  · rw [L_is_delta (by norm_num),delta,W_small (by norm_num),W_small (by norm_num)]
    norm_num

private theorem unit_moebius {B:ℕ} {x:ℝ} (h1:1≤x) (cap:x≤B) :
    BandLog.trans B fixedBandUnitRamp x=x-1 := by
  have zero : ∀ {z:ℝ}, z≤1 → fixedBandUnitRamp z=0 := fun h => unit_small h
  have cap0 : 0≤x := by linarith
  have transform := dilate_flat (μ:ArithmeticFunction ℝ) fixedBandUnitRamp zero cap0 cap
  change dilate (μ:ArithmeticFunction ℝ) fixedBandUnitRamp x = BandLog.trans B fixedBandUnitRamp x at transform
  rw [←transform]
  calc dilate (μ:ArithmeticFunction ℝ) fixedBandUnitRamp x =
      dilate (μ:ArithmeticFunction ℝ) (dilate (ζ:ArithmeticFunction ℝ) ramp) x := by
        unfold dilate
        apply sum_congr rfl
        intro d hd
        exact congrArg _ (unit_dilate (show 0≤x/d by positivity)).symm
    _ = x-1 := by
      rw [←dilate_mul,ArithmeticFunction.coe_moebius_mul_coe_zeta,dilate_one ramp h1,ramp,max_eq_left (by linarith)]

private theorem window_lattice (y:ℝ) :
    dilate (ζ:ArithmeticFunction ℝ) DivisorBand.window y = L y := by
  unfold dilate L fixedBandLattice
  rw [range_eq]
  apply sum_congr rfl
  intro k hk
  rw [DivisorBand.window,div_right_comm y (k:ℝ) 4,FourthMass.tent_at_prime]
  simp [(mem_Ioc.mp hk).1.ne']
  rfl

private def muLog : ArithmeticFunction ℝ := ⟨fixedBandMobiusCoeff,by simp [fixedBandMobiusCoeff]⟩
private theorem muLog_zeta : muLog*ζ = -(ArithmeticFunction.vonMangoldt:ArithmeticFunction ℝ) := by
  ext n
  rw [mul_comm,ArithmeticFunction.coe_zeta_mul_apply]
  exact ArithmeticFunction.sum_moebius_mul_log_eq

private theorem real_mobius {B:ℕ} {x:ℝ} (hx:0≤x) (cap:x≤B) :
    D x=fixedBandMain x+∑ d ∈ Ioc 0 B,fixedBandMobiusCoeff d*L (x/d) := by
  have flat := dilate_flat muLog L (fun h => lattice_small h) hx cap
  change dilate muLog L x = ∑ d ∈ Ioc 0 B,fixedBandMobiusCoeff d*L (x/d) at flat
  rw [←flat,show L=dilate (ζ:ArithmeticFunction ℝ) DivisorBand.window from funext (fun y => (window_lattice y).symm),←dilate_mul,muLog_zeta,D,←band_dilate,fixedBandMain,c]
  simp only [dilate,ArithmeticFunction.neg_apply,neg_mul,sum_neg_distrib]
  ring


private theorem real_centered {B:ℕ} {x:ℝ} (hx:4≤x) (cap:x≤B) : D x = BandLog.trans B F x := by
  let S := Ioc 0 B
  let mu (d:ℕ) : ℝ := μ d
  have pos : 0<x := by linarith
  have hp := unit_moebius (show 1≤x by linarith) cap
  have hh := unit_moebius (show 1≤x/2 by linarith) (show x/2≤B by linarith)
  have hz := fixedBandLattice_moebius_zero hx cap
  change (∑ d ∈ S, mu d*L (x/d)) = 0 at hz
  have term (d:ℕ) (hd:d ∈ S) : mu d*F (x/d) =
      log 2*(mu d*fixedBandUnitRamp (x/d) - mu d*fixedBandUnitRamp ((x/2)/d)) +
      fixedBandMobiusCoeff d*L (x/d) - (log x+fixedBandLogConstant)*(mu d*L (x/d)) := by
    rw [F,fixedBandCenteredKernel,log_div pos.ne' (Nat.cast_pos.mpr (mem_Ioc.mp hd).1).ne',div_right_comm x (d:ℝ) 2]
    dsimp only [mu,L,fixedBandMobiusCoeff]
    ring
  rw [real_mobius pos.le cap]
  change _ = ∑ d ∈ S,mu d*F (x/d)
  rw [sum_congr rfl term,sum_sub_distrib,sum_add_distrib,←mul_sum,←mul_sum,hz,mul_zero,sub_zero,sum_sub_distrib]
  dsimp only [mu,S]
  change fixedBandMain x+_ = log 2*(BandLog.trans B fixedBandUnitRamp x-BandLog.trans B fixedBandUnitRamp (x/2))+_
  rw [hp,hh,fixedBandMain]
  ring

private def realWeight (x:ℝ) (d:ℕ) := F (x/d)-fixedBandFirstCorrection (x/d)

private theorem real_corrected {x:ℝ} (hx:16≤x) :
    D x = ∑ d ∈ Ioc 0 ⌊x/2⌋₊, (μ d:ℝ)*realWeight x d := by
  let B := ⌊x⌋₊+1
  have cap : x≤(B:ℝ) := by dsimp [B]; push_cast; exact (Nat.lt_floor_add_one x).le
  have hz := (DyadicBands.null 1 (x:=x) (by norm_num; linarith) cap).2
  rw [show DyadicBands.correction 1 = fixedBandFirstCorrection from funext first_eq] at hz
  have full : D x = ∑ d ∈ Ioc 0 B, (μ d:ℝ)*realWeight x d := by
    simp only [realWeight,mul_sub,sum_sub_distrib]
    change D x=BandLog.trans B F x-BandLog.trans B fixedBandFirstCorrection x
    rw [hz,sub_zero,real_centered (by linarith) cap]
  rw [full]
  symm
  apply sum_subset (Ioc_subset_Ioc_right ((Nat.floor_mono (show x/2≤x by linarith)).trans (Nat.le_succ _)))
  intro d hd outside
  have dp := (mem_Ioc.mp hd).1
  have dr := Nat.cast_pos (α:=ℝ).mpr dp
  have cutoff : ⌊x/2⌋₊ < d := lt_of_not_ge (fun H => outside (mem_Ioc.mpr ⟨dp,H⟩))
  have beyondCut : x/2 < d := (Nat.floor_lt (show 0≤x/2 by linarith)).mp cutoff
  rw [realWeight,beyond (div_pos (by linarith) dr) ((div_le_iff₀ dr).mpr (by linarith)),mul_zero]

/-- All odd Möbius divisors of the corrected kernel at a real height. -/
def completeOddReal (x:ℝ) : ℝ :=
  ∑ d ∈ (Ioc 0 ⌊x/2⌋₊).filter (fun r => r%2=1), (μ d:ℝ)*realWeight x d

theorem complete_odd_real_nat (N:ℕ) : completeOddReal N=completeOdd N := by
  unfold completeOddReal completeOdd
  rw [show ⌊(N:ℝ)/2⌋₊=N/2 by simpa using Nat.floor_div_natCast (N:ℝ) 2]
  rfl

/-- The complete odd transforms at two consecutive real scales differ by
the prime-power deficit, for every real scale at least sixteen. -/
theorem complete_odd_real_halve {x:ℝ} (hx:16≤x) :
    completeOddReal x-completeOddReal (x/2)=D x := by
  rw [real_corrected hx]
  have folded := fold_signed_rows (Ioc 0 ⌊x/2⌋₊) (realWeight x)
  have cuts : oddHalves (Ioc 0 ⌊x/2⌋₊) = (Ioc 0 ⌊x/2/2⌋₊).filter (fun r => r%2=1) := by
    rw [cofactor_interval,show ⌊x/2/2⌋₊=⌊x/2⌋₊/2 by simpa using Nat.floor_div_natCast (x/2) 2]
  have same (r : ℕ) : realWeight x (2*r)=realWeight (x/2) r := by
    unfold realWeight
    simp only [Nat.cast_mul,Nat.cast_ofNat,div_div]
  simp only [cuts,same] at folded
  exact folded.symm


private theorem small_odd_real {x:ℝ} (h0:0<x) (h1:x≤1024) : |completeOddReal x|≤835584 := by
  let S := (Ioc 0 ⌊x/2⌋₊).filter (fun r => r%2=1)
  have logB : |fixedBandLogConstant| ≤ 1 := by
    unfold fixedBandLogConstant
    apply abs_le.mpr
    have v := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    have w := log_nonneg (by norm_num : (1:ℝ)≤2)
    constructor <;> linarith [one_half_lt_eulerMascheroniConstant,eulerMascheroniConstant_lt_two_thirds]
  have row (d:ℕ) (hd:d∈S) : |(μ d:ℝ)*realWeight x d|≤1632 := by
    obtain ⟨dp,cut⟩ := mem_Ioc.mp (mem_filter.mp hd).1
    have dr := Nat.cast_pos (α:=ℝ).mpr dp
    have y1 : (1:ℝ)≤x/d := (one_le_div dr).mpr ((Nat.le_floor_iff (show 0≤x/2 by linarith)).mp cut |>.trans (by linarith))
    have yp : 0<x/d := zero_lt_one.trans_le y1
    have f := fixedBandCenteredKernel_uniform y1
    have a := (fixedBandFirstCorrection_decay yp).trans (div_le_self (by norm_num : (0:ℝ)≤1500) y1)
    have m : |(μ d:ℝ)|≤1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d)
    rw [abs_mul]
    apply (mul_le_mul_of_nonneg_right m (abs_nonneg _)).trans
    rw [one_mul,realWeight]
    have bound := abs_sub (F (x/d)) (fixedBandFirstCorrection (x/d))
    change |F (x/d)| ≤ _ at f
    linarith only [bound,f,a,logB]
  have card : #S≤512 := (card_le_card (filter_subset ..)).trans (by
      rw [Nat.card_Ioc,Nat.sub_zero]
      exact Nat.floor_le_of_le (show x/2≤(512:ℝ) by linarith))
  change |∑ d ∈ S, (μ d:ℝ)*realWeight x d|≤_
  apply (abs_sum_le_sum_abs ..).trans
  apply (sum_le_sum row).trans
  rw [sum_const,nsmul_eq_mul]
  linarith only [show (#S:ℝ)≤512 by exact_mod_cast card]

/-- A square-root prime-deficit envelope through any real endpoint bounds the
complete odd Möbius sum through the same endpoint. -/
theorem complete_odd_of_prime_envelope {X a:ℝ} (coef:0≤a)
    (prime : ∀ x : ℝ, 1024 ≤ x → x ≤ X → |D x| ≤ a*sqrt x)
    {x:ℝ} (positive:0<x) (cap:x≤X) :
    |completeOddReal x|≤835584+a*((2+sqrt 2)*sqrt x) := by
  generalize hh: ⌊x⌋₊=k
  induction k using Nat.strong_induction_on generalizing x with
  | h k ih =>
    by_cases low : x≤1024
    · exact (small_odd_real positive low).trans (le_add_of_nonneg_right (by positivity))
    have large : 1024≤x := le_of_lt (lt_of_not_ge low)
    have half := half_pos positive
    have cut : ⌊x/2⌋₊<k := by
      rw [←hh]
      apply (Nat.floor_lt half.le).mpr
      have floorBound := Nat.lt_floor_add_one x
      linarith only [floorBound,large]
    have induct := ih ⌊x/2⌋₊ cut half ((show x/2≤x by linarith).trans cap) rfl
    have shift := complete_odd_real_halve (show 16≤x by linarith)
    have d := prime x large cap
    have two : (2+sqrt 2)/sqrt 2=1+sqrt 2 := by
      apply (div_eq_iff (sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne').mpr
      nlinarith only [sq_sqrt (by norm_num : (0:ℝ)≤2)]
    have scale : (2+sqrt 2)*sqrt (x/2) = (1+sqrt 2)*sqrt x := by
      rw [sqrt_div positive.le]
      calc _ = ((2+sqrt 2)/sqrt 2)*sqrt x := by ring
           _ = _ := by rw [two]
    change |completeOddReal (x/2)|≤835584+a*((2+sqrt 2)*sqrt (x/2)) at induct
    rw [scale] at induct
    rw [show completeOddReal x = D x+completeOddReal (x/2) by linarith only [shift]]
    apply (abs_add_le ..).trans
    linarith only [d,induct]

/-- The continuum prime envelope gives an absolute bound on the complete odd
sum at every height in its finite range, including nonintegral dyadic halves. -/
theorem complete_odd_real_finite
    (published : ∀ x : ℝ, 1024 ≤ x → x ≤ (FiniteFifth.cap:ℝ)^2 → |D x| < sqrt x/5)
    {x:ℝ} (positive:0<x) (cap:x≤(FiniteFifth.cap:ℝ)^2) :
    |completeOddReal x|≤835584+((2+sqrt 2)/5)*sqrt x := by
  have h := complete_odd_of_prime_envelope (X:=(FiniteFifth.cap:ℝ)^2) (a:=1/5) (by norm_num)
    (fun y hy hcap => by simpa only [one_div,inv_mul_eq_div] using (published y hy hcap).le) positive cap
  linarith only [h]

/-- The complete signed odd-divisor sum and its signed odd-cofactor companion
both have absolute value below 0.683 n² across the finite fourth-power interval. -/
theorem complete_odd_finite_magnitudes
    (published : ∀ x : ℝ, 1024 ≤ x → x ≤ (FiniteFifth.cap:ℝ)^2 → |D x| < sqrt x/5)
    {n:ℕ} (lo:100000≤n) (hi:n≤26*10^9) :
    |completeOdd (n^4)| < (683/1000)*(n:ℝ)^2 ∧
    |completeOddReal ((n:ℝ)^4/2)| < (683/1000)*(n:ℝ)^2 := by
  have np : 0<(n:ℝ) := Nat.cast_pos.mpr (by omega)
  have cap : (n:ℝ)^4≤(FiniteFifth.cap:ℝ)^2 := by exact_mod_cast (Nat.pow_le_pow_left hi 4).trans (by decide : (26*10^9)^4≤FiniteFifth.cap^2)
  have s2 : sqrt 2≤(14143:ℝ)/10000 := by
    nlinarith only [sq_sqrt (by norm_num : (0:ℝ)≤2),sq_nonneg (sqrt 2-14143/10000)]
  have coeff : (2+sqrt 2)/5≤(68286:ℝ)/100000 := by linarith only [s2]
  have scale : sqrt ((n:ℝ)^4)=(n:ℝ)^2 := by rw [show (n:ℝ)^4=((n:ℝ)^2)^2 by ring,sqrt_sq (sq_nonneg _)]
  have squared : (10^10:ℝ)≤(n:ℝ)^2 := by exact_mod_cast (Nat.pow_le_pow_left lo 2)
  have each {x:ℝ} (p:0<x) (h:x≤(n:ℝ)^4) : |completeOddReal x|<(683/1000)*(n:ℝ)^2 := by
    have result := complete_odd_real_finite published p (h.trans cap)
    have root := sqrt_le_sqrt h
    rw [scale] at root
    have control := mul_le_mul coeff root (sqrt_nonneg _) (by norm_num)
    linarith only [result,control,squared]
  constructor
  · rw [←complete_odd_real_nat,Nat.cast_pow]
    exact each (by positivity) le_rfl
  · exact each (by positivity) (div_le_self (by positivity) (by norm_num))


/-- Identify the full divisor and cofactor sums with the two real scales. -/
theorem full_odd_rows (n:ℕ) :
    oddSum n (Ioc 0 (n^4/2))=completeOdd (n^4) ∧
    cofactorSum n (Ioc 0 (n^4/2))=completeOddReal ((n:ℝ)^4/2) := by
  refine ⟨rfl,?_⟩
  have floor2 (x:ℝ) : ⌊x/2⌋₊=⌊x⌋₊/2 := by simpa using Nat.floor_div_natCast x 2
  rw [cofactorSum,cofactor_interval,completeOddReal,floor2,floor2,← Nat.cast_pow,Nat.floor_natCast]
  apply sum_congr rfl
  intro r _
  simp only [rowWeight,realWeight,F,Nat.cast_mul,Nat.cast_ofNat,div_div]

/-- Every point on each of these complete blocks satisfies the two combined
parity estimates. All divisor rows are included before the signs are summed. -/
theorem complete_odd_finite_blocks
    (published : ∀ x : ℝ, 1024 ≤ x → x ≤ (FiniteFifth.cap:ℝ)^2 → |D x| < sqrt x/5)
    {m n : ℕ} (lo : 100000 ≤ m) (hi : m ≤ 161245) (hn : n ∈ Icc m (m^2)) :
    |oddSum n (Ioc 0 (n^4/2))| < (683/1000)*(n:ℝ)^2 ∧
    |cofactorSum n (Ioc 0 (n^4/2))| < (683/1000)*(n:ℝ)^2 := by
  rw [(full_odd_rows n).1,(full_odd_rows n).2]
  exact complete_odd_finite_magnitudes published (lo.trans (mem_Icc.mp hn).1)
    ((mem_Icc.mp hn).2.trans ((Nat.pow_le_pow_left hi 2).trans (by decide)))

end RiemannReduction.ShortTail.LossFrequency
