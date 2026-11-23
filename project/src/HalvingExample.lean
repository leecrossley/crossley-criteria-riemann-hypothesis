import HalvingIntervals
import OddKernelCells

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency
open Finset Real MeasureTheory RiemannGaussian.AlpogeMined RiemannReduction.ThirdBridge
open scoped ArithmeticFunction.Moebius

private def ramp4 (s : ℝ) := max (s-1) 0
private def density4 (y t : ℝ) := (1+1/t)*ramp4 (y/t)

private theorem ramp_below {s:ℝ} (hi:s≤1) : ramp4 s=0 := max_eq_right (by linarith)

private theorem difference_four {s : ℝ} (lo : 0 ≤ s) (hi : s ≤ 4) :
    fixedBandLattice s-2*fixedBandLattice (s/2) =
      ramp4 s-4*ramp4 (s/2)+ramp4 (s/3) := by
  have u4 := fixedBandUnitRamp_sum lo hi
  have u2 := fixedBandUnitRamp_sum (show 0≤ s/2 by linarith) (show s/2≤2 by linarith)
  have u1 {z : ℝ} (zp : 0≤z) (z1 : z≤1) : fixedBandUnitRamp z=0 := by
    have h := fixedBandUnitRamp_sum zp z1
    norm_num [show Ioc 0 1=({1}:Finset ℕ) by decide,max_eq_right (show z-1≤0 by linarith)] at h
    linarith only [h]
  rw [show ⌊(4:ℝ)⌋₊=4 by norm_num,show Ioc 0 4=({1,2,3,4}:Finset ℕ) by decide] at u4
  rw [show ⌊(2:ℝ)⌋₊=2 by norm_num,show Ioc 0 2=({1,2}:Finset ℕ) by decide] at u2
  norm_num only [sum_insert,sum_singleton,Nat.cast_ofNat,Nat.cast_one,div_one,
    show (1:ℕ) ∉ ({2,3,4}:Finset ℕ) by decide,show (2:ℕ) ∉ ({3,4}:Finset ℕ) by decide,
    show (3:ℕ) ∉ ({4}:Finset ℕ) by decide] at u4
  norm_num only [sum_insert,sum_singleton,Nat.cast_ofNat,Nat.cast_one,div_one,
    show (1:ℕ) ∉ ({2}:Finset ℕ) by decide] at u2
  change ramp4 s+(ramp4 (s/2)+(ramp4 (s/3)+ramp4 (s/4)))=fixedBandUnitRamp s at u4
  change ramp4 (s/2)+ramp4 (s/2/2)=fixedBandUnitRamp (s/2) at u2
  rw [show s/2/2=s/4 by ring,ramp_below (by linarith : s/4≤1),add_zero] at u2
  rw [ramp_below (by linarith : s/4≤1),add_zero] at u4
  rw [fixedBandLattice_ramps lo,fixedBandLattice_ramps (by linarith : 0≤ s/2),
      show s/2/2=s/4 by ring,show s/2/4=s/8 by ring,←u4,←u2,
      u1 (by linarith : 0≤ s/4) (by linarith),u1 (by linarith : 0≤ s/8) (by linarith)]
  ring

private theorem density_interval (y : ℝ) : IntervalIntegrable (density4 y) volume 1 2 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num : (1:ℝ)≤2)]
  have nz (t : ℝ) (ht : t∈Set.Icc (1:ℝ) 2) : t≠0 := (zero_lt_one.trans_le ht.1).ne'
  unfold density4 ramp4
  fun_prop (disch := assumption)

private theorem correction_integral_four :
    (∫ t in (1:ℝ)..2, (1+1/t)*(fixedBandLattice (4/t)-2*fixedBandLattice (4/t/2))) =
      integratedRamp 4-4*integratedRamp 2+integratedRamp (4/3) := by
  change _ = (∫ t in (1:ℝ)..2, density4 4 t)-4*(∫ t in (1:ℝ)..2, density4 2 t)+
    ∫ t in (1:ℝ)..2, density4 (4/3) t
  rw [←intervalIntegral.integral_const_mul,←intervalIntegral.integral_sub (density_interval 4)
    ((density_interval 2).const_mul 4),←intervalIntegral.integral_add ((density_interval 4).sub
    ((density_interval 2).const_mul 4)) (density_interval (4/3))]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (1:ℝ)≤2)] at ht
  have tp := zero_lt_one.trans_le ht.1
  dsimp only
  rw [difference_four (div_nonneg (by norm_num) tp.le) (div_le_self (by norm_num) ht.1)]
  simp only [density4]
  rw [show (4:ℝ)/t/2=2/t by ring,div_right_comm (4:ℝ) t 3]
  ring

/-- Exact value of Sanftenberg's corrected kernel at the quotient-four endpoint. -/
theorem surviving_four : surviving 4 =
    3-2*eulerMascheroniConstant-log 2-log 3/3 := by
  have u4 : fixedBandUnitRamp 4=13/3 := by norm_num [fixedBandUnitRamp]
  have u2 : fixedBandUnitRamp 2=1 := by norm_num [fixedBandUnitRamp]
  have u1 : fixedBandUnitRamp 1=0 := by norm_num [fixedBandUnitRamp]
  have uh : fixedBandUnitRamp (1/2)=0 := by norm_num [fixedBandUnitRamp]
  have l4 : fixedBandLattice 4=4/3 := by
    rw [fixedBandLattice_ramps (by norm_num : (0:ℝ)≤4)]
    norm_num [u4,u2,u1]
  have l2 : fixedBandLattice 2=1 := by
    rw [fixedBandLattice_ramps (by norm_num : (0:ℝ)≤2)]
    norm_num [u2,u1,uh]
  have log4 : log 4=2*log 2 := by rw [show (4:ℝ)=2^2 by norm_num,log_pow]; norm_num
  change fixedBandCenteredKernel 4-((1-eulerMascheroniConstant)*(fixedBandLattice 4-2*fixedBandLattice (4/2))-
    (∫ t in (1:ℝ)..2, (1+1/t)*(fixedBandLattice (4/t)-2*fixedBandLattice (4/t/2))))=_
  rw [fixedBandCenteredKernel,correction_integral_four,integrated_ramp_high (by norm_num : (2:ℝ)≤4),
     integrated_ramp_high (le_refl (2:ℝ)),integrated_ramp_middle (by norm_num : (1:ℝ)≤4/3) (by norm_num),
     show (4:ℝ)/2=2 by norm_num,log_div (by norm_num : (4:ℝ)≠0) (by norm_num : (3:ℝ)≠0),
     u4,u2,l4,l2,fixedBandLogConstant,log4]
  ring

theorem surviving_four_lower : (13:ℝ)/20 < surviving 4 := by
  have upper : eulerMascheroniConstant < 761/280-3*log 2 := by
    have h := eulerMascheroniConstant_lt_eulerMascheroniSeq' 8
    have exact8 : eulerMascheroniSeq' 8=761/280-log 8 := by norm_num [eulerMascheroniSeq']
    have log8 : log 8=3*log 2 := by rw [show (8:ℝ)=2^3 by norm_num,log_pow]; norm_num
    rwa [exact8,log8] at h
  rw [surviving_four]
  linarith only [upper,log_three_lt_d9,log_two_gt_d9]

private theorem example_clip : max 262143 (bandLo 32 2)=262143 := by
  have lg : log 32=5*log 2 := by rw [show (32:ℝ)=2^5 by norm_num,log_pow]; norm_num
  have z := log_two_gt_d9
  have p : 0<log (2:ℝ) := by linarith only [z]
  have root : sqrt (log 32) < 3*log 2 := by
    rw [lg]
    apply (sqrt_lt' (by positivity)).mpr
    nlinarith only [mul_pos p (show 0 < 9*log (2:ℝ)-5 by linarith only [z])]
  have ex := exp_lt_exp.mpr root
  have log8 : 3*log 2=log (8:ℝ) := by rw [show (8:ℝ)=2^3 by norm_num,log_pow]; norm_num
  rw [log8,exp_log (by norm_num)] at ex
  have input : (32:ℝ)^3*exp (sqrt (log 32)) < 262144 := by
    linarith only [mul_lt_mul_of_pos_left ex (by norm_num : (0:ℝ)<32^3)]
  have cut : cutoff 32 < 262144 := by
    unfold cutoff
    exact (Nat.floor_lt (by positivity)).mpr (by norm_num at input ⊢; exact input)
  have multi : fixedBandMultipleCutoff 32 ≤ 262143 :=
    (Nat.div_le_self ..).trans (by decide : 32^3≤262143)
  apply max_eq_left
  unfold bandLo
  omega

private theorem example_share : layerShare 32 2 1 = 256/399 := by
  have h : halvingCount 32 2=19 := by decide
  have k : bandCount 32 0=21 := by decide
  norm_num [layerShare,share,h,k]

private theorem example_layer (i : ℕ) (hi : i<19) :
    clippedBandNet 262143 32 2 i =
      (if i=17 then -surviving 4 else 0) + (if i=18 then surviving 4 else 0) := by
  have cuts : ∀ i : Fin 19, 262143/2^(i:ℕ)+1=2^(18-(i:ℕ)) ∧
      262144/2^(i:ℕ)=2^(18-(i:ℕ)) := by decide +kernel
  obtain ⟨left,right⟩ := cuts ⟨i,hi⟩
  change 262143/2^i+1=2^(18-i) at left
  change 262144/2^i=2^(18-i) at right
  have span : Ioc (262143/2^i) (262144/2^i) = ({2^(18-i)}:Finset ℕ) := by
    ext d
    simp only [mem_Ioc,mem_singleton]
    omega
  rw [clippedBandNet,example_clip,show bandHi 32 2=262144 by decide,halvedNet,intervalNet,span,sum_singleton]
  push_cast
  rw [div_div,←pow_add,show i+(18-i)=18 by omega]
  have value : (32:ℝ)^4/2^18=4 := by norm_num
  rw [value]
  by_cases pl : i=17
  · subst i
    norm_num [ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  by_cases pr : i=18
  · subst i
    norm_num
  have zero := ArithmeticFunction.moebius_apply_prime_pow (k:=18-i) Nat.prime_two (by omega)
  rw [if_neg (by omega : 18-i≠1)] at zero
  simp [zero,pl,pr]

private theorem example_group_zero (g : ℕ) :
    (∑ i ∈ halvingGroupRows 2 (halvingCount 32 2) g, clippedBandNet 262143 32 2 i)=0 := by
  change (∑ i ∈ halvingGroupRows 2 19 g, clippedBandNet 262143 32 2 i)=0
  let S := halvingGroupRows 2 19 g
  have repl := sum_congr (s₁:=S) rfl fun i hi => example_layer i (mem_range.mp (mem_filter.mp hi).1)
  rw [repl,sum_add_distrib]
  have mem17 : 17∈S ↔ (9:ℕ)=g := by
    change 17∈(range 19).filter (fun r => halvingGroupIndex 2 r=g) ↔ 9=g
    rw [mem_filter]
    norm_num [halvingGroupIndex]
  have mem18 : 18∈S ↔ (9:ℕ)=g := by
    change 18∈(range 19).filter (fun r => halvingGroupIndex 2 r=g) ↔ 9=g
    rw [mem_filter]
    norm_num [halvingGroupIndex]
  by_cases showBoth : (9:ℕ)=g <;> simp [mem17,mem18,showBoth]

/-- A false individual alarm in an actual retained quotient band, at the
first positive dyadic threshold. The two opposite depths cancel in their
consecutive pair, and every other group of that band also has zero net. -/
theorem retained_dyadic_reversal :
    layerShare 32 2 1=256/399 ∧
    clippedBandNet 262143 32 2 17 < -layerShare 32 2 1 ∧
    layerShare 32 2 1 < clippedBandNet 262143 32 2 18 ∧
    (∀ g : ℕ, ¬adverseHalvingGroup 2 262143 32 2 g 1) ∧
    ¬signEvent 32 1 (laterRows 32 2 262143) := by
  have q := example_share
  have v := surviving_four_lower
  have left := example_layer 17 (by decide)
  have right := example_layer 18 (by decide)
  norm_num at left right
  have noGroup (g : ℕ) : ¬ adverseHalvingGroup 2 262143 32 2 g 1 := by
    have charge : 0 ≤ (#(halvingGroupRows 2 (halvingCount 32 2) g):ℝ)*layerShare 32 2 1 := by rw [q]; positivity
    unfold adverseHalvingGroup
    dsimp only
    rw [example_group_zero g]
    rintro (neg | ⟨_,pos⟩)
    · linarith only [charge,neg]
    · linarith only [charge,pos]
  refine ⟨q,by linarith only [left,q,v],by linarith only [right,q,v],noGroup,?_⟩
  intro alarm
  obtain ⟨g,_,bad⟩ := adverse_group_of_clipped_alarm 2 (by norm_num : (0:ℝ)≤1) alarm
  exact noGroup g bad

theorem retained_selected_layer :
    selectedLayerEvent (fun _ => 262143) (fun _ j _ => j=2) 32 1 := by
  exact ⟨2,by decide,17,by decide,rfl,Or.inl retained_dyadic_reversal.2.1⟩

end RiemannReduction.ShortTail.LossFrequency
