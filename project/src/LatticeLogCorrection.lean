import OddRampDilation

noncomputable section
namespace RiemannReduction.BandLog
open Finset Real RiemannGaussian.AlpogeMined
open ArithmeticFunction (vonMangoldt_nonneg vonMangoldt_le_log)
open RiemannReduction.ThirdBridge MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius

abbrev L := fixedBandLattice
abbrev F := fixedBandCenteredKernel
abbrev G := RiemannReduction.ThirdBridge.lattice
def delta (f : ℝ→ℝ) (x : ℝ) := f x-2*f (x/2)
abbrev continuousRanges := RiemannReduction.ThirdQuotient.ContinuousRanges

theorem L_is_delta {y : ℝ} (hy : 0≤y) : L y=delta W y := by
  rw [L,fixedBandLattice_ramps hy,delta,W_is_odd_ramp hy,W_is_odd_ramp (by positivity),
      show y/2/2=y/4 by ring]
  ring

theorem G_is_delta (y : ℝ) : G y=delta L y := rfl

theorem W_cont : continuousRanges W := by
  intro Y
  let B := ⌊Y⌋₊+1
  have cap : Y ≤ (B:ℝ) := by dsimp [B]; push_cast; exact (Nat.lt_floor_add_one Y).le
  apply (continuousOn_finsetSum (Ioc 0 B) (f:=fun (k:ℕ) (y:ℝ) => oddUnits k*ramp (y/k))
    (fun _ _ => by unfold ramp; fun_prop)).congr
  intro y hy
  exact dilate_flat oddUnits ramp (fun h => ramp_zero h) hy.1 (hy.2.trans cap)

theorem L_cont : continuousRanges L := lattice_continuousOn

theorem G_cont : continuousRanges G := by
  intro Y
  have arg : ContinuousOn (fun y : ℝ => y/2) (Set.Icc 0 Y) := continuousOn_id.div_const 2
  have maps : Set.MapsTo (fun y:ℝ => y/2) (Set.Icc 0 Y) (Set.Icc 0 Y) :=
    fun y hy => ⟨by dsimp; linarith [hy.1],by dsimp; linarith [hy.1,hy.2]⟩
  exact (L_cont Y).sub (continuousOn_const.mul ((L_cont Y).comp arg maps))

theorem op_congr {f g : ℝ→ℝ} (same : ∀ y:ℝ, 0≤y → f y=g y) {B : ℕ} (hb : 1≤B)
    {y:ℝ} (hy : 0≤y) : logOperator B f y=logOperator B g y := by
  unfold logOperator flatSum
  congr 1
  · apply sum_congr rfl
    intro d _
    rw [same _ (by positivity)]
  · apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by exact_mod_cast hb)] at ht
    have tp := zero_lt_one.trans_le ht.1
    rw [density,density,same _ (by positivity)]

theorem op_delta (f : ℝ→ℝ) (cont : continuousRanges f) {B : ℕ} (hb : 1≤B)
    {y:ℝ} (hy : 0≤y) : logOperator B (delta f) y =
      logOperator B f y-2*logOperator B f (y/2) := by
  have b : (1:ℝ)≤B := by exact_mod_cast hb
  have finiteEq : flatSum oddMangoldt (delta f) B y = flatSum oddMangoldt f B y -
      2*flatSum oddMangoldt f B (y/2) := by
    unfold flatSum
    rw [mul_sum,←sum_sub_distrib]
    apply sum_congr rfl
    intro d _
    rw [delta,div_right_comm y (d:ℝ) 2]
    ring
  have eq (t:ℝ) : density (delta f) y t = density f y t-2*density f (y/2) t := by
    rw [density,delta,density,density,div_right_comm y t 2]
    ring
  unfold logOperator
  simp only [eq]
  rw [finiteEq,intervalIntegral.integral_sub (integrable_density cont hy b)
      ((integrable_density cont (by positivity : 0≤y/2) b).const_mul 2),intervalIntegral.integral_const_mul]
  ring

theorem log_L {B:ℕ} (hb : 1≤B) {y:ℝ} (hy:0<y) (cap:y≤B) :
    logOperator B L y = log y*L y+2*log 2*W (y/2) := by
  rw [op_congr (fun _ h => L_is_delta h) hb hy.le,op_delta W W_cont hb hy.le,
      logOperator_odd hb hy cap,logOperator_odd hb (half_pos hy) (by linarith),
      L_is_delta hy.le,delta,log_div hy.ne' (by norm_num)]
  ring

theorem log_G {B:ℕ} (hb : 1≤B) {y:ℝ} (hy:0<y) (cap:y≤B) :
    logOperator B G y = log y*G y+4*log 2*L (y/2) := by
  change logOperator B (delta L) y=_
  rw [op_delta L L_cont hb hy.le,log_L hb hy cap,log_L hb (half_pos hy) (by linarith),
      G_is_delta,delta,log_div hy.ne' (by norm_num),L_is_delta (by positivity : 0≤y/2),delta]
  ring

theorem centered_delta {y:ℝ} (hy:0<y) :
    F y=2*F (y/2)+(1-eulerMascheroniConstant-log y)*G y := by
  have repr {u:ℝ} (hu:0≤u) : F u = log 2*W u-(log u+fixedBandLogConstant)*L u := by
    rw [F,fixedBandCenteredKernel,W_is_odd_ramp hu]
  rw [repr hy.le,repr (by positivity),G_is_delta,delta,log_div hy.ne' (by norm_num)]
  dsimp only [fixedBandLogConstant]
  have eq := L_is_delta hy.le
  dsimp only [delta] at eq
  linear_combination -(log 2)*eq

def trans (N:ℕ) (f : ℝ→ℝ) (x:ℝ) := ∑ d ∈ Ioc 0 N, (μ d:ℝ)*f (x/d)
theorem G_null {x:ℝ} {N:ℕ} (hx:8≤x) (cap:x≤N) : trans N G x=0 := latticeDifference_zero hx cap
theorem G_decay {y:ℝ} (hy:0<y) : |G y|≤300/y := latticeDifference_decay hy

theorem logOperator_null {x:ℝ} {B N:ℕ} (hb:1≤B) (lo:8*(B:ℝ)≤x) (cap:x≤N) :
    trans N (logOperator B G) x=0 := by
  let S := Ioc 0 N
  let T := Ioc 0 B
  have b : (1:ℝ)≤B := by exact_mod_cast hb
  have x0 : 0≤x := by linarith
  have zero_dil {t:ℝ} (h1 : 1≤t) (h2 : t≤B) :
      trans N G (x/t)=0 := by
    have tp := zero_lt_one.trans_le h1
    apply G_null ((le_div_iff₀ tp).mpr (by linarith)) ((div_le_self x0 h1).trans cap)
  have finiteEq : (∑ d ∈ S, (μ d:ℝ)*flatSum oddMangoldt G B (x/d)) = 0 := by
    calc _ = ∑ k ∈ T, oddMangoldt k*trans N G (x/k) := by
           simp only [flatSum,trans,mul_sum,S,T]
           rw [sum_comm]
           apply sum_congr rfl
           intro k _
           apply sum_congr rfl
           intro d _
           rw [div_right_comm x (d:ℝ) (k:ℝ)]
           ring
         _ = 0 := by
           apply sum_eq_zero
           intro k hk
           rw [zero_dil (by exact_mod_cast (mem_Ioc.mp hk).1) (by exact_mod_cast (mem_Ioc.mp hk).2),mul_zero]
  let f := fun (d:ℕ) (t:ℝ) => (μ d:ℝ)*density G (x/d) t
  have intg (d:ℕ) (_:d∈S) : IntervalIntegrable (f d) volume 1 B :=
    (integrable_density G_cont (by positivity : 0≤x/d) b).const_mul _
  have sumzero (t:ℝ) (ht:t∈Set.uIcc 1 (B:ℝ)) : (∑ d ∈ S, f d t)=0 := by
    rw [Set.uIcc_of_le b] at ht
    calc _ = (1+1/t)*trans N G (x/t) := by
           rw [trans,mul_sum]
           apply sum_congr rfl
           intro d _
           dsimp only [f,density]
           rw [div_right_comm x (d:ℝ) t]
           ring
         _ = 0 := by rw [zero_dil ht.1 ht.2,mul_zero]
  have intEq : (∑ d ∈ S, (μ d:ℝ)*(∫ t in (1:ℝ)..B, density G (x/d) t))=0 := by
    calc _ = ∑ d ∈ S, ∫ t in (1:ℝ)..B, f d t := by
           apply sum_congr rfl
           intro d _
           exact (intervalIntegral.integral_const_mul _ _).symm
         _ = 0 := by
           rw [←intervalIntegral.integral_finsetSum intg,intervalIntegral.integral_congr sumzero,
             intervalIntegral.integral_zero]
  change (∑ d ∈ S, (μ d:ℝ)*(flatSum oddMangoldt G B (x/d) + ∫ t in (1:ℝ)..B, density G (x/d) t)) = 0
  simp only [mul_add,sum_add_distrib,finiteEq,intEq,add_zero]

theorem odd_weight {k B:ℕ} (hk:k∈Ioc 0 B) : |oddMangoldt k|≤log B := by
  have b := log_natCast_nonneg B
  change |if 2 ∣ k then 0 else ArithmeticFunction.vonMangoldt k| ≤ _
  by_cases h : 2 ∣ k
  · rwa [if_pos h,abs_zero]
  · rw [if_neg h,abs_of_nonneg vonMangoldt_nonneg]
    exact vonMangoldt_le_log.trans (log_le_log (Nat.cast_pos.mpr (mem_Ioc.mp hk).1) (by exact_mod_cast (mem_Ioc.mp hk).2))

theorem logOperator_decay {B:ℕ} (hb:1≤B) {y:ℝ} (hy:0<y) :
    |logOperator B G y| ≤ 300*(B:ℝ)^2*(2+log B)/y := by
  have b : (1:ℝ)≤B := by exact_mod_cast hb
  have b0 : (0:ℝ)≤B := by positivity
  have blog := log_natCast_nonneg B
  have finiteLe : |flatSum oddMangoldt G B y| ≤ (B:ℝ)*(log B*(300*B/y)) := by
    apply (abs_sum_le_sum_abs ..).trans
    calc
      _ ≤ ∑ _k ∈ Ioc 0 B, log B*(300*B/y) := by
        apply sum_le_sum
        intro k hk
        have kpos := Nat.cast_pos (α:=ℝ).mpr (mem_Ioc.mp hk).1
        rw [abs_mul]
        apply mul_le_mul (odd_weight hk) _ (abs_nonneg _) blog
        apply (G_decay (div_pos hy kpos)).trans
        rw [div_div_eq_mul_div]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast (mem_Ioc.mp hk).2) (by norm_num)) hy.le
      _ = _ := by rw [sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul]
  have I := intervalIntegral.norm_integral_le_of_norm_le_const (a:=(1:ℝ)) (b:=(B:ℝ))
    (f:=density G y) (C:=600*B/y) (by
      intro t ht
      rw [Set.uIoc_of_le b] at ht
      have tp := zero_lt_one.trans ht.1
      have factor : 1+1/t≤2 := by have := (one_div_le_one_div_of_le zero_lt_one ht.1.le); linarith [this]
      rw [Real.norm_eq_abs,density,abs_mul,abs_of_nonneg (by positivity : 0≤1+1/t)]
      calc _ ≤ 2*(300/(y/t)) := mul_le_mul factor (G_decay (div_pos hy tp)) (abs_nonneg _) (by norm_num)
           _ = (600/y)*t := by field_simp; ring
           _ ≤ (600/y)*B := mul_le_mul_of_nonneg_left ht.2 (by positivity)
           _ = _ := by ring)
  rw [Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤(B:ℝ)-1)] at I
  unfold logOperator
  apply (abs_add_le _ _).trans
  apply (add_le_add finiteLe I).trans
  have rem : 0≤600*B/y := by positivity
  calc _ ≤ (B:ℝ)*(log B*(300*B/y)) + 600*B/y*B :=
           add_le_add le_rfl (mul_le_mul_of_nonneg_left (by linarith) rem)
       _ = _ := by ring

end RiemannReduction.BandLog

