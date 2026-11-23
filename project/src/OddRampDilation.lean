import ThirdQuotientBridge
import DivisorBand

/-! The logarithm of an odd-index reciprocal ramp can be written as a sum
over odd prime powers and an ordinary integral over its dilations. -/
noncomputable section
namespace RiemannReduction.BandLog
open Finset Real ArithmeticFunction RiemannGaussian.AlpogeMined RiemannReduction.DivisorBand
open scoped ArithmeticFunction.zeta ArithmeticFunction.vonMangoldt
open MeasureTheory intervalIntegral

def ramp (x : ℝ) := max (x-1) 0
def oddPart (a : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun k => if 2 ∣ k then 0 else a k, by simp⟩

theorem oddPart_mul (a b : ArithmeticFunction ℝ) : oddPart a * oddPart b = oddPart (a*b) := by
  ext n
  change _ = if 2 ∣ n then 0 else (a*b) n
  rw [mul_apply]
  split_ifs with hn
  · apply sum_eq_zero
    intro ab hab
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hab).1
    obtain h|h := Nat.prime_two.dvd_mul.mp (hprod ▸ hn : 2 ∣ ab.1*ab.2)
    · change (if 2 ∣ ab.1 then 0 else _) * _ = _
      rw [if_pos h,zero_mul]
    · change _ * (if 2 ∣ ab.2 then 0 else _) = _
      rw [if_pos h,mul_zero]
  · rw [mul_apply]
    apply sum_congr rfl
    intro ab hab
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hab).1
    have h : ¬ 2 ∣ ab.1*ab.2 := hprod ▸ hn
    rcases not_or.mp (mt Nat.prime_two.dvd_mul.mpr h) with ⟨h₁,h₂⟩
    change (if 2 ∣ ab.1 then 0 else _) * (if 2 ∣ ab.2 then 0 else _) = _
    rw [if_neg h₁,if_neg h₂]

def flatSum (a : ℕ → ℝ) (f : ℝ → ℝ) (B : ℕ) (x : ℝ) := ∑ k ∈ Ioc 0 B, a k * f (x/k)
def oddUnits : ArithmeticFunction ℝ := oddPart ζ
def oddMangoldt : ArithmeticFunction ℝ := oddPart ArithmeticFunction.vonMangoldt
def W : ℝ → ℝ := dilate oddUnits ramp

theorem ramp_zero {x : ℝ} (hx : x ≤ 1) : ramp x=0 := max_eq_right (by linarith)
theorem dilate_flat (a : ArithmeticFunction ℝ) (f : ℝ → ℝ) (small : ∀ {x}, x ≤ 1 → f x=0)
    {x : ℝ} {B : ℕ} (hx : 0 ≤ x) (hb : x ≤ B) :
    dilate a f x = flatSum a f B x := by
  unfold dilate flatSum
  rw [show Icc 1 ⌊x⌋₊ = Ioc 0 ⌊x⌋₊ by ext k; simp only [mem_Icc,mem_Ioc]; omega]
  apply sum_subset (Ioc_subset_Ioc_right ((Nat.floor_mono hb).trans (by simp)))
  intro i hi hout
  obtain ⟨hpos,_⟩ := mem_Ioc.mp hi
  have beyond : ⌊x⌋₊ < i := by
    by_contra! H
    exact hout (mem_Ioc.mpr ⟨hpos,H⟩)
  rw [small ((div_le_one (Nat.cast_pos.mpr hpos)).mpr ((Nat.floor_lt hx).mp beyond).le),mul_zero]

theorem W_small {x : ℝ} (hx : x ≤ 1) : W x=0 := by
  unfold W dilate
  apply sum_eq_zero
  intro i hi
  have hp := Nat.cast_pos (α:=ℝ).mpr (mem_Icc.mp hi).1
  rw [ramp_zero ((div_le_one hp).mpr (hx.trans (by exact_mod_cast (mem_Icc.mp hi).1))),mul_zero]

private theorem U_sums {x : ℝ} {B : ℕ} (hx : 0 ≤ x) (hb : x ≤ B) :
    flatSum (fun _ => 1) ramp B x = fixedBandUnitRamp x := by
  simpa [flatSum,ramp] using fixedBandUnitRamp_sum hx hb

theorem W_is_odd_ramp {x : ℝ} (hx : 0 ≤ x) : W x = fixedBandUnitRamp x-fixedBandUnitRamp (x/2) := by
  let B := ⌊x⌋₊+1
  have hB : x ≤ (B:ℝ) := by dsimp [B]; push_cast; exact (Nat.lt_floor_add_one x).le
  rw [W,dilate_flat oddUnits ramp (fun h => ramp_zero h) hx hB,←U_sums hx hB]
  let S := Ioc 0 B
  have filtered : flatSum oddUnits ramp B x = ∑ d ∈ S.filter (fun k => ¬ 2 ∣ k), ramp (x/d) := by
    unfold flatSum
    rw [sum_filter]
    apply sum_congr rfl
    intro k hk
    have kp := (mem_Ioc.mp hk).1.ne'
    by_cases h : 2 ∣ k <;> simp [oddUnits,oddPart,h,kp]
  have evenSum : (∑ k ∈ S.filter (fun k => 2 ∣ k), ramp (x/k)) =
      fixedBandUnitRamp (x/2) := by
    have half : x/2 ≤ (B:ℝ) := by linarith
    rw [←U_sums (by positivity) half]
    unfold flatSum
    simp only [one_mul]
    have cut : (∑ d ∈ Ioc 0 (B/2),ramp (x/2/d)) = ∑ d ∈ Ioc 0 B,ramp (x/2/d) := by
      apply sum_subset (Ioc_subset_Ioc_right (Nat.div_le_self ..))
      intro d hd outside
      obtain ⟨hp,_⟩ := mem_Ioc.mp hd
      have dh : B/2 < d := lt_of_not_ge fun h => outside (mem_Ioc.mpr ⟨hp,h⟩)
      apply ramp_zero
      apply (div_le_one (Nat.cast_pos.mpr hp)).mpr
      have h : (B:ℝ) ≤ 2*d := by exact_mod_cast (show B ≤ 2*d by omega)
      linarith
    rw [←cut]
    symm
    apply sum_bij (fun d _ => 2*d)
    · intro d hd
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by have := (mem_Ioc.mp hd).1; omega,by have := (mem_Ioc.mp hd).2; omega⟩,dvd_mul_right ..⟩
    · intro a ha b hb eq
      omega
    · intro k hk
      obtain ⟨inS,⟨d,rfl⟩⟩ := mem_filter.mp hk
      exact ⟨d,mem_Ioc.mpr ⟨by have := (mem_Ioc.mp inS).1; omega,by have := (mem_Ioc.mp inS).2; omega⟩,rfl⟩
    · intro d _
      simp only [Nat.cast_mul,Nat.cast_ofNat,div_div]
  rw [filtered,←evenSum]
  have split := sum_filter_add_sum_filter_not S (fun k => 2 ∣ k) (fun k => ramp (x/k))
  simp only [flatSum,one_mul]
  dsimp only [S] at split ⊢
  linarith only [split]

def density (f : ℝ → ℝ) (y t : ℝ) := (1+1/t)*f (y/t)
def logOperator (B : ℕ) (f : ℝ → ℝ) (y : ℝ) :=
  flatSum oddMangoldt f B y + ∫ t in (1:ℝ)..B, density f y t

theorem integrable_density {f : ℝ → ℝ} (cont : ∀ Y:ℝ, ContinuousOn f (Set.Icc 0 Y))
    {y T : ℝ} (hy : 0≤y) (hT : 1≤T) : IntervalIntegrable (density f y) volume 1 T := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hT]
  have arg : ContinuousOn (fun t:ℝ => y/t) (Set.Icc 1 T) :=
    continuousOn_const.div continuousOn_id fun t ht => by dsimp; linarith [ht.1]
  have maps : Set.MapsTo (fun t:ℝ => y/t) (Set.Icc 1 T) (Set.Icc 0 y) :=
    fun t ht => ⟨div_nonneg hy (by linarith [ht.1]),div_le_self hy ht.1⟩
  exact (continuousOn_const.add (continuousOn_const.div continuousOn_id
    (fun t (ht : t ∈ Set.Icc 1 T) => by dsimp; linarith [ht.1]))).mul ((cont y).comp arg maps)

private theorem ramp_integral {y T : ℝ} (hy : 0<y) (hT : 1≤T) (hcap : y≤T) :
    (∫ t in (1:ℝ)..T, density ramp y t) = log y*ramp y := by
  have cont : ∀ Y:ℝ, ContinuousOn ramp (Set.Icc 0 Y) := by intro Y; unfold ramp; fun_prop
  have above {a b : ℝ} (ha : 0<a) (hab : a≤b) (hya : y≤a) :
      (∫ t in a..b, density ramp y t)=0 := by
    rw [← intervalIntegral.integral_zero (a:=a) (b:=b) (E:=ℝ)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    rw [density,ramp_zero ((div_le_one (ha.trans_le ht.1)).mpr (hya.trans ht.1)),mul_zero]
  by_cases low : y ≤ 1
  · rw [above zero_lt_one hT low,ramp_zero low,mul_zero]
  have h1 : 1≤y := le_of_not_ge low
  have tail := above hy hcap le_rfl
  have hi := integrable_density cont hy.le h1
  have rest : IntervalIntegrable (density ramp y) volume y T := by
    exact (integrable_density cont hy.le hT).mono_set (by rw [Set.uIcc_of_le hcap,Set.uIcc_of_le hT]; exact Set.Icc_subset_Icc h1 le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hi rest,tail,add_zero]
  let prim := fun t : ℝ => (y-1)*log t-y/t-t
  have val : (∫ t in (1:ℝ)..y, density ramp y t) = prim y - prim 1 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=prim) _ hi
    intro t ht
    rw [Set.uIcc_of_le h1] at ht
    have hp := zero_lt_one.trans_le ht.1
    rw [density,ramp,max_eq_left (sub_nonneg.mpr ((one_le_div hp).mpr ht.2))]
    have scalar : (1+1/t)*(y/t-1)=(y-1)*t⁻¹-(0*t-y*1)/t^2-1 := by field_simp; ring
    rw [scalar]
    exact (((Real.hasDerivAt_log hp.ne').const_mul (y-1)).sub
      ((hasDerivAt_const t y).div (hasDerivAt_id' t) hp.ne')).sub (hasDerivAt_id' t)
  rw [val,ramp,max_eq_left (by linarith)]
  simp only [prim,log_one,mul_zero,div_one,div_self hy.ne']
  ring

/-- This uses the divisor-sum identity for the von Mangoldt function on odd integers. -/
theorem logOperator_odd {B : ℕ} (hB : 1≤B) {y : ℝ} (hy : 0<y) (hcap : y≤B) :
    logOperator B W y = log y*W y := by
  have b : (1:ℝ)≤B := by exact_mod_cast hB
  let S := Ioc 0 B
  have integrated : (∫ t in (1:ℝ)..B, density W y t) =
       ∑ k ∈ S, oddUnits k*(log (y/k)*ramp (y/k)) := by
    have f (k:ℕ) (hk:k∈S) : IntervalIntegrable (fun t:ℝ => oddUnits k*density ramp (y/k) t) volume 1 B := by
      apply IntervalIntegrable.const_mul
      apply integrable_density (fun Y => by unfold ramp; fun_prop) (by positivity) b
    have equal : ∀ t ∈ Set.uIcc 1 (B:ℝ), density W y t =
        ∑ k ∈ S, oddUnits k*density ramp (y/k) t := by
      intro t ht
      rw [Set.uIcc_of_le b] at ht
      have tp := zero_lt_one.trans_le ht.1
      rw [density,W,dilate_flat oddUnits ramp (fun h => ramp_zero h) (by positivity) ((div_le_self hy.le ht.1).trans hcap),flatSum,mul_sum]
      apply sum_congr rfl
      intro k _
      rw [density,div_right_comm y t (k:ℝ)]
      ring
    rw [intervalIntegral.integral_congr equal,intervalIntegral.integral_finsetSum f]
    apply sum_congr rfl
    intro k hk
    have hp := Nat.cast_pos (α:=ℝ).mpr (mem_Ioc.mp hk).1
    rw [intervalIntegral.integral_const_mul,ramp_integral (div_pos hy hp) b
      ((div_le_self hy.le (by exact_mod_cast (mem_Ioc.mp hk).1)).trans hcap)]
  have arith : flatSum oddMangoldt W B y = flatSum (oddPart ArithmeticFunction.log) ramp B y := by
    rw [←dilate_flat oddMangoldt W (fun h => W_small h) hy.le hcap]
    change dilate oddMangoldt (dilate oddUnits ramp) y = _
    rw [←dilate_mul]
    change dilate (oddPart (vonMangoldt:ArithmeticFunction ℝ)*oddPart ζ) ramp y = _
    rw [oddPart_mul,vonMangoldt_mul_zeta,dilate_flat _ ramp (fun h => ramp_zero h) hy.le hcap]
  rw [logOperator,arith,integrated,W,dilate_flat oddUnits ramp (fun h => ramp_zero h) hy.le hcap]
  unfold flatSum
  rw [mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  have hp := (mem_Ioc.mp hk).1.ne'
  have kR : (k:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  by_cases even : 2 ∣ k
  · simp [oddPart,oddUnits,even]
  · simp only [oddPart,oddUnits,coe_mk,if_neg even,natCoe_apply,zeta_apply_ne hp,Nat.cast_one,
      one_mul,ArithmeticFunction.log_apply,log_div hy.ne' kR]
    ring

end RiemannReduction.BandLog

