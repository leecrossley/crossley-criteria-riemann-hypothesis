import LatticeLogCorrection
import FourthSignedCriterion

/-! Every dyadic cutoff can be imposed with an exact complete Möbius correction. -/
noncomputable section
namespace RiemannReduction.DyadicBands
open Finset Real RiemannReduction.BandLog RiemannReduction.DivisorBand
open RiemannGaussian.AlpogeMined
open scoped ArithmeticFunction.Moebius

/-- Reconstruct the triangular lattice from its dyadic differences up to 2^j. -/
def lat : ℕ → ℝ → ℝ
  | 0, _ => 0
  | j+1, y => G y+2*lat j (y/2)

/-- Each step adds one truncated odd prime-power operator and dyadic dilations. -/
def correction : ℕ → ℝ → ℝ
  | 0, _ => 0
  | j+1, y => 2*correction j (y/2)+(1-eulerMascheroniConstant)*G y
       -logOperator (2^(j+1)) G y + 4*log 2*lat j (y/2)

theorem agrees (j:ℕ) {y:ℝ} (hy:0<y) (cap:y≤2^j) :
    lat j y=L y ∧ correction j y=F y := by
  induction j generalizing y with
  | zero =>
    have h : y≤1 := by simpa using cap
    have l : L y=0 := by rw [L_is_delta hy.le,delta,W_small h,W_small (by linarith)]; ring
    have f : F y=0 := by
      change log 2*(fixedBandUnitRamp y-fixedBandUnitRamp (y/2))-(log y+fixedBandLogConstant)*L y=0
      rw [←W_is_odd_ramp hy.le,W_small h,l]
      ring
    exact ⟨l.symm,f.symm⟩
  | succ j ih =>
    have half : y/2≤2^j := by rw [pow_succ] at cap; linarith
    obtain ⟨hl,hf⟩ := ih (half_pos hy) half
    have logId := log_G (B:=2^(j+1)) (Nat.succ_le_of_lt (by positivity)) hy (by exact_mod_cast cap)
    constructor
    · rw [lat,hl,G_is_delta,delta]; ring
    · rw [correction,hl,hf,logId,centered_delta hy]
      ring

private theorem trans_combination (f g:ℝ→ℝ) (a b:ℝ) (N:ℕ) (x:ℝ) :
    BandLog.trans N (fun y => a*f y+b*g y) x = a*BandLog.trans N f x+b*BandLog.trans N g x := by
  simp only [BandLog.trans,mul_add,sum_add_distrib,mul_sum]
  congr 1 <;> apply sum_congr rfl <;> intro d _ <;> ring

private theorem trans_scale (f : ℝ→ℝ) (a:ℝ) (N:ℕ) (x:ℝ) :
    BandLog.trans N (fun y => f (y/a)) x = BandLog.trans N f (x/a) := by
  apply sum_congr rfl
  intro d _
  dsimp only
  rw [div_right_comm x (d:ℝ) a]

theorem null (j:ℕ) {N:ℕ} {x:ℝ} (large:8*2^j≤x) (cap:x≤N) :
    BandLog.trans N (lat j) x=0 ∧ BandLog.trans N (correction j) x=0 := by
  induction j generalizing x with
  | zero => simp [lat,correction,BandLog.trans]
  | succ j ih =>
    have p : (0:ℝ)<2^j := by positivity
    have half : 8*2^j ≤ x/2 := by rw [pow_succ] at large; linarith
    have cap2 : x/2 ≤ N := by linarith
    obtain ⟨l,f⟩ := ih half cap2
    have one : (1:ℝ)≤2^(j+1) := one_le_pow₀ (by norm_num)
    have g := G_null (show 8≤x by linarith) cap
    have z := logOperator_null (B:=2^(j+1)) (Nat.succ_le_of_lt (by positivity)) (by exact_mod_cast large) cap
    constructor
    · calc _ = BandLog.trans N G x+2*BandLog.trans N (lat j) (x/2) := by
             have he := trans_combination G (fun y => lat j (y/2)) 1 2 N x
             simpa only [lat,one_mul,trans_scale] using he
           _ = 0 := by rw [g,l]; ring
    · calc _ = 2*BandLog.trans N (correction j) (x/2)+(1-eulerMascheroniConstant)*BandLog.trans N G x -
                   BandLog.trans N (logOperator (2^(j+1)) G) x+ 4*log 2*BandLog.trans N (lat j) (x/2) := by
             unfold BandLog.trans
             simp only [correction,mul_add,mul_sub,sum_add_distrib,sum_sub_distrib,mul_sum]
             have scale (d:ℕ) : x/d/2=x/2/d := div_right_comm ..
             simp_rw [scale]
             congr 1
             · congr 1
               congr 1 <;> apply sum_congr rfl <;> intro d _ <;> ring
             · apply sum_congr rfl; intro d _; ring
           _ = 0 := by rw [g,l,f,z]; ring

/-- The prime-power deficit in the maintained square criterion equals the archived contrast. -/
theorem deficit_contrast {x:ℝ} (hx:0<x) : D x=dyadicContrast x := by
  rw [dyadicContrast_prime_power hx,D,←band_dilate,c,show log 2/2*x=x*log 2/2 by ring]
  congr 1
  unfold dilate
  rw [show Icc 1 ⌊x⌋₊ = Ioc 0 ⌊x⌋₊ by ext k; simp only [mem_Icc,mem_Ioc]; omega]
  apply sum_congr rfl
  intro k _
  rw [window,div_right_comm x (k:ℝ) 4,FourthMass.tent_at_prime]
  rfl

def shortSum (N j:ℕ) : ℝ := ∑ d ∈ Ioc 0 (N/(2^j)), (μ d:ℝ)*(F ((N:ℝ)/d)-correction j ((N:ℝ)/d))

/-- Exact elimination above N/2^j, uniform in j and including both endpoints. -/
theorem exact_sum {N j:ℕ} (large:8*2^j≤N) : D (N:ℝ)=shortSum N j := by
  have p : 0<(2:ℕ)^j := by positivity
  have N4 : 4≤N := by omega
  have pos := Nat.cast_pos (α:=ℝ).mpr (show 0<N by omega)
  have total := fixedBand_centered_identity N4
  have gone := (null j (N:=N) (x:=(N:ℝ)) (by exact_mod_cast large) le_rfl).2
  rw [deficit_contrast pos,total]
  have full : (∑ d ∈ Ioc 0 N, (μ d:ℝ)*(F ((N:ℝ)/d)-correction j ((N:ℝ)/d))) =
      (∑ d ∈ Ioc 0 N, (μ d:ℝ)*F ((N:ℝ)/d)) := by
    simp only [mul_sub,sum_sub_distrib]
    exact sub_eq_self.mpr gone
  rw [←full]
  symm
  apply sum_subset (Ioc_subset_Ioc_right (Nat.div_le_self ..))
  intro d hd outside
  obtain ⟨dp,upper⟩ := mem_Ioc.mp hd
  have beyond : N / 2^j < d := lt_of_not_ge fun h => outside (mem_Ioc.mpr ⟨dp,h⟩)
  have ratio : (N:ℝ)/d ≤ 2^j := (div_le_iff₀ (Nat.cast_pos.mpr dp)).mpr (by
    have h := (Nat.div_lt_iff_lt_mul p).mp beyond
    exact_mod_cast (by simpa only [mul_comm] using h.le : N≤2^j*d))
  rw [(agrees j (div_pos pos (Nat.cast_pos.mpr dp)) ratio).2,sub_self,mul_zero]

def squareDepth (k:ℕ) := Nat.log 2 k
def squareSum (k:ℕ) := shortSum (k^2) (squareDepth k)

theorem square_support {k:ℕ} (hk:0<k) :
    2^squareDepth k ≤ k ∧ k^2/(2^squareDepth k)<2*k := by
  have left := Nat.pow_log_le_self 2 hk.ne'
  have right := Nat.lt_pow_succ_log_self (by decide : 1<2) k
  rw [pow_succ] at right
  refine ⟨left,(Nat.div_lt_iff_lt_mul (by positivity : 0<2^squareDepth k)).mpr ?_⟩
  change k^2 < 2*k*(2^Nat.log 2 k)
  calc _ = k*k := pow_two _
       _ < (2^(Nat.log 2 k)*2)*k := Nat.mul_lt_mul_of_pos_right right hk
       _ = _ := by ring

theorem square_exact {k:ℕ} (hk:8≤k) : D ((k:ℝ)^2)=squareSum k := by
  have left := (square_support (by omega : 0<k)).1
  have scale : 8*2^squareDepth k ≤ k^2 := calc
    _ ≤ k*k := Nat.mul_le_mul hk left
    _ = _ := (pow_two _).symm
  rw [←Nat.cast_pow]
  exact exact_sum scale

end RiemannReduction.DyadicBands

