import AllDyadicBands
import SquareConstant

/-! Exact integer cutoffs, with the finite prime and Möbius tables exposed. -/
noncomputable section
namespace RiemannReduction.BalancedSquare
open Finset Real RiemannReduction.BandLog RiemannReduction.DyadicBands
open RiemannReduction.DivisorBand RiemannGaussian.AlpogeMined
open scoped ArithmeticFunction.Moebius

def operatorWith (a : ℕ→ℝ) (B:ℕ) (y:ℝ) :=
  flatSum a G B y + ∫ t in (1:ℝ)..B, density G y t

def correctionWith (a : ℕ→ℝ) : ℕ→ℝ→ℝ
  | 0,_ => 0
  | j+1,y => 2*correctionWith a j (y/2)+(1-eulerMascheroniConstant)*G y
       -operatorWith a (2^(j+1)) y+4*log 2*lat j (y/2)

def atCut (a:ℕ→ℝ) (B:ℕ) (y:ℝ) :=
  2*correctionWith a (squareDepth B) (y/2)+(1-eulerMascheroniConstant)*G y
       -operatorWith a B y+4*log 2*lat (squareDepth B) (y/2)

def tableSum (u a:ℕ→ℝ) (N B:ℕ) : ℝ := ∑ d ∈ Ioc 0 (N/B), u d*(F ((N:ℝ)/d)-atCut a B ((N:ℝ)/d))

def mobiusTable (d:ℕ):ℝ := μ d

private theorem actual (j:ℕ) : correctionWith oddMangoldt j = correction j := by
  induction j with
  | zero => rfl
  | succ j h => funext y; rw [correctionWith,h,correction]; rfl

theorem top_identity (B:ℕ) (y:ℝ) :
    atCut oddMangoldt B y = correction (squareDepth B+1) y+
      logOperator (2^(squareDepth B+1)) G y-logOperator B G y := by
  rw [atCut,actual,correction]
  change _-logOperator B G y+_=_-logOperator _ G y+_+_-_
  ring

theorem cap_agrees {B:ℕ} (hp:0<B) {y:ℝ} (hy:0<y) (h:y≤B) : atCut oddMangoldt B y=F y := by
  have big := (Nat.lt_pow_succ_log_self (by decide : 1<2) B).le
  have cap : y≤(2:ℝ)^(squareDepth B+1) := h.trans (by exact_mod_cast big)
  rw [top_identity,(agrees (squareDepth B+1) hy cap).2,log_G (Nat.succ_le_of_lt (by positivity)) hy
    (by exact_mod_cast cap),log_G hp hy h]
  ring

theorem cap_null {N B:ℕ} {x:ℝ} (hp:0<B) (low:8*2^(squareDepth B+1)≤x) (hi:x≤N) :
    BandLog.trans N (atCut oddMangoldt B) x=0 := by
  have big : (B:ℝ)≤2^(squareDepth B+1) := by exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1<2) B).le
  have h := (DyadicBands.null (squareDepth B+1) low hi).2
  have A := logOperator_null (B:=2^(squareDepth B+1)) (Nat.succ_le_of_lt (by positivity)) (by exact_mod_cast low) hi
  have b := logOperator_null hp (show 8*(B:ℝ)≤x by linarith) hi
  calc _ = BandLog.trans N (correction (squareDepth B+1)) x
        +BandLog.trans N (logOperator (2^(squareDepth B+1)) G) x-BandLog.trans N (logOperator B G) x := by
          unfold BandLog.trans
          simp only [top_identity,mul_sub,mul_add,sum_sub_distrib,sum_add_distrib]
       _ = 0 := by rw [h,A,b]; ring

/-- An exact two-table identity at any integer cap past the first layer. -/
theorem exact_at_cut {N B:ℕ} (bp:0<B) (late:16*B≤N) :
    D (N:ℝ)=tableSum mobiusTable oddMangoldt N B := by
  have left : 2^squareDepth B≤B := Nat.pow_log_le_self 2 bp.ne'
  have bound : 8*2^(squareDepth B+1)≤N := by rw [pow_succ]; omega
  have np : 0<N := by omega
  have z := cap_null (N:=N) bp (by exact_mod_cast bound) (le_rfl:(N:ℝ)≤N)
  rw [deficit_contrast (Nat.cast_pos.mpr np),fixedBand_centered_identity (by omega : 4≤N)]
  have all : (∑ d ∈ Ioc 0 N,mobiusTable d*(F ((N:ℝ)/d)-atCut oddMangoldt B ((N:ℝ)/d))) =
      ∑ d ∈ Ioc 0 N,mobiusTable d*F ((N:ℝ)/d) := by
    simp only [mul_sub,sum_sub_distrib]
    exact sub_eq_self.mpr z
  change (∑ d ∈ Ioc 0 N,mobiusTable d*F ((N:ℝ)/d)) = _
  rw [←all]
  symm
  apply sum_subset (Ioc_subset_Ioc_right (Nat.div_le_self ..))
  intro d hd outside
  have pos := (mem_Ioc.mp hd).1
  have beyond : N/B<d := lt_of_not_ge fun h => outside (mem_Ioc.mpr ⟨pos,h⟩)
  have bound' : (N:ℝ)/d≤B := (div_le_iff₀ (Nat.cast_pos.mpr pos)).mpr (by
    have l := (Nat.div_lt_iff_lt_mul bp).mp beyond
    exact_mod_cast (by simpa only [mul_comm] using l.le : N≤B*d))
  rw [cap_agrees bp (div_pos (Nat.cast_pos.mpr np) (Nat.cast_pos.mpr pos)) bound',sub_self,mul_zero]

private theorem operator_congr {a b:ℕ→ℝ} {B:ℕ} (agree:∀ i∈Ioc 0 B,a i=b i) (y:ℝ) :
    operatorWith a B y=operatorWith b B y := by
  unfold operatorWith
  congr 1
  apply sum_congr rfl
  intro k hk
  rw [agree k hk]

private theorem correction_congr {a b:ℕ→ℝ} (j:ℕ) (agree:∀ i∈Ioc 0 (2^j),a i=b i) :
    correctionWith a j=correctionWith b j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have le : (2:ℕ)^j≤2^(j+1) := Nat.pow_le_pow_right (by decide) (by omega)
    funext y
    rw [correctionWith,correctionWith,ih (fun i hi => agree i (Ioc_subset_Ioc_right le hi)),operator_congr agree]

theorem uses_only_prefixes {u v a b:ℕ→ℝ} {N B:ℕ} (bp:0<B)
    (rows:∀ i∈Ioc 0 (N/B),u i=v i) (weights:∀ i∈Ioc 0 B,a i=b i) :
    tableSum u a N B=tableSum v b N B := by
  have low : (2:ℕ)^squareDepth B≤B := Nat.pow_log_le_self 2 bp.ne'
  have inside := correction_congr (squareDepth B) (fun i hi => weights i (Ioc_subset_Ioc_right low hi))
  unfold tableSum
  apply sum_congr rfl
  intro d hd
  rw [rows d hd]
  simp only [atCut,inside,operator_congr weights]

def normalizedRows (k:ℕ) := tableSum mobiusTable oddMangoldt (k^2) k

/-- Both arithmetic tables stop at k for the prime-power deficit evaluated at k². -/
theorem balanced_square {k:ℕ} (hk:16≤k) : D ((k:ℝ)^2)=normalizedRows k := by
  have kp : 0<k := by omega
  have big : 16*k ≤ k^2 := by simpa only [pow_two] using Nat.mul_le_mul_right k hk
  rw [←Nat.cast_pow]
  exact exact_at_cut kp big

theorem balanced_input {k:ℕ} (hk:16≤k) {u a:ℕ→ℝ}
    (rows:∀ i∈Ioc 0 k,u i=mobiusTable i) (weights:∀ i∈Ioc 0 k,a i=oddMangoldt i) :
    D ((k:ℝ)^2)=tableSum u a (k^2) k := by
  rw [balanced_square hk]
  symm
  have kp : 0<k := by omega
  have r : k^2/k=k := by rw [pow_two,Nat.mul_div_cancel _ kp]
  apply uses_only_prefixes (N:=k^2) (B:=k) kp _ weights
  rw [r]
  exact rows

def lowerBlocks (C:ℝ) := ∀ m:ℕ,∃ K≥m,∀ k∈Icc K (K^2), -C*(k:ℝ)≤normalizedRows k

/-- The user's one-sided full-block target with only square-root length inputs. -/
theorem rh_iff_lower_blocks : RiemannHypothesis ↔ ∃ C:ℝ, 0<C ∧ lowerBlocks C := by
  constructor
  · intro rh
    obtain ⟨C,cp,all⟩ := square_root_bound_of_rh rh
    refine ⟨C,cp,fun m=>⟨max 16 m,le_max_right _ _,?_⟩⟩
    intro k hk
    have l := (le_max_left 16 m).trans (mem_Icc.mp hk).1
    rw [←balanced_square l]
    simpa only [neg_mul] using (abs_le.mp (all k (by omega))).1
  · rintro ⟨C,_,blocks⟩
    apply RiemannReduction.PrimeGrid.rh_of_any_square_bound (C:=C)
    intro m
    obtain ⟨K,start,checks⟩ := blocks (max 16 m)
    refine ⟨K,(le_max_right _ _).trans start,?_⟩
    intro k hk
    have l := ((le_max_left 16 m).trans start).trans (mem_Icc.mp hk).1
    have check := checks k hk
    rw [←balanced_square l,←Nat.cast_pow,D_nat] at check
    exact check

#print axioms balanced_input
#print axioms rh_iff_lower_blocks
end RiemannReduction.BalancedSquare

