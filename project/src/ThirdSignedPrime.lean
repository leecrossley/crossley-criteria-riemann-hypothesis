import ThirdQuotientBridge
import FourthSignedCriterion

/-! Compare the shortened linear tail to the prime-window family's paired remainder,
with its actual signs and on its complete square windows. -/
noncomputable section
namespace RiemannReduction.ThirdPrime
open Real Finset RiemannGaussian.AlpogeMined RiemannReduction.ThirdBridge
open RiemannReduction.DivisorBand RiemannReduction.DivisorBand.FourthMass

open Lean Elab Command in
run_cmd do
  let source := ((`_private ++ `CheckAlpogeFixedPrimeBandCentered).num 0) ++
    `RiemannGaussian.AlpogeMined.fixedBandMultipleCutoff_cost
  let i ← getConstInfo source
  liftTermElabM <| addDecl <| .thmDecl {
    name := `RiemannReduction.ThirdPrime.cutoff_cost
    levelParams := i.levelParams
    type := i.type
    value := mkConst source (i.levelParams.map Level.param) }

/-- The pointwise comparison underlying the public critical-tail mass estimate. -/
private theorem ordinary_full :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 2 ≤ n →
      |ordinary n-fixedBandCenteredTail (n^4) (fixedBandMultipleCutoff n)| ≤ C*(n:ℝ)^2 := by
  obtain ⟨C,hC,h⟩ := dyadicPrimeDeficit_power_cost
  let B := 4*(72+60*|fixedBandLogConstant|)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨C+B,by positivity,fun {n} hn => ?_⟩
  have eq : ordinary n = dyadicPrimeDeficit ((n:ℝ)^4) := ordinary_eq_fixed_band n
  rw [eq]
  have hp : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  obtain ⟨low,high⟩ := h (pow_pos hp 4)
  rw [show sqrt ((n:ℝ)^4) = (n:ℝ)^2 by rw [show (n:ℝ)^4=((n:ℝ)^2)^2 by ring,
    Real.sqrt_sq (sq_nonneg (n:ℝ))]] at high
  have K := fixedBandMultipleCutoff_bounds (V:=n^2) hn le_rfl (by omega)
  have N := (by decide : 4 ≤ 2^4).trans (Nat.pow_le_pow_left hn 4)
  have err := (fixedBandCenteredTail_error N K.2.2).trans (cutoff_cost hn)
  rw [Nat.cast_pow] at err
  apply (abs_sub_le _ (dyadicContrast ((n:ℝ)^4)) _).trans
  rw [abs_of_nonneg low]
  exact (add_le_add high err).trans_eq (by dsimp [B]; ring)

private theorem full_to_half {n : ℕ} (hn : 2 ≤ n) :
    |fixedBandCenteredTail (n^4) (fixedBandMultipleCutoff n)-
      fixedBandHalfTail (n^4) (fixedBandMultipleCutoff n)| ≤ 1500*(n:ℝ)^2 := by
  have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have hK : fixedBandMultipleCutoff n ≤ n^3 := Nat.div_le_self ..
  have h₄ := (by decide : 16 ≤ 2^4).trans (Nat.pow_le_pow_left hn 4)
  have h₃ : n^3 ≤ n^4 := Nat.pow_le_pow_right (by omega) (by decide)
  apply (fixedBandHalfTail_error h₄ (hK.trans h₃)).trans
  rw [Nat.cast_pow]
  apply (div_le_iff₀ (pow_pos hnR 4)).mpr
  calc 1500*(fixedBandMultipleCutoff n:ℝ)^2 ≤ 1500*((n:ℝ)^3)^2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hK) 2) (by norm_num)
       _ = _ := by ring

theorem remainder_third : ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 10^8 ≤ n →
    |remainder n-thirdSample n| ≤ C*(n:ℝ)^2 := by
  obtain ⟨C,hC,h⟩ := ordinary_full
  refine ⟨C+13519,by positivity,fun {n} late => ?_⟩
  have hn : 2 ≤ n := by omega
  have M := ordinary_remainder_error late
  rw [abs_sub_comm] at M
  calc
    _ ≤ |remainder n-ordinary n|+|ordinary n-thirdSample n| := abs_sub_le ..
    _ ≤ 19*(n:ℝ)^2+(|ordinary n-fixedBandCenteredTail (n^4) (fixedBandMultipleCutoff n)|+
      |fixedBandCenteredTail (n^4) (fixedBandMultipleCutoff n)-thirdSample n|) := add_le_add M (abs_sub_le ..)
    _ ≤ 19*(n:ℝ)^2+(C*(n:ℝ)^2+(|fixedBandCenteredTail (n^4) (fixedBandMultipleCutoff n)-
      fixedBandHalfTail (n^4) (fixedBandMultipleCutoff n)|+
      |fixedBandHalfTail (n^4) (fixedBandMultipleCutoff n)-thirdSample n|)) :=
      add_le_add le_rfl (add_le_add (h hn) (abs_sub_le ..))
    _ ≤ 19*(n:ℝ)^2+(C*(n:ℝ)^2+(1500*(n:ℝ)^2+12000*(n:ℝ)^2)) :=
      add_le_add le_rfl (add_le_add le_rfl (add_le_add (full_to_half hn) (sample_error hn)))
    _ = _ := by ring

theorem remainder_third_mass :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℝ}, |s| ≤ 1 → ∀ {m : ℕ}, 10^8 ≤ m →
      |mass (signedRemainder s) m-thirdMass s m (m^2)| ≤ C*(1+2*log m) := by
  obtain ⟨C,hC,h⟩ := remainder_third
  refine ⟨C,hC,fun {s} hs {m} late => ?_⟩
  let x := fun n : ℕ => if 10^8 ≤ n then s*remainder n else s*thirdSample n
  have err {n : ℕ} (_hn : 2 ≤ n) : |x n-s*thirdSample n| ≤ C*(n:ℝ)^2 := by
    dsimp only [x]
    split_ifs with H
    · rw [←mul_sub,abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) hs).trans (h H)
    · rw [sub_self,abs_zero]
      positivity
  have total := fixedBand_mass_sqrt_error (x:=x) (y:=fun n => s*thirdSample n) hC
    (fun hn => err hn) (b:=m^2) (show 2 ≤ m by omega)
  have eq : (∑ n ∈ Icc m (m^2), max (x n) 0/(n:ℝ)^3) = mass (signedRemainder s) m := by
    apply sum_congr rfl
    intro n hn
    simp only [x,if_pos (late.trans (mem_Icc.mp hn).1),signedRemainder]
  rw [eq,Nat.cast_pow,log_pow,Nat.cast_ofNat] at total
  exact total

theorem cofinal_third {s : ℝ} (hs : |s| ≤ 1) :
    cofinalLogBound (signedRemainder s) ↔ cofinalLogBound (fun n => s*thirdSample n) := by
  obtain ⟨B,hB,together⟩ := remainder_third_mass
  constructor <;> rintro ⟨C,hC,h⟩ <;> refine ⟨C+B,by positivity,fun A => ?_⟩ <;>
    obtain ⟨m,hm,hw⟩ := h (max (10^8) A)
  all_goals
    have he := abs_le.mp (together hs ((le_max_left _ A).trans hm))
    change -(B*(1+2*log m)) ≤ mass (signedRemainder s) m-mass (fun n => s*thirdSample n) m ∧
      mass (signedRemainder s) m-mass (fun n => s*thirdSample n) m ≤ B*(1+2*log m) at he
    exact ⟨m,(le_max_right _ _).trans hm,by linarith only [hw,he.1,he.2]⟩

theorem rh_iff_third_signed (s : ℝ) (sign : s=1 ∨ s= -1) :
    RiemannHypothesis ↔ cofinalLogBound (fun n => s*thirdSample n) :=
  (rh_iff_signed_quartic_budget s sign).trans (cofinal_third (by rcases sign with rfl|rfl <;> norm_num))

theorem all_squares_of_negative_third (h : cofinalLogBound (fun n => (-1:ℝ)*thirdSample n)) :
    ∃ C > (0:ℝ), ∀ k : ℕ, 3≤k → |D ((k:ℝ)^2)| ≤ C*k :=
  all_squares_of_quartic_loss ((cofinal_third (s:=-1) (by norm_num)).mpr h)

end RiemannReduction.ThirdPrime
#print axioms RiemannReduction.ThirdPrime.remainder_third
#print axioms RiemannReduction.ThirdPrime.remainder_third_mass
#print axioms RiemannReduction.ThirdPrime.rh_iff_third_signed
#print axioms RiemannReduction.ThirdPrime.all_squares_of_negative_third

