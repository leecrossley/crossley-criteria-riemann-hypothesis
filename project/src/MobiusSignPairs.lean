import PairingShell

/-! Pairing 391r with the appropriate neighboring prime multiple, according
to the actual sign of μ(r), in the retained portion of the linear sum. -/

noncomputable section
namespace RiemannReduction.ShortTail.SignPairs
open Finset Filter Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius

def leftFactor (r : ℕ) : ℕ := if μ r = -1 then 389 else 391
def rightFactor (r : ℕ) : ℕ := if μ r = -1 then 391 else 397
def leftIndex (r : ℕ) := leftFactor r*r
def rightIndex (r : ℕ) := rightFactor r*r

private theorem cases_factor (r : ℕ) :
    (leftFactor r=389 ∧ rightFactor r=391) ∨ (leftFactor r=391 ∧ rightFactor r=397) := by
  by_cases h : μ r = -1 <;> simp [leftFactor,rightFactor,h]

private theorem factors (r : ℕ) :
    leftFactor r ∈ ({389,391,397}:Finset ℕ) ∧ rightFactor r ∈ ({389,391,397}:Finset ℕ) ∧
    leftFactor r < rightFactor r := by
  rcases cases_factor r with ⟨a,b⟩|⟨a,b⟩ <;> rw [a,b] <;> decide

private theorem three_signs {n r : ℕ} (hr : r ∈ cofactors n) :
    μ (389*r) = -(μ r) ∧ μ (391*r) = μ r ∧ μ (397*r) = -(μ r) := by
  obtain ⟨_,_,p17,p23,p389,p397⟩ := cofactor_data hr
  have a : Nat.Coprime 389 r := (show Nat.Prime 389 by decide).coprime_iff_not_dvd.mpr p389
  have b : Nat.Coprime 391 r := by
    change Nat.Coprime (17*23) r
    exact Nat.coprime_mul_iff_left.mpr ⟨(show Nat.Prime 17 by decide).coprime_iff_not_dvd.mpr p17,
      (show Nat.Prime 23 by decide).coprime_iff_not_dvd.mpr p23⟩
  have c : Nat.Coprime 397 r := (show Nat.Prime 397 by decide).coprime_iff_not_dvd.mpr p397
  have m389 : μ 389 = -1 := moebius_apply_prime (by decide)
  have m391 : μ 391 = 1 := by
    change μ (17*23) = 1
    rw [isMultiplicative_moebius.map_mul_of_coprime (by decide : Nat.Coprime 17 23),
      moebius_apply_prime (by decide : Nat.Prime 17),moebius_apply_prime (by decide : Nat.Prime 23)]
    norm_num
  have m397 : μ 397 = -1 := moebius_apply_prime (by decide)
  simp [isMultiplicative_moebius.map_mul_of_coprime a,isMultiplicative_moebius.map_mul_of_coprime b,
    isMultiplicative_moebius.map_mul_of_coprime c,m389,m391,m397]

theorem mobius_pair_signs {n r : ℕ} (hr : r ∈ cofactors n) :
    μ (leftIndex r) = 1 ∧ μ (rightIndex r) = -1 := by
  obtain ⟨a,b,c⟩ := three_signs hr
  rcases moebius_ne_zero_iff_eq_or.mp (moebius_ne_zero_iff_squarefree.mpr (cofactor_data hr).2.1) with s|s <;>
    simp [leftIndex,rightIndex,leftFactor,rightFactor,s,a,b,c]

theorem pair_credit {n r : ℕ} (hn : 100000 ≤ n) (hr : r ∈ cofactors n) :
    1/5 ≤ -term n (rightIndex r) ∧ 1/400 ≤ term n (leftIndex r)+term n (rightIndex r) := by
  have bandR := (cofactor_data hr).1
  have rpos : 0 < (r:ℝ) := Nat.cast_pos.mpr ((Nat.zero_le _).trans_lt (mem_Ioc.mp bandR).1)
  obtain ⟨l,h,_⟩ := factors r
  have u := z_bounds (by omega : 0 < n) (in_shell hn bandR l)
  have v := z_bounds (by omega : 0 < n) (in_shell hn bandR h)
  change 9/8 ≤ zAt n (leftIndex r) ∧ zAt n (leftIndex r) ≤ 5/4 at u
  change 9/8 ≤ zAt n (rightIndex r) ∧ zAt n (rightIndex r) ≤ 5/4 at v
  have sep : 1/200 ≤ zAt n (leftIndex r)-zAt n (rightIndex r) := by
    rcases cases_factor r with ⟨a,b⟩|⟨a,b⟩
    all_goals
      simp only [leftIndex,rightIndex,a,b] at u v ⊢
    · have eqn : 389*zAt n (389*r)=391*zAt n (391*r) := by
        unfold zAt; push_cast; field_simp
      linarith only [eqn,v.1]
    · have eqn : 391*zAt n (391*r)=397*zAt n (397*r) := by
        unfold zAt; push_cast; field_simp
      linarith only [eqn,v.1]
  have rise := weight_rise v.1 (by linarith only [sep]) u.2
  obtain ⟨lsgn,rsgn⟩ := mobius_pair_signs hr
  rw [term_eq,term_eq,lsgn,rsgn]
  norm_num only [Int.cast_one,Int.cast_neg,one_mul,neg_mul,neg_neg]
  exact ⟨weight_lower v.1 v.2,by linarith only [rise,sep]⟩

/-- Keeping all three lanes reduces their signed total to one Möbius
value at the cofactor. The coefficient stays positive. -/
def tripleWeight (n r : ℕ) := weight (zAt n (389*r))-weight (zAt n (391*r))+weight (zAt n (397*r))

theorem triple_identity {n r : ℕ} (hn : 100000 ≤ n) (hr : r ∈ cofactors n) :
    1/5 ≤ tripleWeight n r ∧
    term n (389*r)+term n (391*r)+term n (397*r) = -(μ r:ℝ)*tripleWeight n r := by
  have theBand := (cofactor_data hr).1
  have rp : 0 < (r:ℝ) := Nat.cast_pos.mpr ((Nat.zero_le _).trans_lt (mem_Ioc.mp theBand).1)
  have a := z_bounds (by omega : 0 < n) (in_shell hn theBand (by decide : 389 ∈ ({389,391,397}:Finset ℕ)))
  have b := z_bounds (by omega : 0 < n) (in_shell hn theBand (by decide : 391 ∈ ({389,391,397}:Finset ℕ)))
  have c := z_bounds (by omega : 0 < n) (in_shell hn theBand (by decide : 397 ∈ ({389,391,397}:Finset ℕ)))
  have ab : 389*zAt n (389*r)=391*zAt n (391*r) := by unfold zAt; push_cast; field_simp
  have order : zAt n (391*r) ≤ zAt n (389*r) := by linarith only [ab,b.1]
  obtain ⟨s₁,s₂,s₃⟩ := three_signs hr
  constructor
  · unfold tripleWeight
    linarith only [weight_rise b.1 order a.2,order,weight_lower c.1 c.2]
  · simp only [term_eq,s₁,s₂,s₃,Int.cast_neg,tripleWeight]
    ring

def pair (r : ℕ) : Finset ℕ := {leftIndex r,rightIndex r}
def selected (n : ℕ) := (cofactors n).biUnion pair
def credit (n : ℕ) : ℝ := ∑ r ∈ cofactors n, (term n (leftIndex r)+term n (rightIndex r))
def paid (n : ℕ) : ℝ := ∑ r ∈ cofactors n, -term n (rightIndex r)
def rest (n : ℕ) : ℝ := ∑ d ∈ late n \ selected n, term n d

private theorem recover_cofactor {n r s i j : ℕ} (hr : r ∈ band n) (hs : s ∈ band n)
    (hi : i ∈ ({389,391,397}:Finset ℕ)) (hj : j ∈ ({389,391,397}:Finset ℕ))
    (eqn : i*r=j*s) : r=s := by
  rcases lt_trichotomy i j with lt|e|lt
  · exact False.elim ((different_lanes hr hs hi hj lt).ne eqn)
  · subst j
    have pos : 0 < i := by simp only [mem_insert,mem_singleton] at hi; omega
    exact Nat.eq_of_mul_eq_mul_left pos eqn
  · exact False.elim ((different_lanes hs hr hj hi lt).ne eqn.symm)

theorem disjoint_pairs (n : ℕ) : (cofactors n : Set ℕ).PairwiseDisjoint pair := by
  intro r hr s hs ne
  apply disjoint_left.mpr
  intro d dr ds
  have rB := (cofactor_data hr).1
  have sB := (cofactor_data hs).1
  obtain ⟨rl,rr,_⟩ := factors r
  obtain ⟨sl,sr,_⟩ := factors s
  simp only [pair,mem_insert,mem_singleton,leftIndex,rightIndex] at dr ds
  rcases dr with er|er <;> rcases ds with es|es
  · exact ne (recover_cofactor rB sB rl sl (er.symm.trans es))
  · exact ne (recover_cofactor rB sB rl sr (er.symm.trans es))
  · exact ne (recover_cofactor rB sB rr sl (er.symm.trans es))
  · exact ne (recover_cofactor rB sB rr sr (er.symm.trans es))

theorem selected_inside {n : ℕ} (hn : 100000 ≤ n) : selected n ⊆ late n := by
  intro d hd
  obtain ⟨r,hr,atR⟩ := mem_biUnion.mp hd
  have rB := (cofactor_data hr).1
  simp only [pair,mem_insert,mem_singleton] at atR
  rcases atR with rfl|rfl
  · exact in_late hn (quarter_cut hn) (in_shell hn rB (factors r).1)
  · exact in_late hn (quarter_cut hn) (in_shell hn rB (factors r).2.1)

theorem selected_sum (n : ℕ) : ∑ d ∈ selected n, term n d = credit n := by
  unfold selected credit
  rw [sum_biUnion (disjoint_pairs n)]
  apply sum_congr rfl
  intro r hr
  have p : 0 < r := (Nat.zero_le _).trans_lt (mem_Ioc.mp (cofactor_data hr).1).1
  have lt : leftIndex r < rightIndex r := Nat.mul_lt_mul_of_pos_right (factors r).2.2 p
  simp [pair,lt.ne]

theorem decompose {n : ℕ} (hn : 100000 ≤ n) :
    core n = credit n+rest n := by
  rw [←selected_sum,add_comm]
  exact (sum_sdiff (selected_inside hn)).symm

theorem covered_weight {n : ℕ} (hn : 100000 ≤ n) :
    (n:ℝ)^4/20000000 ≤ paid n ∧ (n:ℝ)^4/1600000000 ≤ credit n := by
  have many := many_cofactors hn
  have p := sum_le_sum (s:=cofactors n) (fun r hr => (pair_credit hn hr).1)
  have c := sum_le_sum (s:=cofactors n) (fun r hr => (pair_credit hn hr).2)
  change _ ≤ paid n at p
  change _ ≤ credit n at c
  simp only [sum_const,nsmul_eq_mul] at p c
  constructor <;> linarith only [many,p,c]

end RiemannReduction.ShortTail.SignPairs
