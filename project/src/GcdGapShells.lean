import LargeGcdShells
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.Dist

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency

open Finset Real RiemannReduction.ThirdBridge

/-- Absolute difference of the two primitive coordinates of an ordered pair. -/
def reducedPairGap (d e : ℕ) : ℕ := Nat.dist (d/d.gcd e) (e/d.gcd e)

def closeGapPairs (s : Finset ℕ) (R : ℕ) : Finset (ℕ × ℕ) :=
  (s ×ˢ s).filter fun p => reducedPairGap p.1 p.2 ≤ R

theorem reduced_gap_le_height (d e : ℕ) : reducedPairGap d e ≤ reducedPairHeight d e := by
  unfold reducedPairGap reducedPairHeight
  rw [Nat.dist_eq_max_sub_min]
  apply Nat.sub_le

theorem distance_eq_gcd_mul_gap (d e : ℕ) : Nat.dist d e=d.gcd e*reducedPairGap d e := by
  unfold reducedPairGap
  rw [←Nat.dist_mul_left,Nat.mul_div_cancel' (Nat.gcd_dvd_left ..),
    Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)]

theorem far_reduced_gap_iff {d e R : ℕ} (hd : 0<d) :
    R<reducedPairGap d e ↔ d.gcd e*R<Nat.dist d e := by
  rw [distance_eq_gcd_mul_gap,Nat.mul_lt_mul_left (Nat.gcd_pos_of_pos_left _ hd)]

theorem large_gcd_pairs_subset_close_gap (s : Finset ℕ) (R : ℕ) :
    largeGcdPairs s R ⊆ closeGapPairs s R := by
  intro p hp
  obtain ⟨rows,ht⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨rows,(reduced_gap_le_height ..).trans ht⟩

/-- An upper cover for the off-diagonal, with g as outer variable. A pair
with upper primitive coordinate a and positive gap k gives (ga,g(a-k)). -/
private def orientedGaps (U R : ℕ) : Finset (ℕ × ℕ) :=
  (Ioc 0 U).biUnion fun g =>
    ((Ioc 0 (U/g)) ×ˢ (Ioc 0 R)).image fun p => (g*p.1,g*(p.1-p.2))

private theorem belongs_to_gap {d e U R : ℕ} (ep : 0<e) (ord : e<d) (top : d≤U)
    (cap : reducedPairGap d e≤R) : (d,e)∈orientedGaps U R := by
  let g := d.gcd e
  let a := d/g
  let b := e/g
  have dp := ep.trans ord
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ dp
  have gu : g≤U := (Nat.le_of_dvd dp (Nat.gcd_dvd_left ..)).trans top
  have da : g*a=d := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have eb : g*b=e := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have ba : b<a := Nat.lt_of_mul_lt_mul_left (show g*b<g*a by rwa [eb,da])
  have dk : Nat.dist a b=a-b := Nat.dist_eq_sub_of_le_right ba.le
  change Nat.dist a b≤R at cap
  rw [dk] at cap
  have acap : a≤U/g := (Nat.le_div_iff_mul_le gp).mpr (by rw [Nat.mul_comm,da]; exact top)
  refine mem_biUnion.mpr ⟨g,mem_Ioc.mpr ⟨gp,gu⟩,mem_image.mpr ⟨(a,a-b),?_,?_⟩⟩
  · exact mem_product.mpr ⟨mem_Ioc.mpr ⟨(Nat.zero_le _).trans_lt ba,acap⟩,
      mem_Ioc.mpr ⟨Nat.sub_pos_of_lt ba,cap⟩⟩
  · change (g*a,g*(a-(a-b)))=(d,e)
    rw [Nat.sub_sub_self ba.le,da,eb]

private theorem oriented_gap_count (U R : ℕ) :
    (orientedGaps U R).card ≤ (∑ g ∈ Ioc 0 U,U/g)*R := by
  unfold orientedGaps
  refine card_biUnion_le.trans ?_
  rw [sum_mul]
  apply sum_le_sum
  intro g _
  exact card_image_le.trans (by simp [card_product])

/-- Count the diagonal once. Each nonzero gap contributes two orientations
and at most floor(U/g) possible upper primitive coordinates for each g. -/
theorem reduced_gap_pair_count_nat {s : Finset ℕ} {U : ℕ}
    (rows : ∀ d∈s, 0<d ∧ d≤U) (R : ℕ) :
    (closeGapPairs s R).card ≤ U+2*R*(∑ g ∈ Ioc 0 U,U/g) := by
  let A := orientedGaps U R
  have inside : closeGapPairs s R ⊆ s.diag ∪ (A ∪ A.image Prod.swap) := by
    rintro ⟨d,e⟩ h
    obtain ⟨pair,cap⟩ := mem_filter.mp h
    obtain ⟨hd,he⟩ := mem_product.mp pair
    rcases lt_trichotomy e d with ed|eq|de
    · exact mem_union_right _ (mem_union_left _ (belongs_to_gap (rows e he).1 ed (rows d hd).2 cap))
    · exact mem_union_left _ (mem_diag.mpr ⟨hd,eq.symm⟩)
    · apply mem_union_right
      apply mem_union_right
      refine mem_image.mpr ⟨(e,d),belongs_to_gap (rows d hd).1 de (rows e he).2 ?_,rfl⟩
      simpa only [reducedPairGap,Nat.gcd_comm e d,Nat.dist_comm] using cap
  have dcard : s.diag.card ≤ U := by
    calc
      _ = s.card := by simp [diag]
      _ ≤ (Ioc 0 U).card := card_le_card (fun d hd => mem_Ioc.mpr (rows d hd))
      _ = U := by simp
  have one : A.card ≤ (∑ g ∈ Ioc 0 U,U/g)*R := oriented_gap_count U R
  have other : (A.image Prod.swap).card ≤ (∑ g ∈ Ioc 0 U,U/g)*R := card_image_le.trans one
  calc
    _ ≤ s.diag.card+(A ∪ A.image Prod.swap).card :=
      (card_le_card inside).trans (card_union_le ..)
    _ ≤ U+(A.card+(A.image Prod.swap).card) := Nat.add_le_add dcard (card_union_le ..)
    _ ≤ U+((∑ g ∈ Ioc 0 U,U/g)*R+(∑ g ∈ Ioc 0 U,U/g)*R) :=
      Nat.add_le_add_left (Nat.add_le_add one other) U
    _ = _ := by ring

private theorem divisor_sum_log (U : ℕ) :
    ((∑ g ∈ Ioc 0 U,U/g:ℕ):ℝ) ≤ (U:ℝ)*(1+log U) := by
  have sets : Ioc 0 U=Icc 1 U := by ext i; simp only [mem_Ioc,mem_Icc]; omega
  have H := harmonic_le_one_add_log U
  simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] at H
  calc
    _ = ∑ g ∈ Icc 1 U,((U/g:ℕ):ℝ) := by rw [Nat.cast_sum,sets]
    _ ≤ ∑ g ∈ Icc 1 U,(U:ℝ)*(g:ℝ)⁻¹ := by
      apply sum_le_sum
      intro g _
      simpa only [div_eq_mul_inv] using (Nat.cast_div_le : ((U/g:ℕ):ℝ) ≤ (U:ℝ)/g)
    _ = (U:ℝ)*∑ g ∈ Icc 1 U,(g:ℝ)⁻¹ := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left H (Nat.cast_nonneg _)

theorem reduced_gap_pair_count {s : Finset ℕ} {U : ℕ}
    (rows : ∀ d∈s, 0<d ∧ d≤U) (R : ℕ) :
    ((closeGapPairs s R).card:ℝ) ≤ (U:ℝ)*(1+2*(R:ℝ)*(1+log U)) := by
  have h : ((closeGapPairs s R).card:ℝ) ≤
      (U:ℝ)+2*(R:ℝ)*((∑ g ∈ Ioc 0 U,U/g:ℕ):ℝ) := by exact_mod_cast reduced_gap_pair_count_nat rows R
  have second := mul_le_mul_of_nonneg_left (divisor_sum_log U) (show (0:ℝ)≤2*(R:ℝ) by positivity)
  linarith only [h,second]

def nearGapShellContribution (n j R : ℕ) : ℝ :=
  ∑ p ∈ closeGapPairs (fullGcdShellRows n j) R,
    fullGcdShellTerm n p.1 * fullGcdShellTerm n p.2

def farGapShellContribution (n j R : ℕ) : ℝ :=
  ∑ p ∈ ((fullGcdShellRows n j) ×ˢ (fullGcdShellRows n j)).filter
    (fun p => ¬reducedPairGap p.1 p.2 ≤ R),
    fullGcdShellTerm n p.1 * fullGcdShellTerm n p.2

theorem full_shell_gap_square (n j R : ℕ) :
    (fullFirstShell n j)^2=nearGapShellContribution n j R+farGapShellContribution n j R := by
  unfold nearGapShellContribution farGapShellContribution closeGapPairs
  rw [sum_filter_add_sum_filter_not]
  rw [full_shell_gcd_square n j R]
  unfold largeGcdShellContribution smallGcdShellContribution largeGcdPairs
  rw [sum_filter_add_sum_filter_not]

/-- The count pays even the sum of absolute pair terms over all close primitive gaps. -/
theorem near_gap_absolute_bound (n j R : ℕ) (jp : 1≤j) :
    (∑ p ∈ closeGapPairs (fullGcdShellRows n j) R, |fullGcdShellTerm n p.1 * fullGcdShellTerm n p.2|) ≤
      (↑(n^4/2^j:ℕ):ℝ)*(1+2*(R:ℝ)*(1+log (n^4/2^j:ℕ))) *
      (kernelConstant*(1+log ((2:ℝ)^j))/(2:ℝ)^j)^2 := by
  let s := fullGcdShellRows n j
  let K := kernelConstant*(1+log ((2:ℝ)^j))/(2:ℝ)^j
  have rows (d : ℕ) (hd : d∈s) : 0<d ∧ d≤n^4/2^j :=
    ⟨(Nat.zero_le _).trans_lt (mem_Ioc.mp hd).1,(mem_Ioc.mp hd).2⟩
  have bound (d : ℕ) (hd : d∈s) : |fullGcdShellTerm n d|≤K := full_shell_term_decay jp hd
  calc
    _ ≤ ∑ _p ∈ closeGapPairs s R,K^2 := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hd,he⟩ := mem_product.mp (mem_filter.mp hp).1
      rw [abs_mul,pow_two]
      exact mul_le_mul (bound _ hd) (bound _ he) (abs_nonneg _) ((abs_nonneg _).trans (bound _ hd))
    _ = ((closeGapPairs s R).card:ℝ)*K^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (reduced_gap_pair_count rows R) (sq_nonneg _)

theorem near_gap_shell_bound (n j R : ℕ) (jp : 1≤j) :
    |nearGapShellContribution n j R| ≤
      (↑(n^4/2^j:ℕ):ℝ)*(1+2*(R:ℝ)*(1+log (n^4/2^j:ℕ))) *
      (kernelConstant*(1+log ((2:ℝ)^j))/(2:ℝ)^j)^2 :=
  (abs_sum_le_sum_abs ..).trans (near_gap_absolute_bound n j R jp)

theorem near_gap_shell_bound_uniform (n j R : ℕ) (jp : 1≤j) :
    |nearGapShellContribution n j R| ≤
      (↑(n^4/2^j:ℕ):ℝ)*(1+2*(R:ℝ)*(1+log (n^4/2^j:ℕ)))*kernelConstant^2 := by
  let Q : ℝ := 2^j
  have qp : 0<Q := by dsimp [Q]; positivity
  have lq : 0≤log Q := log_nonneg (one_le_pow₀ (by norm_num))
  have lu := log_natCast_nonneg (n^4/2^j)
  have ratio : kernelConstant*(1+log Q)/Q ≤ kernelConstant := by
    apply (div_le_iff₀ qp).mpr
    exact mul_le_mul_of_nonneg_left (by linarith only [log_le_sub_one_of_pos qp]) kernelConstant_nonneg
  have pos : 0 ≤ kernelConstant*(1+log Q)/Q := by positivity [kernelConstant_nonneg]
  exact (near_gap_shell_bound n j R jp).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ pos ratio 2) (by positivity))

/-- The upper divisor endpoint contributes the third power of the quotient
after both copies of the corrected kernel have supplied their decay. -/
theorem near_gap_absolute_cubic (n j R : ℕ) (jp : 1≤j) :
    (∑ p ∈ closeGapPairs (fullGcdShellRows n j) R, |fullGcdShellTerm n p.1 * fullGcdShellTerm n p.2|) *
      ((2:ℝ)^j)^3 ≤
      (n:ℝ)^4*(1+2*(R:ℝ)*(1+log (n^4/2^j:ℕ)))*(kernelConstant*(1+log ((2:ℝ)^j)))^2 := by
  let Q : ℝ := 2^j
  let U := n^4/2^j
  let L := 1+2*(R:ℝ)*(1+log U)
  let A := kernelConstant*(1+log Q)
  have qp : 0<Q := by dsimp [Q]; positivity
  have cap : (U:ℝ)*Q ≤ (n:ℝ)^4 := by
    dsimp [U,Q]
    exact_mod_cast Nat.div_mul_le_self (n^4) (2^j)
  have lp : 0≤L := by dsimp [L]; positivity [log_natCast_nonneg U]
  have raw : (∑ p ∈ closeGapPairs (fullGcdShellRows n j) R,
      |fullGcdShellTerm n p.1 * fullGcdShellTerm n p.2|) ≤ (U:ℝ)*L*(A/Q)^2 :=
    near_gap_absolute_bound n j R jp
  calc
    _ ≤ ((U:ℝ)*L*(A/Q)^2)*Q^3 := mul_le_mul_of_nonneg_right raw (pow_nonneg qp.le 3)
    _ = ((U:ℝ)*Q)*(L*A^2) := by field_simp
    _ ≤ (n:ℝ)^4*(L*A^2) := mul_le_mul_of_nonneg_right cap (mul_nonneg lp (sq_nonneg _))
    _ = _ := by dsimp [L,A,Q,U]; ring

theorem near_gap_shell_cubic (n j R : ℕ) (jp : 1≤j) :
    |nearGapShellContribution n j R| * ((2:ℝ)^j)^3 ≤
      (n:ℝ)^4*(1+2*(R:ℝ)*(1+log (n^4/2^j:ℕ)))*(kernelConstant*(1+log ((2:ℝ)^j)))^2 :=
  (mul_le_mul_of_nonneg_right (abs_sum_le_sum_abs ..) (by positivity)).trans (near_gap_absolute_cubic n j R jp)

/-- Every reduced gap is at most the lower endpoint of the original dyadic bin. -/
theorem shell_pair_gap_le_half {n j d e : ℕ} (hd : d∈fullGcdShellRows n j)
    (he : e∈fullGcdShellRows n j) : reducedPairGap d e≤n^4/2^(j+1) := by
  let U := n^4/2^j
  have endpoints : n^4/2^(j+1)=U/2 := by
    dsimp [U]
    rw [Nat.div_div_eq_div_mul,pow_succ (2:ℕ) j]
  have db : U/2<d ∧ d≤U := by simpa [fullGcdShellRows,endpoints,U] using hd
  have eb : U/2<e ∧ e≤U := by simpa [fullGcdShellRows,endpoints,U] using he
  have dg := Nat.gcd_pos_of_pos_left e ((Nat.zero_le _).trans_lt db.1)
  have raw : Nat.dist d e ≤ U/2 := by
    rcases le_total d e with ord|ord
    · rw [Nat.dist_eq_sub_of_le ord]
      omega
    · rw [Nat.dist_eq_sub_of_le_right ord]
      omega
  calc
    _ = 1*reducedPairGap d e := (one_mul _).symm
    _ ≤ d.gcd e*reducedPairGap d e := Nat.mul_le_mul_right _ dg
    _ = Nat.dist d e := (distance_eq_gcd_mul_gap ..).symm
    _ ≤ _ := raw.trans_eq endpoints.symm

theorem far_gap_shell_eq_zero_of_half_endpoint (n j R : ℕ) (cap : n^4/2^(j+1)≤R) :
    farGapShellContribution n j R=0 := by
  apply sum_eq_zero
  intro p hp
  obtain ⟨pair,apart⟩ := mem_filter.mp hp
  obtain ⟨hd,he⟩ := mem_product.mp pair
  exact (apart ((shell_pair_gap_le_half hd he).trans cap)).elim

/-- The close-gap cover adds arbitrarily high primitive rays. Every full
shell with upper endpoint U≥3 contains the consecutive pair (U-1,U). -/
theorem adjacent_shell_gap_one (n j : ℕ) (large : 3≤n^4/2^j) :
    let U := n^4/2^j
    (U-1,U) ∈ closeGapPairs (fullGcdShellRows n j) 1 ∧
      reducedPairGap (U-1) U=1 ∧ reducedPairHeight (U-1) U=U := by
  let U := n^4/2^j
  have u3 : 3≤U := large
  have top : n^4/2^(j+1)=U/2 := by
    dsimp [U]
    rw [Nat.div_div_eq_div_mul,pow_succ (2:ℕ) j]
  have gcd1 : (U-1).gcd U=1 := by
    calc
      _ = (U-1).gcd ((U-1)+1) := by congr 1; omega
      _ = 1 := by simp
  have gap : reducedPairGap (U-1) U=1 := by
    simp only [reducedPairGap,gcd1,Nat.div_one,Nat.dist]
    omega
  have height : reducedPairHeight (U-1) U=U := by
    simp [reducedPairHeight,gcd1]
  refine ⟨mem_filter.mpr ⟨mem_product.mpr ⟨?_,?_⟩,gap.le⟩,gap,height⟩
  · change _∈Ioc _ U
    rw [top,mem_Ioc]
    omega
  · change _∈Ioc _ U
    rw [top,mem_Ioc]
    omega

end RiemannReduction.ShortTail.LossFrequency
