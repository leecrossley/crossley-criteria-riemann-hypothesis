import UniformShellCriterion

noncomputable section
namespace RiemannReduction.ShortTail.LossFrequency

open Finset Real ArithmeticFunction RiemannReduction.ThirdBridge
open scoped ArithmeticFunction.Moebius

/-- The larger coordinate after dividing an ordered divisor pair by its gcd. -/
def reducedPairHeight (d e : ℕ) : ℕ := max (d / d.gcd e) (e / d.gcd e)

/-- Ordered pairs whose primitive ray has height at most R. -/
def largeGcdPairs (s : Finset ℕ) (R : ℕ) : Finset (ℕ × ℕ) :=
  (s ×ˢ s).filter fun p => reducedPairHeight p.1 p.2 ≤ R

/-- The common multiplier contributes its squared Möbius value on a permitted ray.
A common prime with either reduced coordinate makes the product vanish. -/
theorem moebius_pair_common_multiplier (g a b : ℕ) :
    μ (g*a)*μ (g*b) =
      if g.Coprime a ∧ g.Coprime b then (μ g)^2 * μ a * μ b else 0 := by
  by_cases ca : g.Coprime a
  · by_cases cb : g.Coprime b
    · rw [if_pos ⟨ca,cb⟩,isMultiplicative_moebius.map_mul_of_coprime ca,
          isMultiplicative_moebius.map_mul_of_coprime cb]
      ring
    · rw [if_neg (fun h => cb h.2),moebius_eq_zero_of_not_squarefree
          (fun h => cb (Nat.coprime_of_squarefree_mul h)),mul_zero]
  · rw [if_neg (fun h => ca h.1),moebius_eq_zero_of_not_squarefree
          (fun h => ca (Nat.coprime_of_squarefree_mul h)),zero_mul]

/-- Exact weighted sum along a ray. The only Möbius factor left in the common
multiplier is nonnegative, even when the interval and kernel weights vary with g. -/
theorem weighted_moebius_ray (a b : ℕ) (G : Finset ℕ) (w : ℕ → ℝ) :
    (∑ g ∈ G, (μ (g*a):ℝ)*(μ (g*b):ℝ)*w g) =
      (μ a:ℝ)*(μ b:ℝ)*∑ g ∈ G.filter (fun g => g.Coprime a ∧ g.Coprime b), (μ g:ℝ)^2*w g := by
  classical
  rw [mul_sum,sum_filter]
  apply sum_congr rfl
  intro g _
  have ray := moebius_pair_common_multiplier g a b
  by_cases good : g.Coprime a ∧ g.Coprime b
  · rw [if_pos good] at ray ⊢
    have r : (μ (g*a):ℝ)*(μ (g*b):ℝ)=(μ g:ℝ)^2*(μ a:ℝ)*(μ b:ℝ) := by exact_mod_cast ray
    rw [r]
    ring
  · rw [if_neg good] at ray ⊢
    have r : (μ (g*a):ℝ)*(μ (g*b):ℝ)=0 := by exact_mod_cast ray
    rw [r,zero_mul]

private def orientedRays (U R : ℕ) : Finset (ℕ × ℕ) :=
  (Ioc 0 R).biUnion fun a =>
    ((Ioc 0 (U/a)) ×ˢ (Ioc 0 a)).image fun p => (p.1*a,p.1*p.2)

private theorem belongs_to_ray {d e U R : ℕ} (ep : 0 < e) (ord : e ≤ d)
    (hi : d ≤ U) (cap : d/d.gcd e ≤ R) : (d,e) ∈ orientedRays U R := by
  let g := d.gcd e
  let a := d/g
  let b := e/g
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ (ep.trans_le ord)
  have ap : 0<a := Nat.div_pos (Nat.le_of_dvd (ep.trans_le ord) (Nat.gcd_dvd_left ..)) gp
  have bp : 0<b := Nat.div_pos (Nat.le_of_dvd ep (Nat.gcd_dvd_right ..)) gp
  have da : g*a=d := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have eb : g*b=e := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  refine mem_biUnion.mpr ⟨a,mem_Ioc.mpr ⟨ap,cap⟩,mem_image.mpr ⟨(g,b),?_,?_⟩⟩
  · exact mem_product.mpr ⟨mem_Ioc.mpr ⟨gp,(Nat.le_div_iff_mul_le ap).mpr (da.le.trans hi)⟩,
      mem_Ioc.mpr ⟨bp,Nat.div_le_div_right ord⟩⟩
  · exact Prod.ext da eb

private theorem oriented_ray_count (U R : ℕ) : (orientedRays U R).card ≤ R*U := by
  unfold orientedRays
  refine card_biUnion_le.trans ?_
  calc
    _ ≤ ∑ _a ∈ Ioc 0 R, U := by
      apply sum_le_sum
      intro a _
      exact card_image_le.trans (by simpa [card_product] using Nat.div_mul_le_self U a)
    _ = R*U := by simp

/-- Each possible larger primitive coordinate a uses at most a*floor(U/a)
ordered pairs in each orientation. The estimate is uniform in the set s. -/
theorem large_gcd_pair_count {s : Finset ℕ} {U : ℕ}
    (rows : ∀ d ∈ s, 0<d ∧ d≤U) (R : ℕ) : (largeGcdPairs s R).card ≤ 2*R*U := by
  let A := orientedRays U R
  have inside : largeGcdPairs s R ⊆ A ∪ A.image Prod.swap := by
    rintro ⟨d,e⟩ h
    obtain ⟨pair,cap⟩ := mem_filter.mp h
    obtain ⟨hd,he⟩ := mem_product.mp pair
    have bounds := max_le_iff.mp cap
    by_cases ord : e≤d
    · exact mem_union_left _ (belongs_to_ray (rows e he).1 ord (rows d hd).2 bounds.1)
    · apply mem_union_right
      refine mem_image.mpr ⟨(e,d),belongs_to_ray (rows d hd).1 (le_of_not_ge ord) (rows e he).2 ?_,rfl⟩
      simpa [Nat.gcd_comm] using bounds.2
  have one : A.card ≤ R*U := oriented_ray_count U R
  have both := (card_le_card inside).trans (card_union_le A (A.image Prod.swap))
  have other : (A.image Prod.swap).card ≤ R*U := card_image_le.trans one
  calc
    _ ≤ A.card+(A.image Prod.swap).card := both
    _ ≤ R*U+R*U := Nat.add_le_add one other
    _ = _ := by ring

def fullGcdShellRows (n j : ℕ) : Finset ℕ :=
  Ioc (n^4/2^(j+1)) (n^4/2^j)

def fullGcdShellTerm (n d : ℕ) : ℝ := (μ d:ℝ)*surviving ((n:ℝ)^4/d)

def largeGcdShellContribution (n j R : ℕ) : ℝ :=
  ∑ p ∈ largeGcdPairs (fullGcdShellRows n j) R,
    fullGcdShellTerm n p.1 * fullGcdShellTerm n p.2

def smallGcdShellContribution (n j R : ℕ) : ℝ :=
  ∑ p ∈ ((fullGcdShellRows n j) ×ˢ (fullGcdShellRows n j)).filter
    (fun p => ¬reducedPairHeight p.1 p.2 ≤ R),
    fullGcdShellTerm n p.1 * fullGcdShellTerm n p.2

/-- The two ordered-pair contributions partition the actual signed shell square. -/
theorem full_shell_gcd_square (n j R : ℕ) :
    (fullFirstShell n j)^2 =
      largeGcdShellContribution n j R + smallGcdShellContribution n j R := by
  let s := fullGcdShellRows n j
  change (∑ d ∈ s,fullGcdShellTerm n d)^2 = _
  unfold largeGcdShellContribution smallGcdShellContribution largeGcdPairs
  rw [sum_filter_add_sum_filter_not,sum_product _ _ (fun p : ℕ×ℕ =>
    fullGcdShellTerm n p.1 * fullGcdShellTerm n p.2),pow_two,sum_mul]
  apply sum_congr rfl
  intro d _
  rw [mul_sum]

/-- Pointwise quotient decay for each actual signed divisor row. -/
theorem full_shell_term_decay {n j d : ℕ} (jp : 1≤j) (hd : d∈fullGcdShellRows n j) :
    |fullGcdShellTerm n d| ≤ kernelConstant*(1+log ((2:ℝ)^j))/(2:ℝ)^j := by
  obtain ⟨left,top⟩ := mem_Ioc.mp hd
  have dp : 0<(d:ℝ) := Nat.cast_pos.mpr ((Nat.zero_le _).trans_lt left)
  have qtwo : (2:ℝ) ≤ 2^j := by simpa using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) jp)
  have height : (2:ℝ)^j ≤ (n:ℝ)^4/d := by
    apply (le_div_iff₀ dp).mpr
    have bound := (Nat.le_div_iff_mul_le (by positivity : 0<(2:ℕ)^j)).mp top
    rw [mul_comm]
    exact_mod_cast bound
  have qpos : 0<(2:ℝ)^j := by positivity
  have dec := kernel_at_larger_quotient (one_le_pow₀ (by norm_num)) (qtwo.trans height) height
  have mu : |(μ d:ℝ)|≤1 := by exact_mod_cast abs_moebius_le_one (n:=d)
  unfold fullGcdShellTerm
  rw [abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) mu).trans ((le_div_iff₀ qpos).mpr dec)

/-- Only linear size in R times the upper divisor endpoint remains after taking
absolute values on these rays. The two kernel factors retain their full quotient decay. -/
theorem large_gcd_shell_bound (n j R : ℕ) (jp : 1 ≤ j) :
    |largeGcdShellContribution n j R| ≤
      (2*(R:ℝ)*(n^4/2^j:ℕ)) * (kernelConstant*(1+log ((2:ℝ)^j))/(2:ℝ)^j)^2 := by
  let s := fullGcdShellRows n j
  let K := kernelConstant*(1+log ((2:ℝ)^j))/(2:ℝ)^j
  have rows (d : ℕ) (hd : d∈s) : 0<d ∧ d≤n^4/2^j :=
    ⟨(Nat.zero_le _).trans_lt (mem_Ioc.mp hd).1,(mem_Ioc.mp hd).2⟩
  have count : ((largeGcdPairs s R).card:ℝ) ≤ 2*(R:ℝ)*(n^4/2^j:ℕ) := by
    exact_mod_cast large_gcd_pair_count rows R
  have bound (d : ℕ) (hd : d∈s) : |fullGcdShellTerm n d|≤K := full_shell_term_decay jp hd
  calc
    _ ≤ ∑ p ∈ largeGcdPairs s R, |fullGcdShellTerm n p.1 * fullGcdShellTerm n p.2| :=
      abs_sum_le_sum_abs ..
    _ ≤ ∑ _p ∈ largeGcdPairs s R, K^2 := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hd,he⟩ := mem_product.mp (mem_filter.mp hp).1
      rw [abs_mul,pow_two]
      exact mul_le_mul (bound p.1 hd) (bound p.2 he) (abs_nonneg _) ((abs_nonneg _).trans (bound p.1 hd))
    _ = ((largeGcdPairs s R).card:ℝ)*K^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right count (sq_nonneg _)

/-- A version with just the global kernel constant, uniform in j ≥ 1. -/
theorem large_gcd_shell_bound_uniform (n j R : ℕ) (jp : 1 ≤ j) :
    |largeGcdShellContribution n j R| ≤ (2*(R:ℝ)*(n^4/2^j:ℕ))*kernelConstant^2 := by
  let Q : ℝ := 2^j
  have qp : 0 < Q := by dsimp [Q]; positivity
  have lg : 0 ≤ log Q := log_nonneg (one_le_pow₀ (by norm_num))
  have ratio : kernelConstant*(1+log Q)/Q ≤ kernelConstant := by
    apply (div_le_iff₀ qp).mpr
    exact mul_le_mul_of_nonneg_left (by linarith only [log_le_sub_one_of_pos qp]) kernelConstant_nonneg
  have pos : 0 ≤ kernelConstant*(1+log Q)/Q := by positivity [kernelConstant_nonneg]
  exact (large_gcd_shell_bound n j R jp).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ pos ratio 2) (by positivity))

private theorem shell_strict_ratio {n j d e : ℕ} (hd : d∈fullGcdShellRows n j)
    (he : e∈fullGcdShellRows n j) : d<2*e := by
  have lower := (mem_Ioc.mp he).1
  have upper := (mem_Ioc.mp hd).2
  have endpoints : n^4/2^(j+1) = (n^4/2^j)/2 := by rw [Nat.div_div_eq_div_mul,pow_succ (2:ℕ) j]
  change n^4/2^(j+1)<e at lower
  change d≤n^4/2^j at upper
  rw [endpoints] at lower
  omega

private theorem small_mu {a : ℕ} (lo : 2≤a) (hi : a≤5) : μ a≤0 := by
  have negprime (p : ℕ) (hp : p.Prime) : μ p≤0 := by rw [moebius_apply_prime hp]; decide
  have four : μ 4=0 := by
    have z := moebius_apply_prime_pow Nat.prime_two (show (2:ℕ)≠0 by decide)
    norm_num at z
    exact z
  interval_cases a
  · exact negprime _ (by decide)
  · exact negprime _ (by decide)
  · exact four.le
  · exact negprime _ (by decide)

/-- In a strict dyadic shell, no primitive ray of height at most five has
opposite Möbius signs. This statement concerns signs before the kernel weights. -/
theorem dyadic_pair_moebius_nonneg_through_five {n j d e : ℕ} (hd : d∈fullGcdShellRows n j)
    (he : e∈fullGcdShellRows n j) (cap : reducedPairHeight d e≤5) : 0 ≤ μ d*μ e := by
  let g := d.gcd e
  let a := d/g
  let b := e/g
  have da : g*a=d := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have eb : g*b=e := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ ((Nat.zero_le _).trans_lt (mem_Ioc.mp hd).1)
  have ap : 0<a := Nat.div_pos
    (Nat.le_of_dvd ((Nat.zero_le _).trans_lt (mem_Ioc.mp hd).1) (Nat.gcd_dvd_left ..)) gp
  have bp : 0<b := Nat.div_pos
    (Nat.le_of_dvd ((Nat.zero_le _).trans_lt (mem_Ioc.mp he).1) (Nat.gcd_dvd_right ..)) gp
  have ab : a<2*b := by
    apply Nat.lt_of_mul_lt_mul_left (a:=g)
    calc
      g*a = d := da
      _ < 2*e := shell_strict_ratio hd he
      _ = g*(2*b) := by rw [←eb]; ring
  have ba : b<2*a := by
    apply Nat.lt_of_mul_lt_mul_left (a:=g)
    calc
      g*b = e := eb
      _ < 2*d := shell_strict_ratio he hd
      _ = g*(2*a) := by rw [←da]; ring
  have reduced : 0 ≤ μ a * μ b := by
    by_cases one : a=1
    · have other : b=1 := by omega
      rw [one,other,moebius_apply_one]
      decide
    · have large : 2≤a := by omega
      have other : 2≤b := by omega
      exact mul_nonneg_of_nonpos_of_nonpos (small_mu large (max_le_iff.mp cap).1)
        (small_mu other (max_le_iff.mp cap).2)
  calc
    0 ≤ (if g.Coprime a ∧ g.Coprime b then (μ g)^2*μ a*μ b else 0) := by
      split
      · rw [mul_assoc]
        exact mul_nonneg (sq_nonneg _) reduced
      · exact le_rfl
    _ = μ (g*a)*μ (g*b) := (moebius_pair_common_multiplier ..).symm
    _ = μ d*μ e := by rw [da,eb]

/-- The n=2, j=1 shell contains the ratio 5:6. Its reduced height is six
and its Möbius signs are opposite. -/
theorem first_negative_moebius_ray :
    5∈fullGcdShellRows 2 1 ∧ 6∈fullGcdShellRows 2 1 ∧ reducedPairHeight 5 6=6 ∧ μ 5*μ 6 = -1 := by
  refine ⟨by decide,by decide,by decide,?_⟩
  rw [moebius_apply_prime (by decide : Nat.Prime 5),show (6:ℕ)=2*3 by decide,
    isMultiplicative_moebius.map_mul_of_coprime (by decide : Nat.Coprime 2 3),
    moebius_apply_prime Nat.prime_two,moebius_apply_prime (by decide : Nat.Prime 3)]
  norm_num

end RiemannReduction.ShortTail.LossFrequency
