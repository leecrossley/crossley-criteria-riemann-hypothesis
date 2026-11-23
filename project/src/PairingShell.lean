import ShortTailLoss

/-! A positive increasing part of Sanftenberg's corrected kernel, and
a squarefree sieve for a family of disjoint cofactor pairs in that band. -/

noncomputable section
namespace RiemannReduction.ShortTail.SignPairs
open Finset Filter Real RiemannGaussian.AlpogeMined
open scoped ArithmeticFunction.Moebius

def weight (z : ℝ) := fixedBandCenteredKernel (2*z)-fixedBandFirstCorrection (2*z)

theorem weight_lower {z : ℝ} (lo : 9/8 ≤ z) (hi : z ≤ 5/4) : 1/5 ≤ weight z :=
  fixedBandHalfKernel_second_lower lo hi

/-- The rise of the corrected kernel is uniform over this part of its second quotient band. -/
theorem weight_rise {x y : ℝ} (lo : 9/8 ≤ x) (xy : x ≤ y) (hi : y ≤ 5/4) :
    (y-x)/2 ≤ weight y-weight x := by
  have x1 : 1 ≤ x := by linarith
  have xp : 0 < x := by linarith
  have yp : 0 < y := xp.trans_le xy
  have loglo := log_le_log xp xy
  have logx := log_le_sub_one_of_pos xp
  have quotient := log_le_sub_one_of_pos (div_pos yp xp)
  rw [log_div yp.ne' xp.ne'] at quotient
  have ratio : y/x-1 ≤ y-x := by
    rw [sub_le_iff_le_add,div_le_iff₀ xp]
    nlinarith only [mul_nonneg (sub_nonneg.mpr xy) (sub_nonneg.mpr x1)]
  let A := 2*(1-eulerMascheroniConstant)+4*log 2+1
  have logtwo := one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at logtwo
  have coeff : 5/2 ≤ A-4*log x := by
    dsimp [A]
    linarith [eulerMascheroniConstant_lt_two_thirds]
  have h₁ := mul_le_mul_of_nonneg_right coeff (sub_nonneg.mpr xy)
  have h₂ := mul_nonneg (show 0 ≤ 5-4*y by linarith) (sub_nonneg.mpr loglo)
  unfold weight
  rw [fixedBandHalfKernel_second (x1.trans xy) (by linarith),
    fixedBandHalfKernel_second x1 (by linarith)]
  change (y-x)/2 ≤ ((y-1)*A+(3-4*y)*log y)-((x-1)*A+(3-4*x)*log x)
  nlinarith only [h₁,h₂,quotient.trans ratio]

def scale (n : ℕ) := n^4/190000
def band (n : ℕ) := Ioc (200*scale n) (200*scale n+scale n)
def avoid (q : ℕ) (S : Finset ℕ) := S.filter (fun r => ¬q ∣ r)
def cofactors (n : ℕ) :=
  avoid 397 (avoid 389 (avoid 23 (avoid 17 ((band n).filter Squarefree))))

theorem cofactor_data {n r : ℕ} (hr : r ∈ cofactors n) :
    r ∈ band n ∧ Squarefree r ∧ ¬17 ∣ r ∧ ¬23 ∣ r ∧ ¬389 ∣ r ∧ ¬397 ∣ r := by
  simpa only [cofactors,avoid,mem_filter,and_assoc] using hr

/- Refer to the original proofs of the two private sieve inequalities from
the pinned, replayed module. Lean verifies the types and bodies of the aliases. -/
open Lean Elab Command in
run_cmd do
  for short in [`squarefree_interval_lower,`multiples_in_interval] do
    let source := ((`_private ++ `CheckAlpogeFixedPrimeBandFirstQuotient).num 0) ++
      `RiemannGaussian.AlpogeMined ++ short
    let c ← getConstInfo source
    liftTermElabM <| addDecl <| .thmDecl {
      name := `RiemannReduction.ShortTail.SignPairs ++ short, levelParams := c.levelParams,
      type := c.type, value := mkConst source (c.levelParams.map Level.param) }

private theorem avoid_cost {n q : ℕ} (hq : 0 < q) {S : Finset ℕ} (sub : S ⊆ band n) :
    (S.card:ℝ)-((scale n:ℝ)/q+1) ≤ ((avoid q S).card:ℝ) := by
  have cap := multiples_in_interval (200*scale n) (scale n) q hq
  have small : S.filter (fun k => q ∣ k) ⊆ (band n).filter (fun k => q ∣ k) :=
    fun _ hk => mem_filter.mpr ⟨sub (mem_filter.mp hk).1,(mem_filter.mp hk).2⟩
  have le : ((S.filter (fun k => q ∣ k)).card:ℝ) ≤ (scale n:ℝ)/q+1 :=
    (Nat.cast_le.mpr (card_le_card small)).trans cap
  have h := congrArg (Nat.cast (R:=ℝ)) (card_filter_add_card_filter_not (s:=S) (fun k => q ∣ k))
  push_cast at h
  change _ ≤ ((S.filter (fun k => ¬q ∣ k)).card:ℝ)
  linarith

theorem scale_bounds (n : ℕ) : scale n*190000 ≤ n^4 ∧ n^4 < scale n*190000+190000 :=
  ⟨Nat.div_mul_le_self _ _,Nat.lt_div_mul_add (by decide)⟩

theorem scale_large {n : ℕ} (hn : 100000 ≤ n) : 100*(n^2+4) ≤ scale n := by
  have s := scale_bounds n
  have n2 : 100000000 ≤ n^2 :=
    (by decide : 100000000 ≤ 100000^2).trans (Nat.pow_le_pow_left hn 2)
  have grow : 100000000*n^2 ≤ n^4 :=
    (Nat.mul_le_mul_right (n^2) n2).trans_eq (by ring)
  omega

/-- A fixed positive density of the cofactors in this narrow band works for either sign. -/
theorem many_cofactors {n : ℕ} (hn : 100000 ≤ n) :
    (n:ℝ)^4/4000000 ≤ ((cofactors n).card:ℝ) := by
  let S := (band n).filter Squarefree
  have b₀ : S ⊆ band n := filter_subset _ _
  have b₁ := (filter_subset (fun r => ¬17 ∣ r) S).trans b₀
  have b₂ := (filter_subset (fun r => ¬23 ∣ r) (avoid 17 S)).trans b₁
  have b₃ := (filter_subset (fun r => ¬389 ∣ r) (avoid 23 (avoid 17 S))).trans b₂
  have s := scale_bounds n
  have large := scale_large hn
  have hN : 200*scale n+scale n ≤ (n^2)^2 := by rw [←pow_mul]; change _ ≤ n^4; omega
  have base := squarefree_interval_lower (200*scale n) (scale n) (n^2)
    (by have := Nat.pow_le_pow_left hn 2; omega) hN
  change (scale n:ℝ)/4-((n^2:ℕ):ℝ) ≤ (S.card:ℝ) at base
  have c₁ := avoid_cost (q:=17) (by decide) b₀
  have c₂ := avoid_cost (q:=23) (by decide) b₁
  have c₃ := avoid_cost (q:=389) (by decide) b₂
  have c₄ := avoid_cost (q:=397) (by decide) b₃
  have grow : 100*((n:ℝ)^2+4) ≤ (scale n:ℝ) := by exact_mod_cast large
  have cap : (n:ℝ)^4 < (scale n:ℝ)*190000+190000 := by exact_mod_cast s.2
  rw [Nat.cast_pow] at base
  change _ ≤ ((avoid 397 (avoid 389 (avoid 23 (avoid 17 S)))).card:ℝ)
  change _ ≤ ((avoid 23 (avoid 17 S)).card:ℝ) at c₂
  change _ ≤ ((avoid 389 (avoid 23 (avoid 17 S))).card:ℝ) at c₃
  change _ ≤ ((avoid 397 (avoid 389 (avoid 23 (avoid 17 S)))).card:ℝ) at c₄
  dsimp only [avoid] at c₁ c₂ c₃ c₄ ⊢
  norm_num only [Nat.cast_ofNat] at c₁ c₂ c₃ c₄
  linarith only [base,c₁,c₂,c₃,c₄,cap,grow,sq_nonneg (n:ℝ)]

/-- The three images occupy disjoint index intervals, in ascending order. -/
theorem different_lanes {n i j r s : ℕ} (hr : r ∈ band n) (hs : s ∈ band n)
    (hi : i ∈ ({389,391,397}:Finset ℕ)) (hj : j ∈ ({389,391,397}:Finset ℕ)) (lt : i < j) :
    i*r < j*s := by
  obtain ⟨hr1,hr2⟩ := mem_Ioc.mp hr
  obtain ⟨hs1,hs2⟩ := mem_Ioc.mp hs
  simp only [mem_insert,mem_singleton] at hi hj
  rcases hi with rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl <;> omega

theorem quarter_cut {n : ℕ} (hn : 100000 ≤ n) : 4*cutoff n ≤ n^4 := by
  have nr : (100000:ℝ) ≤ n := by exact_mod_cast hn
  have np : 0 < (n:ℝ) := by linarith
  have lg := log_le_log (by norm_num : (0:ℝ) < 2^8) (show (2:ℝ)^8 ≤ n by norm_num; linarith)
  rw [log_pow] at lg
  have l4 : 4 ≤ log (n:ℝ) := by norm_num at lg; linarith [log_two_gt_d9]
  have rt : sqrt (log n) ≤ log n/2 := sqrt_le_iff.mpr ⟨by linarith,
    by nlinarith only [mul_nonneg (log_natCast_nonneg n) (sub_nonneg.mpr l4)]⟩
  have sq : sqrt (n:ℝ) ≤ (n:ℝ)/4 := sqrt_le_iff.mpr ⟨by positivity,
    by nlinarith only [mul_nonneg np.le (show 0 ≤ (n:ℝ)-16 by linarith)]⟩
  have ex := exp_le_exp.mpr rt
  rw [exp_half,exp_log np] at ex
  have floor := Nat.floor_le (show 0 ≤ (n:ℝ)^3*exp (sqrt (log n)) by positivity)
  change (cutoff n:ℝ) ≤ _ at floor
  have simpCap : 4*exp (sqrt (log n)) ≤ (n:ℝ) := by linarith
  exact_mod_cast (show 4*(cutoff n:ℝ) ≤ (n:ℝ)^4 by
    nlinarith only [floor,mul_le_mul_of_nonneg_left simpCap (show 0 ≤ (n:ℝ)^3 by positivity)])

theorem in_shell {n r i : ℕ} (hn : 100000 ≤ n) (hr : r ∈ band n)
    (hi : i ∈ ({389,391,397}:Finset ℕ)) :
    2*n^4 ≤ 5*(i*r) ∧ 9*(i*r) ≤ 4*n^4 := by
  have bounds := scale_bounds n
  have big := scale_large hn
  have l := mem_Ioc.mp hr
  simp only [mem_insert,mem_singleton] at hi
  rcases hi with rfl|rfl|rfl <;> omega

theorem in_late {n d : ℕ} (hn : 100000 ≤ n) (cut : 4*cutoff n ≤ n^4)
    (h : 2*n^4 ≤ 5*d ∧ 9*d ≤ 4*n^4) : d ∈ late n := by
  have k : fixedBandMultipleCutoff n ≤ n^3 := Nat.div_le_self ..
  have hi : 4*n^3 ≤ n^4 := (Nat.mul_le_mul_right (n^3) (show 4 ≤ n by omega)).trans_eq (by ring)
  have p : 0 < n^4 := pow_pos (by omega) _
  apply mem_filter.mpr
  exact ⟨mem_Ioc.mpr ⟨by omega,by omega⟩,by omega⟩

def zAt (n d : ℕ) := ((n^4:ℕ):ℝ)/d/2

theorem z_bounds {n d : ℕ} (hn : 0 < n) (h : 2*n^4 ≤ 5*d ∧ 9*d ≤ 4*n^4) :
    9/8 ≤ zAt n d ∧ zAt n d ≤ 5/4 := by
  have p := pow_pos hn 4
  have dp : 0 < (d:ℝ) := Nat.cast_pos.mpr (by omega)
  have a : 2*((n^4:ℕ):ℝ) ≤ 5*d := by exact_mod_cast h.1
  have b : 9*(d:ℝ) ≤ 4*((n^4:ℕ):ℝ) := by exact_mod_cast h.2
  unfold zAt
  constructor
  · rw [le_div_iff₀ (by norm_num),le_div_iff₀ dp]; linarith
  · rw [div_le_iff₀ (by norm_num),div_le_iff₀ dp]; linarith

theorem term_eq (n d : ℕ) : term n d = (μ d:ℝ)*weight (zAt n d) := by
  unfold term weight zAt
  rw [show 2*(((n^4:ℕ):ℝ)/d/2)=((n^4:ℕ):ℝ)/d by ring]

end RiemannReduction.ShortTail.SignPairs
