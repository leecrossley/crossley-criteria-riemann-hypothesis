import Mathlib

noncomputable section
open Finset
namespace SparseAnchor

theorem one_Icc (m : ℕ) : Icc 1 m = Ioc 0 m := by
  ext d
  simp only [mem_Icc, mem_Ioc]
  omega

/-- The number of positive integers n with lo < n ≤ hi and n*d ≤ X. -/
private theorem rectangle_row (X d lo hi : ℕ) (hd : 0 < d) (top : X/d ≤ hi) :
    (∑ n ∈ Ioc lo hi, if n*d ≤ X then 1 else 0) = X/d-lo := by
  have sel : (Ioc lo hi).filter (fun n => n*d ≤ X) = Ioc lo (X/d) := by
    ext n
    simp only [mem_filter, mem_Ioc, Nat.le_div_iff_mul_le hd]
    constructor
    · rintro ⟨⟨h,_⟩,h'⟩
      exact ⟨h,h'⟩
    · rintro ⟨h,h'⟩
      exact ⟨⟨h, ((Nat.le_div_iff_mul_le hd).2 h').trans top⟩,h'⟩
  rw [←sum_filter, sel]
  simp

/-- Splitting the integer lattice at a factorization X=u*v makes the
overlapping rectangle contain exactly X points. -/
theorem floor_hyperbola {u v : ℕ} (hu : 0<u) (hv : 0<v) :
    (∑ d ∈ Ioc 0 (u*v), u*v/d) + u*v =
      (∑ d ∈ Ioc 0 u, u*v/d) + ∑ n ∈ Ioc 0 v, u*v/n := by
  let X := u*v
  have ux : u≤X := by dsimp [X]; simpa using Nat.mul_le_mul_left u hv
  have vx : v≤X := by dsimp [X]; simpa using Nat.mul_le_mul_right v hu
  have tail : (∑ d ∈ Ioc u X, X/d) = ∑ n ∈ Ioc 0 v, (X/n-u) := by
    calc
      _ = ∑ d ∈ Ioc u X, ∑ n ∈ Ioc 0 v, if n*d≤X then 1 else 0 := by
        refine sum_congr rfl fun d hd => ?_
        have ud := (mem_Ioc.mp hd).1
        have dp : 0<d := hu.trans ud
        have cap : X/d≤v := Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul dp).mpr (by
          dsimp [X]
          nlinarith [Nat.mul_le_mul_right v ud.le]))
        simpa only [Nat.sub_zero] using (rectangle_row X d 0 v dp cap).symm
      _ = ∑ n ∈ Ioc 0 v, ∑ d ∈ Ioc u X, if d*n≤X then 1 else 0 := by
        rw [sum_comm]
        simp only [Nat.mul_comm]
      _ = _ := sum_congr rfl fun n hn => rectangle_row X n u X (mem_Ioc.mp hn).1 (Nat.div_le_self ..)
  have addback : (∑ n ∈ Ioc 0 v, (X/n-u)) + u*v = ∑ n ∈ Ioc 0 v, X/n := by
    have size : (∑ _n ∈ Ioc 0 v, u) = u*v := by simp [Nat.mul_comm]
    rw [←size, ←sum_add_distrib]
    refine sum_congr rfl fun n hn => Nat.sub_add_cancel ?_
    exact (Nat.le_div_iff_mul_le (mem_Ioc.mp hn).1).2 (Nat.mul_le_mul_left u (mem_Ioc.mp hn).2)
  change (∑ d ∈ Ioc 0 X, X/d)+u*v = _
  rw [←sum_Ioc_consecutive (fun d => X/d) (Nat.zero_le u) ux, tail, Nat.add_assoc, addback]

/-- The fractional complement uses value one when n divides X. -/
def weight (X n : ℕ) : ℝ := 1 + ((X/n:ℕ):ℝ) - (X:ℝ)/n

theorem weight_bounds (X : ℕ) {n : ℕ} (hn : 0<n) :
    0 ≤ weight X n ∧ weight X n ≤ 1 := by
  have nr : (0:ℝ)<n := by exact_mod_cast hn
  have a : ((X/n:ℕ):ℝ)*(n:ℝ) ≤ X := by exact_mod_cast Nat.div_mul_le_self X n
  have b : (X:ℝ) < (((X/n:ℕ):ℝ)+1)*(n:ℝ) := by
    exact_mod_cast (Nat.div_lt_iff_lt_mul hn).mp (Nat.lt_succ_self (X/n))
  unfold weight
  have aa := (le_div_iff₀ nr).mpr a
  have bb := (div_lt_iff₀ nr).mpr b
  constructor <;> linarith

private theorem harmonic_floor_bounds (X m : ℕ) :
    (X:ℝ) * (harmonic m:ℝ) - m ≤ ∑ n ∈ Ioc 0 m, ((X/n:ℕ):ℝ) ∧
    (∑ n ∈ Ioc 0 m, ((X/n:ℕ):ℝ)) ≤ (X:ℝ) * (harmonic m:ℝ) := by
  have harm : (X:ℝ)*(harmonic m:ℝ) = ∑ n ∈ Ioc 0 m, (X:ℝ)/n := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum, one_Icc m, mul_sum]
    simp [div_eq_mul_inv]
  have a : (∑ n ∈ Ioc 0 m, ((X:ℝ)/n-1)) ≤ ∑ n ∈ Ioc 0 m, ((X/n:ℕ):ℝ) := by
    refine sum_le_sum fun n hn => ?_
    have h := (weight_bounds X (mem_Ioc.mp hn).1).1
    unfold weight at h
    linarith
  have b : (∑ n ∈ Ioc 0 m, ((X/n:ℕ):ℝ)) ≤ ∑ n ∈ Ioc 0 m, (X:ℝ)/n := by
    refine sum_le_sum fun n hn => ?_
    have h := (weight_bounds X (mem_Ioc.mp hn).1).2
    unfold weight at h
    linarith
  rw [sum_sub_distrib] at a
  rw [harm]
  simpa using And.intro a b

private theorem harmonic_vs_log {m : ℕ} (hm : 0 < m) :
    Real.log m + Real.eulerMascheroniConstant ≤ (harmonic m:ℝ) ∧
    (harmonic m:ℝ) ≤ Real.log m+Real.eulerMascheroniConstant+1/m := by
  have hu := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' m
  have hl := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant m
  simp only [Real.eulerMascheroniSeq', if_neg (Nat.ne_of_gt hm)] at hu
  simp only [Real.eulerMascheroniSeq] at hl
  have mr : (0:ℝ) < m := by exact_mod_cast hm
  have incr : Real.log ((m:ℝ)+1) - Real.log m ≤ 1/m := by
    rw [←Real.log_div (by positivity) mr.ne']
    apply (Real.log_le_sub_one_of_pos (by positivity)).trans
    field_simp
    linarith
  constructor <;> linarith

/-- Ordinary-density centering of the sawtooth weight at an integer product. -/
theorem weight_center {u v : ℕ} (hu : 0<u) (hv : 0<v) :
    |Real.eulerMascheroniConstant*(u*v:ℕ) - ∑ n ∈ Ioc 0 (u*v), weight (u*v) n|
      ≤ u+(v:ℝ)+1 := by
  let X := u*v
  have xp : 0<X := Nat.mul_pos hu hv
  have xr : (0:ℝ)<X := by exact_mod_cast xp
  have ur : (0:ℝ)<u := by exact_mod_cast hu
  have vr : (0:ℝ)<v := by exact_mod_cast hv
  have product : (X:ℝ)=(u:ℝ)*v := by simp [X]
  have logs : Real.log X = Real.log u + Real.log v := by rw [product, Real.log_mul ur.ne' vr.ne']
  have division : (X:ℝ)*(1/(u:ℝ)) = v ∧ (X:ℝ)*(1/(v:ℝ)) = u ∧ (X:ℝ)*(1/(X:ℝ))=1 := by
    constructor
    · rw [product]; field_simp
    constructor
    · rw [product]; field_simp
    · field_simp
  have totals : (∑ n ∈ Ioc 0 X, ((X/n:ℕ):ℝ)) + (X:ℝ) =
      (∑ n ∈ Ioc 0 u, ((X/n:ℕ):ℝ)) + ∑ n ∈ Ioc 0 v, ((X/n:ℕ):ℝ) := by
    exact_mod_cast floor_hyperbola hu hv
  have rhs : (∑ n ∈ Ioc 0 X, weight X n) =
      (X:ℝ) + (∑ n ∈ Ioc 0 X, ((X/n:ℕ):ℝ)) - (X:ℝ)*(harmonic X:ℝ) := by
    simp [weight, sum_sub_distrib, sum_add_distrib, harmonic_eq_sum_Icc,
      one_Icc X, Finset.mul_sum, div_eq_mul_inv]
  have xu := harmonic_floor_bounds X u
  have xv := harmonic_floor_bounds X v
  have terms (m : ℕ) (pos : 0 < m) := And.intro
    (mul_le_mul_of_nonneg_left (harmonic_vs_log pos).1 xr.le)
    (mul_le_mul_of_nonneg_left (harmonic_vs_log pos).2 xr.le)
  have a := terms X xp
  have b := terms u hu
  have c := terms v hv
  change |Real.eulerMascheroniConstant*(X:ℝ)-∑ n ∈ Ioc 0 X, weight X n| ≤ _
  rw [rhs]
  rw [logs] at a
  rcases division with ⟨du,dv,dx⟩
  simp only [mul_add,du,dv,dx] at a b c
  apply abs_le.mpr
  constructor <;> linarith only [a.1,a.2,b.1,b.2,c.1,c.2,xu.1,xu.2,xv.1,xv.2,totals]

end SparseAnchor
