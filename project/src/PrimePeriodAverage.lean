import DirectRampConvexity

open Finset IndependentLandau

noncomputable section
namespace PrimePeriodAverage

/-- Average an integer sequence over the symmetric box of radius `h`. -/
def box (h : ℕ) (f : ℤ → ℝ) (x : ℤ) : ℝ :=
  (∑ j ∈ range (2*h+1), f (x + (j : ℤ) - (h : ℤ))) / ((2*h+1 : ℕ) : ℝ)

def centered (p : ℕ) (f : ℤ → ℝ) : Prop :=
  ∀ x : ℤ, ∑ j ∈ range p, f (x + (j : ℤ)) = 0

theorem centered_box {p h : ℕ} {f : ℤ → ℝ} (hf : centered p f) :
    centered p (box h f) := by
  intro x
  unfold box
  rw [← sum_div, sum_comm]
  have zero : (∑ j ∈ range (2*h+1), ∑ i ∈ range p,
      f (x + (i : ℤ) + (j : ℤ) - (h : ℤ))) = 0 := by
    apply sum_eq_zero
    intro j _
    have eq (i : ℕ) : x + (i : ℤ) + (j : ℤ) - (h : ℤ) =
        x + (j : ℤ) - (h : ℤ) + (i : ℤ) := by ring
    simpa only [eq] using hf (x + (j : ℤ) - (h : ℤ))
  rw [zero, zero_div]

private theorem full_periods_zero {p : ℕ} {f : ℤ → ℝ} (hf : centered p f) (q : ℕ) (x : ℤ) :
    ∑ j ∈ range (p*q), f (x + (j : ℤ)) = 0 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, sum_range_add, ih, zero_add]
    have eq (i : ℕ) : x + ((p*q+i : ℕ) : ℤ) = x + ((p*q : ℕ) : ℤ) + (i : ℤ) := by
      push_cast
      ring
    simpa only [eq] using hf (x + ((p*q : ℕ) : ℤ))

/-- Complete periods drop out, leaving only the last incomplete period. -/
theorem box_le {p h : ℕ} {f : ℤ → ℝ} (hp : 0 < p) (hf : centered p f)
    {A : ℝ} (ha : 0 ≤ A) (bound : ∀ x, |f x| ≤ A) (x : ℤ) :
    |box h f x| ≤ ((p : ℝ) / ((2*h+1 : ℕ) : ℝ)) * A := by
  let W := 2*h+1
  let z := x - (h : ℤ)
  have pos : 0 < (W : ℝ) := by dsimp [W]; positivity
  have split : W = p*(W/p) + W%p := (Nat.mod_add_div W p).symm.trans (by omega)
  have sum_bound : |∑ j ∈ range W, f (z + (j : ℤ))| ≤ (p : ℝ)*A := by
    rw [show range W = range (p*(W/p) + W%p) from congrArg range split]
    rw [sum_range_add, full_periods_zero hf, zero_add]
    calc
      _ ≤ ∑ j ∈ range (W%p), |f (z + ((p*(W/p)+j : ℕ) : ℤ))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ range (W%p), A := sum_le_sum fun j _ => bound _
      _ = ((W%p : ℕ) : ℝ)*A := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (Nat.mod_lt W hp).le) ha
  unfold box
  have eq (j : ℕ) : x + (j : ℤ) - (h : ℤ) = z + (j : ℤ) := by dsimp [z]; ring
  simp only [eq]
  change |(∑ j ∈ range W, f (z + (j : ℤ))) / (W : ℝ)| ≤ ((p : ℝ) / W)*A
  rw [abs_div, abs_of_pos pos]
  calc _ ≤ ((p : ℝ)*A) / W := div_le_div_of_nonneg_right sum_bound pos.le
       _ = _ := by ring

def iterate (h : ℕ) (f : ℤ → ℝ) : ℕ → ℤ → ℝ
  | 0 => f
  | r + 1 => box h (iterate h f r)

theorem centered_iterate {p h : ℕ} {f : ℤ → ℝ} (hf : centered p f) (r : ℕ) :
    centered p (iterate h f r) := by
  induction r with
  | zero => exact hf
  | succ r ih => exact centered_box ih

theorem iterate_le {p h : ℕ} {f : ℤ → ℝ} (hp : 0 < p) (hf : centered p f)
    {A : ℝ} (ha : 0 ≤ A) (bound : ∀ x, |f x| ≤ A) (r : ℕ) (x : ℤ) :
    |iterate h f r x| ≤ ((p : ℝ) / ((2*h+1 : ℕ) : ℝ))^r * A := by
  induction r generalizing x with
  | zero => simpa [iterate] using bound x
  | succ r ih =>
    have nonneg : 0 ≤ ((p : ℝ) / ((2*h+1 : ℕ) : ℝ))^r * A :=
      mul_nonneg (pow_nonneg (by positivity) _) ha
    calc
      _ ≤ ((p : ℝ) / ((2*h+1 : ℕ) : ℝ)) *
          (((p : ℝ) / ((2*h+1 : ℕ) : ℝ))^r * A) :=
        box_le hp (centered_iterate hf r) nonneg ih x
      _ = _ := by ring

/-- The symmetric pair around a fourth-power sample pays only a quadratic cost. -/
theorem ramp_midpoint {x u R : ℝ} (hR : |u| ≤ R) (hx : R < x) :
    rampG x ≤ (rampG (x-u) + rampG (x+u))/2 + R^2/(x-R) := by
  obtain ⟨lo, hi⟩ := abs_le.mp hR
  have aux (v : ℝ) (v0 : 0 ≤ v) (vR : v ≤ R) :
      rampG x ≤ (rampG (x-v) + rampG (x+v))/2 + R^2/(x-R) := by
    have ch := DirectRampConvexity.rampG_chord_le
      (show 0 < x-v by linarith) (show x-v ≤ x+v by linarith)
      (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num : (1/2:ℝ) ≤ 1)
    dsimp only at ch
    rw [show (1-(1/2:ℝ))*(x-v)+(1/2:ℝ)*(x+v)=x by ring,
      show x-(x-v)=v by ring, show x+v-x=v by ring, ← pow_two] at ch
    have gap : v^2/(x-v) ≤ R^2/(x-R) := by
      exact (div_le_div_of_nonneg_right (pow_le_pow_left₀ v0 vR 2)
        (by linarith)).trans (div_le_div_of_nonneg_left (sq_nonneg R)
          (by linarith) (by linarith))
    linarith only [ch, gap]
  rcases le_total 0 u with h | h
  · exact aux u h hi
  · simpa only [sub_neg_eq_add, ← sub_eq_add_neg, add_comm] using
      aux (-u) (neg_nonneg.mpr h) (by linarith)

/-- The fractional complement after subtraction of its exact discrete mean. -/
def residue (p : ℕ) (x : ℤ) : ℝ :=
  (((p : ℝ)-1)/2 - (((x % (p : ℤ)) : ℤ) : ℝ)) / p

theorem residue_centered {p : ℕ} (hp : 0 < p) : centered p (residue p) := by
  let f := residue p
  let S (x : ℤ) := ∑ j ∈ range p, f (x + (j : ℤ))
  have eq (x : ℤ) : f (x + p) = f x := by
    simp only [f, residue]
    rw [Int.add_emod, Int.emod_self, add_zero, Int.emod_emod]
  have step (x : ℤ) : S (x+1) = S x := by
    -- Compare the two decompositions of the same window of length p + 1.
    have first := sum_range_succ (fun j : ℕ => f (x+(j:ℤ))) p
    have second := sum_range_succ' (fun j : ℕ => f (x+(j:ℤ))) p
    have alternate : (∑ j ∈ range p, f (x+((j+1:ℕ):ℤ))) = S (x+1) := by
      unfold S
      exact sum_congr rfl fun j _ => by push_cast; ring_nf
    rw [first, alternate, eq, Nat.cast_zero, add_zero] at second
    change S x + f x = S (x+1) + f x at second
    linarith only [second]
  have initial : S 0 = 0 := by
    have scale : (∑ j ∈ range p, (((p:ℝ)-1)/2 - (j:ℝ))) = 0 := by
      have count := Finset.sum_range_id_mul_two p
      have cast_count : (∑ j ∈ range p, (j:ℝ)) * 2 = (p:ℝ)*((p:ℝ)-1) := by
        have h := congrArg (Nat.cast : ℕ → ℝ) count
        push_cast [Nat.cast_sub (Nat.one_le_of_lt hp)] at h
        exact h
      rw [sum_sub_distrib]
      simp only [sum_const, card_range, nsmul_eq_mul]
      linarith only [cast_count]
    unfold S
    have term (j : ℕ) (hj : j∈range p) : f (0+(j:ℤ)) = (((p:ℝ)-1)/2 - (j:ℝ))/p := by
      simp only [f, residue]
      rw [zero_add, Int.emod_eq_of_lt (by positivity)
        (by exact_mod_cast (mem_range.mp hj)), Int.cast_natCast]
    rw [sum_congr rfl term, ← sum_div, scale, zero_div]
  intro x
  change S x = 0
  induction x using Int.induction_on with
  | zero => exact initial
  | succ i ih => exact (step i).trans ih
  | pred i ih =>
    have h := step (-(i:ℤ)-1)
    rw [sub_add_cancel, ih] at h
    exact h.symm

theorem residue_abs_le_one {p : ℕ} (hp : 0 < p) (x : ℤ) : |residue p x| ≤ 1 := by
  have ip : 0 < (p : ℤ) := by exact_mod_cast hp
  have rp : 0 < (p : ℝ) := by exact_mod_cast hp
  have p1 : 1 ≤ (p : ℝ) := by exact_mod_cast (Nat.one_le_of_lt hp)
  have lo : 0 ≤ (((x % (p : ℤ)) : ℤ) : ℝ) := by exact_mod_cast Int.emod_nonneg x ip.ne'
  have hi : (((x % (p : ℤ)) : ℤ) : ℝ) ≤ p := by exact_mod_cast (Int.emod_lt_of_pos x ip).le
  rw [residue, abs_div, abs_of_pos rp, div_le_iff₀ rp, one_mul]
  exact abs_le.mpr ⟨by linarith only [p1, hi], by linarith only [rp, lo]⟩

theorem residue_average {p h : ℕ} (hp : 0 < p) (r : ℕ) (x : ℤ) :
    |iterate h (residue p) r x| ≤ ((p : ℝ) / ((2*h+1 : ℕ) : ℝ)) ^ r := by
  simpa only [mul_one] using
    (iterate_le (h := h) hp (residue_centered hp) zero_le_one (residue_abs_le_one hp) r x)

#print axioms iterate_le
#print axioms ramp_midpoint
#print axioms residue_centered
#print axioms residue_average

end PrimePeriodAverage
