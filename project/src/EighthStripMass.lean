import ZetaWindowMass

open Finset
namespace RiemannReduction.ZetaWindow.Eighth
noncomputable section

/-- The statement supplied by the separately published seven-eighths zero-free theorem. -/
def ZeroFree : Prop := ∀ {s : ℂ}, (7/8 : ℝ) < s.re → riemannZeta s ≠ 0

theorem strip_bounds (free : ZeroFree) {z : ℂ} (hz : stripZero z) :
    (1/8 : ℝ) ≤ z.re ∧ z.re ≤ 7/8 := by
  obtain ⟨zp,z1,zero⟩ := hz
  have high : z.re ≤ 7/8 := le_of_not_gt (fun h => free h zero)
  have zone : z ≠ 1 := by rintro rfl; norm_num at z1
  have nonneg (n : ℕ) : z ≠ -n := by
    intro e
    have er := congrArg Complex.re e
    simp only [Complex.neg_re,Complex.natCast_re] at er
    linarith [Nat.cast_nonneg (α:=ℝ) n]
  have zsym : riemannZeta (1-z) = 0 := by rw [riemannZeta_one_sub nonneg zone,zero,mul_zero]
  refine ⟨?_,high⟩
  by_contra! h
  exact free (show (7/8:ℝ) < (1-z).re by simp only [Complex.sub_re,Complex.one_re]; linarith) zsym

private def window (t : ℝ) : Set ℂ := {z | 0 < z.re ∧ z.re < 1 ∧
  |z.im-t| ≤ 1 ∧ riemannZeta z = 0}

private lemma windows : ∃ C > (0:ℝ), ∀ t : ℝ, ∃ fin : (window t).Finite,
    ∑ z ∈ fin.toFinset, mass z ≤ C*Real.log (|t|+2) := by
  obtain ⟨C,hC,count⟩ := Compat.count_zeros_window_zeta
  refine ⟨C,hC,fun t => ?_⟩
  obtain ⟨fin,bound⟩ := count t
  exact ⟨fin, by rwa [finsum_mem_eq_finite_toFinset_sum _ fin] at bound⟩

private def bucket (z : ℂ) : ℕ := ⌊|z.im|⌋₊

private lemma bucket_window {z : ℂ} (hz : stripZero z) :
    z ∈ window (bucket z) ∨ z ∈ window (-(bucket z:ℝ)) := by
  have lo := Nat.floor_le (abs_nonneg z.im)
  have hi := Nat.lt_floor_add_one |z.im|
  change (0 < z.re ∧ z.re < 1 ∧ |z.im-↑⌊|z.im|⌋₊| ≤ 1 ∧ riemannZeta z = 0) ∨
    (0 < z.re ∧ z.re < 1 ∧ |z.im- -↑⌊|z.im|⌋₊| ≤ 1 ∧ riemannZeta z = 0)
  generalize hn : (↑⌊|z.im|⌋₊ : ℝ) = n at *
  by_cases pos : 0 ≤ z.im
  · rw [abs_of_nonneg pos] at lo hi
    exact Or.inl ⟨hz.1,hz.2.1,abs_le.mpr ⟨by linarith,by linarith⟩,hz.2.2⟩
  · rw [abs_of_nonpos (le_of_not_ge pos)] at lo hi
    exact Or.inr ⟨hz.1,hz.2.1,abs_le.mpr ⟨by linarith,by linarith⟩,hz.2.2⟩

private lemma weight_le {z : ℂ} (left : (1/8:ℝ) ≤ z.re) (right : z.re ≤ 7/8) :
    1/(‖z‖*‖z-1‖) ≤ 81/((bucket z:ℝ)+1)^2 := by
  have fl : (bucket z:ℝ) ≤ |z.im| := Nat.floor_le (abs_nonneg _)
  have iz := Complex.abs_im_le_norm z
  have iw : |z.im| ≤ ‖z-1‖ := by simpa using Complex.abs_im_le_norm (z-1)
  have rz := (le_abs_self z.re).trans (Complex.abs_re_le_norm z)
  have wr : 1-z.re ≤ ‖z-1‖ := by
    have v := (neg_le_abs (z-1).re).trans (Complex.abs_re_le_norm (z-1))
    simpa only [Complex.sub_re,Complex.one_re, neg_sub] using v
  have zp : 0 < ‖z‖ := by linarith
  have wp : 0 < ‖z-1‖ := by linarith
  have bp : 0 ≤ (bucket z:ℝ)+1 := by positivity
  have h := mul_le_mul (show (bucket z:ℝ)+1 ≤ 9*‖z‖ by linarith)
    (show (bucket z:ℝ)+1 ≤ 9*‖z-1‖ by linarith) bp (by positivity)
  apply (div_le_div_iff₀ (mul_pos zp wp) (sq_pos_of_pos (by positivity))).mpr
  nlinarith only [h]

private lemma log_series : Summable (fun n : ℕ => Real.log ((n:ℝ)+2)/((n:ℝ)+1)^2) := by
  have ps := (Real.summable_nat_rpow.mpr (show -(3/2:ℝ) < -1 by norm_num))
  have shifted := (summable_nat_add_iff 1).mpr ps
  have major : Summable (fun n : ℕ => 4 * ((n:ℝ)+1)^(-(3/2):ℝ)) := by
    simpa only [Nat.cast_add,Nat.cast_one] using shifted.mul_left 4
  apply major.of_nonneg_of_le
  · intro n; exact div_nonneg (Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) n])) (sq_nonneg _)
  intro n
  set x : ℝ := (n:ℝ)+1
  have hx : 1 ≤ x := by dsimp [x]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hp : 0 < x := by linarith
  have l := Real.log_le_rpow_div (show 0 ≤ (n:ℝ)+2 by positivity) (show (0:ℝ)<1/2 by norm_num)
  rw [← Real.sqrt_eq_rpow] at l
  have sq1 := Real.sq_sqrt (show 0 ≤ (n:ℝ)+2 by positivity)
  have sq2 := Real.sq_sqrt hp.le
  have roots : Real.sqrt ((n:ℝ)+2) ≤ 2*Real.sqrt x := by
    have : (n:ℝ)+2 ≤ 4*x := by dsimp [x]; linarith [Nat.cast_nonneg (α:=ℝ) n]
    nlinarith [Real.sqrt_nonneg x,Real.sqrt_nonneg ((n:ℝ)+2)]
  rw [show -(3/2:ℝ)=1/2-(2:ℕ) by norm_num,Real.rpow_sub hp,Real.rpow_natCast,← Real.sqrt_eq_rpow]
  rw [mul_div_assoc', div_le_div_iff_of_pos_right (sq_pos_of_pos hp)]
  linarith

/-- Uniform in the truncation height and including multiplicities. -/
theorem finite_inverse_square_mass (free : ZeroFree) : ∃ H ≥ (0:ℝ),
    ∀ S : Finset ℂ, (∀ z ∈ S, stripZero z) →
    (∑ z ∈ S, mass z/(‖z‖*‖z-1‖)) ≤ H := by
  classical
  obtain ⟨C,cp,count⟩ := windows
  let g (n : ℕ) := Real.log ((n:ℝ)+2)/((n:ℝ)+1)^2
  have gn (n : ℕ) : 0 ≤ g n :=
    div_nonneg (Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) n])) (sq_nonneg _)
  refine ⟨162*C*∑' n, g n, mul_nonneg (by positivity) (tsum_nonneg gn),fun S hS => ?_⟩
  let bins := S.image bucket
  have split := sum_fiberwise_of_maps_to (t := bins) (fun z hz => mem_image_of_mem bucket hz)
    (fun z => mass z/(‖z‖*‖z-1‖))
  rw [← split]
  calc _ ≤ ∑ n ∈ bins, 162*C*g n := by
         apply sum_le_sum
         intro n _
         obtain ⟨pos,hpos⟩ := count (n:ℝ)
         obtain ⟨neg,hneg⟩ := count (-(n:ℝ))
         simp only [abs_neg,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) n)] at hpos hneg
         let F := S.filter (fun z => bucket z=n)
         have sub : F ⊆ pos.toFinset ∪ neg.toFinset := by
           intro z mem
           obtain ⟨hz,hn⟩ := mem_filter.mp mem
           have h := bucket_window (hS z hz)
           rw [hn] at h
           simpa using h
         have upper := sum_le_sum_of_subset_of_nonneg (f:=mass) sub (fun z _ _ => mass_nonneg z)
         have union := sum_union_inter (s₁:=pos.toFinset) (s₂:=neg.toFinset) (f:=mass)
         have small := sum_nonneg (s:=pos.toFinset ∩ neg.toFinset) (fun z _ => mass_nonneg z)
         have both : ∑ z ∈ F, mass z ≤ 2*C*Real.log ((n:ℝ)+2) := by linarith
         calc _ ≤ ∑ z ∈ F, mass z*(81/((n:ℝ)+1)^2) := by
                apply sum_le_sum
                intro z hz
                obtain ⟨mem,hn⟩ := mem_filter.mp hz
                have w := weight_le (strip_bounds free (hS z mem)).1 (strip_bounds free (hS z mem)).2
                rw [hn] at w
                simpa only [← div_eq_mul_one_div] using mul_le_mul_of_nonneg_left w (mass_nonneg z)
              _ = (∑ z ∈ F, mass z)*(81/((n:ℝ)+1)^2) := (sum_mul ..).symm
              _ ≤ (2*C*Real.log ((n:ℝ)+2))*(81/((n:ℝ)+1)^2) :=
                mul_le_mul_of_nonneg_right both (by positivity)
              _ = 162*C*g n := by dsimp [g]; ring
       _ = 162*C * ∑ n ∈ bins, g n := (mul_sum ..).symm
       _ ≤ _ := mul_le_mul_of_nonneg_left (log_series.sum_le_tsum bins (fun n _ => gn n)) (by positivity)

#print axioms finite_inverse_square_mass
end
end RiemannReduction.ZetaWindow.Eighth
