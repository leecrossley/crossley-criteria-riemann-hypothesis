import TentZeroBudget
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section
namespace TentZeroBudget

def tent (b : ℝ) (z : ℂ) : ℂ :=
  ((b : ℂ) ^ z - 1) * ((b : ℂ) ^ z - b) / (z * (z - 1))

def companion (b : ℝ) (z : ℂ) : ℂ :=
  (Real.sqrt b : ℂ) * ((b + 1 : ℂ) - (b : ℂ) ^ z - (b : ℂ) ^ (1-z)) / (z * (1-z))

private theorem positive_base_components {b : ℝ} (hb : 0 < b) (z : ℂ) :
    ((b : ℂ) ^ z).re = b ^ z.re * Real.cos (z.im * Real.log b) ∧
    ((b : ℂ) ^ z).im = b ^ z.re * Real.sin (z.im * Real.log b) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hb.ne'),
    ← Complex.ofReal_log hb.le, Real.rpow_def_of_pos hb, Complex.exp_re, Complex.exp_im,
    Complex.re_ofReal_mul, Complex.im_ofReal_mul, mul_comm (Real.log b) z.im]
  exact ⟨rfl, rfl⟩

theorem companion_re {b : ℝ} (hb : 0 < b) (z : ℂ) :
    (companion b z).re = companionRe b z.re z.im := by
  let u := z.im ^ 2 + z.re * (1 - z.re)
  let v := z.im * (1 - 2*z.re)
  have denRe : (z * (1-z)).re = u := by
    simp [u, Complex.mul_re]
    ring
  have denIm : (z * (1-z)).im = v := by
    simp [v, Complex.mul_im]
    ring
  obtain ⟨pRe,pIm⟩ := positive_base_components hb z
  obtain ⟨qRe,qIm⟩ := positive_base_components hb (1-z)
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub,
    neg_mul, Real.cos_neg, Real.sin_neg, mul_neg] at qRe qIm
  rw [companion, Complex.div_re, Complex.normSq_apply, denRe, denIm,
    Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_re, Complex.one_im, pRe, pIm, qRe, qIm, add_zero, zero_sub]
  change _ = Real.sqrt b * _ / (u^2 + v^2)
  rw [← add_div]
  simp only [sq]
  ring

theorem companion_pos {b e : ℝ} {z : ℂ} (hb : 1 < b) (he : 0 < e)
    (hl : e ≤ z.re) (hr : e ≤ 1-z.re) (ht : 1 ≤ e*z.im^2) : 0 < (companion b z).re := by
  rw [companion_re (by linarith)]
  exact companionRe_pos hb he hl hr ht

#print axioms companion_re
#print axioms companion_pos
theorem dephase_tent {b : ℝ} (hb : 0 < b) (z : ℂ) :
    (b : ℂ) ^ ((1:ℂ)/2-z) * tent b z = companion b z := by
  have hb' := Complex.ofReal_ne_zero.mpr hb.ne'
  have hr : (b : ℂ) ^ ((1:ℂ)/2) = (Real.sqrt b : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hb.le]
    norm_num
  have hp : (b : ℂ) ^ z ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hb')
  have hd : z * (1-z) = -(z*(z-1)) := by ring
  rw [tent, companion, Complex.cpow_sub _ _ hb', Complex.cpow_sub _ _ hb',
    Complex.cpow_one, hd, div_neg, hr]
  simp only [div_eq_mul_inv]
  ring_nf
  field_simp
  ring

private theorem on_line_den {z : ℂ} (hz : z.re = 1/2) :
    z * (1-z) = ((1/4+z.im^2 : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.ofReal_re, Complex.mul_re, Complex.one_re, Complex.one_im,
      Complex.sub_re, Complex.sub_im, hz]
    ring
  · simp only [Complex.ofReal_im, Complex.mul_im, Complex.one_re, Complex.one_im,
      Complex.sub_re, Complex.sub_im, hz]
    ring

theorem companion_on_line {b : ℝ} {z : ℂ} (hb : 1 < b) (hz : z.re = 1/2) :
    (companion b z).re = ‖tent b z‖ := by
  have hb0 : 0 < b := by linarith
  have hmirror : 1-z = (star z) := by
    apply Complex.ext <;> simp [hz]
    ring
  have hc : (b : ℂ)^(1-z) = star ((b : ℂ)^z) := by
    rw [hmirror]
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hb0.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hb0.ne'), ← Complex.ofReal_log hb0.le]
    change _ = (starRingEnd ℂ) (Complex.exp _)
    rw [← Complex.exp_conj]
    simp
  have hn : (b + 1 : ℂ) - (b : ℂ)^z - (b : ℂ)^(1-z) =
      ((b + 1 - 2*((b : ℂ)^z).re : ℝ) : ℂ) := by
    rw [hc]
    apply Complex.ext <;> simp
    ring
  have hbnd : ((b : ℂ)^z).re ≤ Real.sqrt b := by
    have h := Complex.re_le_norm ((b : ℂ)^z)
    rwa [Complex.norm_cpow_eq_rpow_re_of_pos hb0, hz, ← Real.sqrt_eq_rpow] at h
  have harg : 0 ≤ b + 1 - 2*((b : ℂ)^z).re := by
    nlinarith only [hbnd, sq_nonneg (Real.sqrt b - 1), Real.sq_sqrt hb0.le]
  have unit : ‖(b : ℂ)^((1:ℂ)/2-z)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hb0]
    norm_num [hz]
  have hnorm : ‖companion b z‖ = ‖tent b z‖ := by
    rw [← dephase_tent hb0, norm_mul, unit, one_mul]
  rw [← hnorm, companion, hn, on_line_den hz, ← Complex.ofReal_mul, ← Complex.ofReal_div,
    Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg]
  positivity

noncomputable def lineMass (b : ℝ) (z : ℂ) : ℝ :=
  if z.re = 1/2 then ‖tent b z‖ else 0

/-- The family may repeat a zero to represent its multiplicity. -/
theorem line_mass_bound_and_equality {ι : Type*} {b : ℝ} (hb : 1 < b) (zero : ι → ℂ)
    (off : ∀ i, (zero i).re ≠ 1/2 →
      ∃ e : ℝ, 0 < e ∧ e ≤ (zero i).re ∧ e ≤ 1-(zero i).re ∧ 1 ≤ e*(zero i).im^2)
    (summable : Summable (fun i => (companion b (zero i)).re)) :
    (∑' i, lineMass b (zero i)) ≤ ∑' i, (companion b (zero i)).re ∧
    ((∑' i, lineMass b (zero i)) = ∑' i, (companion b (zero i)).re ↔
      ∀ i, (zero i).re = 1/2) := by
  have strict (i) (h : (zero i).re ≠ 1/2) :
      lineMass b (zero i) < (companion b (zero i)).re := by
    obtain ⟨e,he,hl,hr,ht⟩ := off i h
    rw [lineMass, if_neg h]
    exact companion_pos hb he hl hr ht
  have dom (i) : lineMass b (zero i) ≤ (companion b (zero i)).re := by
    by_cases h : (zero i).re = 1/2
    · rw [lineMass, if_pos h, companion_on_line hb h]
    · exact (strict i h).le
  have hs : Summable (fun i => lineMass b (zero i)) :=
    Summable.of_nonneg_of_le (fun i => by unfold lineMass; split <;> positivity) dom summable
  refine ⟨hs.tsum_le_tsum dom summable, ?_⟩
  constructor
  · intro heq i
    by_contra h
    exact (hs.tsum_lt_tsum dom (strict i h) summable).ne heq
  · intro all_line
    exact tsum_congr (fun i => by rw [lineMass, if_pos (all_line i), companion_on_line hb (all_line i)])

#print axioms dephase_tent
#print axioms companion_on_line
#print axioms line_mass_bound_and_equality
end TentZeroBudget
