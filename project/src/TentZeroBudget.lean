import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

noncomputable section
namespace TentZeroBudget
open Real

/-- Real part of the dephased tent transform, in real coordinates. -/
def companionRe (b σ t : ℝ) : ℝ :=
  let u := t^2 + σ*(1-σ)
  let v := t*(1-2*σ)
  Real.sqrt b * (((b+1)-(b^σ+b^(1-σ))*Real.cos (t*Real.log b))*u -
    (b^σ-b^(1-σ))*Real.sin (t*Real.log b)*v) / (u^2+v^2)

private theorem width_bound {b σ e : ℝ} (hb : 1 < b) (he : 0 < e)
    (hl : e ≤ σ) (hr : e ≤ 1-σ) :
    (b^σ-b^(1-σ))^2 ≤ (1-e)*(b-1)^2 := by
  have h1 : e ≤ 1 := by linarith
  have chord (x : ℝ) (hx : 0 ≤ x) (ht : x ≤ 1-e) :
      1 ≤ b^x ∧ b^x ≤ 1+(1-e)*(b-1) := by
    refine ⟨Real.one_le_rpow hb.le hx, ?_⟩
    have h := rpow_one_add_le_one_add_mul_self (s := b-1) (by linarith) hx (by linarith)
    rw [show 1+(b-1)=b by ring] at h
    exact h.trans (by gcongr)
  obtain ⟨a,A⟩ := chord σ (by linarith) (by linarith)
  obtain ⟨c,C⟩ := chord (1-σ) (by linarith) (by linarith)
  have spread : |b^σ-b^(1-σ)| ≤ (1-e)*(b-1) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have sq := pow_le_pow_left₀ (abs_nonneg _) spread 2
  rw [sq_abs, mul_pow] at sq
  have save : (1-e)^2 ≤ 1-e := by nlinarith only [mul_nonneg he.le (sub_nonneg.mpr h1)]
  exact sq.trans (mul_le_mul_of_nonneg_right save (sq_nonneg _))

private theorem positive_numerator {b A B u v e c s : ℝ} (hb : 1 < b)
    (hu : 0 < u) (he : 0 < e) (ha : A^2=B^2+4*b)
    (hbnd : B^2 ≤ (1-e)*(b-1)^2) (hv : v^2 ≤ e*u^2) (phase : c^2+s^2=1) :
    0 < ((b+1)-A*c)*u-B*s*v := by
  have hh : B^2*(u^2+v^2) < (b-1)^2*u^2 := calc
    _ ≤ B^2*((1+e)*u^2) := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    _ ≤ ((1-e)*(b-1)^2)*((1+e)*u^2) := mul_le_mul_of_nonneg_right hbnd (by positivity)
    _ = (b-1)^2*u^2 - e^2*(b-1)^2*u^2 := by ring
    _ < _ := by have : 0 < e^2*(b-1)^2*u^2 := by positivity
                linarith
  have mag : (A*u)^2+(B*v)^2 < ((b+1)*u)^2 := by
    rw [mul_pow A u, ha, mul_pow B v]
    linarith only [hh]
  have cs : (A*u*c + B*v*s)^2 ≤ (A*u)^2+(B*v)^2 := calc
    _ ≤ (A*u*c + B*v*s)^2 + (A*u*s-B*v*c)^2 := le_add_of_nonneg_right (sq_nonneg _)
    _ = ((A*u)^2+(B*v)^2)*(c^2+s^2) := by ring
    _ = _ := by rw [phase,mul_one]
  have pos : 0 < (b+1)*u := by positivity
  have small := cs.trans_lt mag
  have lt : A*u*c + B*v*s < (b+1)*u := by
    by_contra! back
    exact (not_lt_of_ge (pow_le_pow_left₀ pos.le back 2)) small
  linarith only [lt]

/-- A classical strip of width e with e t² ≥ 1 pays every width b, uniformly in the phase. -/
theorem companionRe_pos {b σ t e : ℝ} (hb : 1 < b) (he : 0 < e)
    (hl : e ≤ σ) (hr : e ≤ 1-σ) (ht : 1 ≤ e*t^2) : 0 < companionRe b σ t := by
  let u := t^2+σ*(1-σ)
  let v := t*(1-2*σ)
  have hprod : 0 < σ*(1-σ) := mul_pos (he.trans_le hl) (he.trans_le hr)
  have hu : 0 < u := by dsimp [u]; positivity
  have hangle : (1-2*σ)^2 ≤ 1 := by nlinarith only [hprod]
  have hsq : t^2 ≤ u := by dsimp [u]; linarith
  have vt : v^2 ≤ t^2 := by
    dsimp [v]
    rw [mul_pow]
    simpa using mul_le_mul_of_nonneg_left hangle (sq_nonneg t)
  have vbound : v^2 ≤ e*u^2 := calc
    _ ≤ t^2 := vt
    _ ≤ e*(t^2)^2 := by nlinarith only [mul_le_mul_of_nonneg_right ht (sq_nonneg t)]
    _ ≤ e*u^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg _) hsq 2) he.le
  have mul : b^σ*b^(1-σ) = b := by
    rw [← Real.rpow_add (by linarith : 0 < b), show σ+(1-σ)=1 by ring, Real.rpow_one]
  have alg : (b^σ+b^(1-σ))^2 = (b^σ-b^(1-σ))^2+4*b := by nlinarith only [mul]
  have ph := Real.sin_sq_add_cos_sq (t*Real.log b)
  have result := positive_numerator hb hu he alg (width_bound hb he hl hr) vbound
    (show Real.cos (t*Real.log b)^2+Real.sin (t*Real.log b)^2=1 by linarith only [ph])
  change 0 < Real.sqrt b * _ / (u^2+v^2)
  exact div_pos (mul_pos (Real.sqrt_pos.2 (by linarith)) result) (by positivity)

/-- The weakened logarithmic zero-free width already suffices above height six. -/
theorem height_criterion {t e : ℝ} (ht : 6 ≤ |t|) (he : 0 < e)
    (width : 1 ≤ 6 * Real.log |t| * e) : 1 ≤ e*t^2 := by
  have hlog := Real.log_le_sub_one_of_pos (by linarith : 0 < |t|)
  have first : 6*Real.log |t| ≤ 6*|t| := by linarith
  have last : 6*|t| ≤ |t|^2 := by nlinarith only [mul_nonneg (abs_nonneg t) (sub_nonneg.mpr ht)]
  have bound := mul_le_mul_of_nonneg_right (first.trans last) he.le
  rw [sq_abs] at bound
  linarith only [width, bound]

#print axioms companionRe_pos
#print axioms height_criterion
end TentZeroBudget
