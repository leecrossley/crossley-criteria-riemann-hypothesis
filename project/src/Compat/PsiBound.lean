import Mathlib
import Compat.Ramp

/-! Chebyshev error and eventual explicit bounds from `Compat.gzPNT` (`ZetaClassical.rampPNTStatement`).

Proves from Mathlib and `Compat.gzPNT`:
* `Compat.psi_sub_id_of_ramp`: a classical bound for the centred ramp gives
  `|ψ(x) - x| ≤ B x exp(-(c/4) √log x)` for `x ≥ 2`;
* `Compat.psi_sub_id_eventually`: `|ψ(x) - x| ≤ ε x` for large `x`;
* `Compat.psi_chebyshev_bounds_eventually`: eventual Chebyshev bounds for `ψ(x)`. -/

open scoped ArithmeticFunction.vonMangoldt
open Filter Finset

noncomputable section

namespace Compat

/-- `∑_{n ≤ x} Λ(n) / n`. -/
def lambdaOverN (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n / n

lemma psi_eq_sum_Icc_one (x : ℝ) : Chebyshev.psi x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n := by
  rw [Chebyshev.psi, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]

lemma Sz_eq (x : ℝ) : Compat.rampSz x = x * lambdaOverN x - Chebyshev.psi x := by
  rw [psi_eq_sum_Icc_one, lambdaOverN, Compat.rampSz, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- The ramp sum is convex with slope `lambdaOverN`: lower bound for an increment. -/
lemma Sz_sub_ge {x y : ℝ} (hxy : x ≤ y) :
    (y - x) * lambdaOverN x ≤ Compat.rampSz y - Compat.rampSz x := by
  have h1 : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (y / n - 1) ≤ Compat.rampSz y := by
    unfold Compat.rampSz
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hxy)) fun n hn _ => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr h1
    have hle : (n : ℝ) ≤ y := (Nat.le_floor_iff' (by omega)).mp h2
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (sub_nonneg.mpr ((one_le_div hn0).mpr hle))
  have h2 : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (y / n - 1) - Compat.rampSz x =
      (y - x) * lambdaOverN x := by
    rw [Compat.rampSz, lambdaOverN, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  linarith

/-- The ramp sum is convex with slope `lambdaOverN`: upper bound for an increment. -/
lemma Sz_sub_le {x y : ℝ} (hxy : x ≤ y) :
    Compat.rampSz y - Compat.rampSz x ≤ (y - x) * lambdaOverN y := by
  have hsub : Finset.Icc 1 ⌊x⌋₊ ⊆ Finset.Icc 1 ⌊y⌋₊ :=
    Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hxy)
  have h1 : ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n * (x / n - 1) ≤ Compat.rampSz x := by
    unfold Compat.rampSz
    rw [← Finset.sum_sdiff hsub]
    have hneg : ∑ n ∈ Finset.Icc 1 ⌊y⌋₊ \ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1) ≤ 0 := by
      refine Finset.sum_nonpos fun n hn => ?_
      obtain ⟨hy, hx⟩ := Finset.mem_sdiff.mp hn
      obtain ⟨h1, _⟩ := Finset.mem_Icc.mp hy
      have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr h1
      have hlt : x < n := by
        by_contra hcon
        exact hx (Finset.mem_Icc.mpr ⟨h1, (Nat.le_floor_iff' (by omega)).mpr (not_lt.mp hcon)⟩)
      exact mul_nonpos_of_nonneg_of_nonpos ArithmeticFunction.vonMangoldt_nonneg
        (sub_nonpos.mpr ((div_le_one hn0).mpr hlt.le))
    linarith
  have h2 : Compat.rampSz y - ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n * (x / n - 1) =
      (y - x) * lambdaOverN y := by
    rw [Compat.rampSz, lambdaOverN, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  linarith

private lemma exp_sqrt_log_anti {c : ℝ} (hc : 0 ≤ c) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.exp (-c * Real.sqrt (Real.log b)) ≤ Real.exp (-c * Real.sqrt (Real.log a)) := by
  apply Real.exp_le_exp.mpr
  have h := Real.sqrt_le_sqrt (Real.log_le_log ha hab)
  nlinarith [mul_nonneg hc (sub_nonneg.mpr h)]

/-- The differencing step for `x ≥ 4`. -/
private lemma psi_sub_id_large {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K)
    (hG : ∀ z : ℝ, 2 ≤ z → |Compat.rampGz z| ≤ K * z * Real.exp (-c * Real.sqrt (Real.log z)))
    {x : ℝ} (hx : 4 ≤ x) :
    |Chebyshev.psi x - x| ≤
      (1 / 2 + 7 * K) * x * Real.exp (-(c / 4) * Real.sqrt (Real.log x)) := by
  have hx0 : 0 < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hGx0 := hG x (by linarith)
  obtain ⟨L, hL⟩ : ∃ L, L = Real.sqrt (Real.log x) := ⟨_, rfl⟩
  rw [← hL] at hGx0 ⊢
  have hL0 : 0 ≤ L := hL ▸ Real.sqrt_nonneg _
  have hLsq : L ^ 2 = Real.log x := by rw [hL, Real.sq_sqrt hlogx]
  have hE : Real.exp (-c * L) = Real.exp (-(c / 4) * L) ^ 4 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hE2 : Real.exp (-c * (L / 2)) = Real.exp (-(c / 4) * L) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  obtain ⟨e, he⟩ : ∃ e, e = Real.exp (-(c / 4) * L) := ⟨_, rfl⟩
  rw [← he] at hE hE2 ⊢
  have he0 : 0 < e := he ▸ Real.exp_pos _
  have he1 : e ≤ 1 := by
    rw [he]; exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hc.le hL0])
  obtain ⟨h, hh⟩ : ∃ h, h = e / 2 := ⟨_, rfl⟩
  have hh0 : 0 < h := by rw [hh]; positivity
  have hh1 : h ≤ 1 / 2 := by rw [hh]; linarith
  have hKx : 0 ≤ K * x := mul_nonneg hK hx0.le
  -- the ramp at the three points
  have hGx : |Compat.rampGz x| ≤ K * x * e ^ 4 := by rwa [hE] at hGx0
  have hGp : |Compat.rampGz (x * (1 + h))| ≤ K * (2 * x) * e ^ 4 := by
    refine (hG _ (by nlinarith)).trans ?_
    have hmono : Real.exp (-c * Real.sqrt (Real.log (x * (1 + h)))) ≤ e ^ 4 := by
      rw [← hE, hL]
      exact exp_sqrt_log_anti hc.le hx0 (by nlinarith)
    have h1 : x * (1 + h) ≤ 2 * x := by nlinarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hK) hmono (Real.exp_pos _).le
      (mul_nonneg hK (by linarith))
  have hm_ge : x / 2 ≤ x * (1 - h) := by nlinarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlogm : Real.log x / 4 ≤ Real.log (x * (1 - h)) := by
    have h1 : Real.log (x / 2) ≤ Real.log (x * (1 - h)) := Real.log_le_log (by linarith) hm_ge
    have h2 : Real.log (x / 2) = Real.log x - Real.log 2 := Real.log_div hx0.ne' (by norm_num)
    have h3 : Real.log 4 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    linarith
  have hsqrtm : L / 2 ≤ Real.sqrt (Real.log (x * (1 - h))) := by
    have h1 : L / 2 = Real.sqrt (Real.log x / 4) := by
      rw [show Real.log x / 4 = (L / 2) ^ 2 by rw [div_pow, hLsq]; norm_num,
        Real.sqrt_sq (by positivity)]
    rw [h1]
    exact Real.sqrt_le_sqrt hlogm
  have hGm : |Compat.rampGz (x * (1 - h))| ≤ K * x * e ^ 2 := by
    refine (hG _ (by linarith)).trans ?_
    have hmono : Real.exp (-c * Real.sqrt (Real.log (x * (1 - h)))) ≤ e ^ 2 := by
      rw [← hE2]
      exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hsqrtm)])
    have h1 : x * (1 - h) ≤ x := by nlinarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hK) hmono (Real.exp_pos _).le hKx
  -- algebra of the increments
  obtain ⟨A, hA⟩ : ∃ A, A = lambdaOverN x := ⟨_, rfl⟩
  have hψ : Chebyshev.psi x = x * A - Compat.rampSz x := by rw [hA, Sz_eq]; ring
  have hSx : Compat.rampSz x =
      Compat.rampGz x + x * Real.log x - (1 + Real.eulerMascheroniConstant) * x := by
    unfold Compat.rampGz; ring
  have hSp : Compat.rampSz (x * (1 + h)) = Compat.rampGz (x * (1 + h)) +
      x * (1 + h) * (Real.log x + Real.log (1 + h)) -
        (1 + Real.eulerMascheroniConstant) * (x * (1 + h)) := by
    rw [← Real.log_mul hx0.ne' (by positivity)]; unfold Compat.rampGz; ring
  have hSm : Compat.rampSz (x * (1 - h)) = Compat.rampGz (x * (1 - h)) +
      x * (1 - h) * (Real.log x + Real.log (1 - h)) -
        (1 + Real.eulerMascheroniConstant) * (x * (1 - h)) := by
    rw [← Real.log_mul hx0.ne' (by linarith)]; unfold Compat.rampGz; ring
  have hlp : Real.log (1 + h) ≤ h := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + h by positivity); linarith
  have hlm : Real.log (1 - h) ≤ -h := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 - h by linarith); linarith
  have hlow := Sz_sub_ge (show x ≤ x * (1 + h) by nlinarith)
  have hupp := Sz_sub_le (show x * (1 - h) ≤ x by nlinarith)
  rw [← hA] at hlow hupp
  rw [hSp, hSx] at hlow
  rw [hSm, hSx] at hupp
  have key : h * (Chebyshev.psi x - x) = x * h * A - h * Compat.rampGz x - h * x * Real.log x +
      Real.eulerMascheroniConstant * h * x := by
    rw [hψ, hSx]; ring
  have hprod_p : x * (1 + h) * Real.log (1 + h) ≤ x * (1 + h) * h :=
    mul_le_mul_of_nonneg_left hlp (by positivity)
  have hprod_m : x * (1 - h) * Real.log (1 - h) ≤ x * (1 - h) * (-h) :=
    mul_le_mul_of_nonneg_left hlm (mul_nonneg hx0.le (by linarith))
  have upper : h * (Chebyshev.psi x - x) ≤
      Compat.rampGz (x * (1 + h)) - Compat.rampGz x + x * h * h - h * Compat.rampGz x := by
    rw [key]; linarith
  have lower : Compat.rampGz x - Compat.rampGz (x * (1 - h)) - x * h * h - h * Compat.rampGz x ≤
      h * (Chebyshev.psi x - x) := by
    rw [key]; linarith
  -- sizes
  obtain ⟨hGx1, hGx2⟩ := abs_le.mp hGx
  obtain ⟨_, hGp2⟩ := abs_le.mp hGp
  obtain ⟨hGm1, _⟩ := abs_le.mp hGm
  have m4 : K * x * e ^ 4 ≤ K * x * e ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one he0.le he1 (by norm_num)) hKx
  have m5 : K * x * e ^ 5 ≤ K * x * e ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one he0.le he1 (by norm_num)) hKx
  have hq : 0 ≤ K * x * e ^ 2 := mul_nonneg hKx (by positivity)
  have hhG1 : h * (-(K * x * e ^ 4)) ≤ h * Compat.rampGz x :=
    mul_le_mul_of_nonneg_left hGx1 hh0.le
  have hhG2 : h * Compat.rampGz x ≤ h * (K * x * e ^ 4) :=
    mul_le_mul_of_nonneg_left hGx2 hh0.le
  subst hh
  rw [abs_le]
  constructor
  · refine le_of_mul_le_mul_left ?_ hh0
    nlinarith
  · refine le_of_mul_le_mul_left ?_ hh0
    nlinarith

/-- A classical bound for the centred ramp gives the prime number theorem for the Chebyshev
function with a classical error term. Mathlib only. -/
theorem psi_sub_id_of_ramp {c K : ℝ} (hc : 0 < c)
    (hG : ∀ z : ℝ, 2 ≤ z → |Compat.rampGz z| ≤ K * z * Real.exp (-c * Real.sqrt (Real.log z))) :
    ∀ x : ℝ, 2 ≤ x → |Chebyshev.psi x - x| ≤
      (1 / 2 + 7 * |K| + 6 * Real.exp (c / 2)) * x *
        Real.exp (-(c / 4) * Real.sqrt (Real.log x)) := by
  intro x hx
  have hG' : ∀ z : ℝ, 2 ≤ z →
      |Compat.rampGz z| ≤ |K| * z * Real.exp (-c * Real.sqrt (Real.log z)) := fun z hz =>
    (hG z hz).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith)) (Real.exp_pos _).le)
  have hx0 : 0 < x := by linarith
  have hE0 := Real.exp_pos (-(c / 4) * Real.sqrt (Real.log x))
  have hxE : 0 ≤ x * Real.exp (-(c / 4) * Real.sqrt (Real.log x)) := mul_nonneg hx0.le hE0.le
  by_cases h4 : 4 ≤ x
  · refine (psi_sub_id_large hc (abs_nonneg K) hG' h4).trans ?_
    have := mul_le_mul_of_nonneg_right
      (show 1 / 2 + 7 * |K| ≤ 1 / 2 + 7 * |K| + 6 * Real.exp (c / 2) by
        linarith [Real.exp_pos (c / 2)]) hxE
    linarith
  · have h4' : x < 4 := lt_of_not_ge h4
    have hpsi0 := Chebyshev.psi_nonneg x
    have hpsi := Chebyshev.psi_le_const_mul_self hx0.le
    have hlog4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
    have hprod := mul_le_mul_of_nonneg_right hlog4 hx0.le
    have habs : |Chebyshev.psi x - x| ≤ 6 * x := by
      rw [abs_le]; constructor <;> linarith
    have hlogx : Real.log x ≤ 4 := by
      have := Real.log_le_log hx0 h4'.le; linarith
    have hL : Real.sqrt (Real.log x) ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hlogx
    have hone : 1 ≤ Real.exp (c / 2) * Real.exp (-(c / 4) * Real.sqrt (Real.log x)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hL)])
    have h6 : 6 * x ≤ 6 * x *
        (Real.exp (c / 2) * Real.exp (-(c / 4) * Real.sqrt (Real.log x))) :=
      le_mul_of_one_le_right (by linarith) hone
    have hrest : 0 ≤ (1 / 2 + 7 * |K|) *
        (x * Real.exp (-(c / 4) * Real.sqrt (Real.log x))) :=
      mul_nonneg (by positivity) hxE
    linarith

/-- The prime number theorem for the Chebyshev function, in the form `|ψ(x) - x| ≤ ε x` for
large `x`. From the ramp prime number theorem. -/
theorem psi_sub_id_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, |Chebyshev.psi x - x| ≤ ε * x := by
  obtain ⟨c, K, hc, hG⟩ := Compat.gzPNT
  have hbound := psi_sub_id_of_ramp hc hG
  obtain ⟨B, hB⟩ : ∃ B, B = 1 / 2 + 7 * |K| + 6 * Real.exp (c / 2) := ⟨_, rfl⟩
  rw [← hB] at hbound
  have hBpos : 0 < B := by rw [hB]; positivity
  have htend : Tendsto (fun x : ℝ => Real.exp (-(c / 4) * Real.sqrt (Real.log x))) atTop
      (nhds 0) := by
    have h1 : Tendsto (fun x : ℝ => (c / 4) * Real.sqrt (Real.log x)) atTop atTop :=
      (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).const_mul_atTop (by positivity)
    refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).congr fun x => ?_
    simp only [Function.comp_apply, neg_mul]
  have hev := htend.eventually (eventually_lt_nhds (show (0 : ℝ) < ε / B by positivity))
  filter_upwards [hev, eventually_ge_atTop (2 : ℝ)] with x hx h2
  calc |Chebyshev.psi x - x| ≤ B * x * Real.exp (-(c / 4) * Real.sqrt (Real.log x)) :=
        hbound x h2
    _ ≤ B * x * (ε / B) := mul_le_mul_of_nonneg_left hx.le (by positivity)
    _ = ε * x := by field_simp

/-- Eventual Chebyshev lower and upper bounds for `Chebyshev.psi x`. -/
theorem psi_chebyshev_bounds_eventually : ∀ᶠ x : ℝ in atTop,
    0.92129 * x - 5 / 2 * Real.log x ≤ Chebyshev.psi x ∧
      Chebyshev.psi x ≤ 1.1056 * x + 0.7 * (Real.log x) ^ 2 := by
  filter_upwards [psi_sub_id_eventually (show (0 : ℝ) < 1 / 20 by norm_num),
    eventually_ge_atTop (1 : ℝ)] with x hx h1
  have hlog := Real.log_nonneg h1
  have hsq := sq_nonneg (Real.log x)
  obtain ⟨hlo, hhi⟩ := abs_le.mp hx
  constructor
  · linarith
  · linarith

end Compat
