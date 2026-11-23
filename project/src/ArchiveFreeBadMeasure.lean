import Mathlib
import IndependentLandau.WindowLemma
import IndependentLandau.Zeta
import RampWindowEquivalence

/-!
# Archive-Free Exceptional-Measure Density for `IndependentLandau.rampG`

This module proves, 100% from Mathlib `0df444a360ea` and first-party Mathlib-only modules
(`IndependentLandau`, `RampWindowEquivalence`), that any zeta zero in `Re s > θ` (`1/2 ≤ θ < 1`)
forces near-full physical Lebesgue measure `> Y^(1 + d - ε)` of threshold violations
`rampG x > c * x^θ` on **every** sufficiently late multiplicative block `[Y, Y^(1+d)]`, with zero
external archive objects:

1. **Elementary Slope & Linear Upper Envelope (`rampG_rise`, `rampG_le_linear`):**
   Proves `rampG y - rampG x ≤ 8 * (y - x)` for `1 ≤ x ≤ y` and `rampG x ≤ 8 * x + 2` for `x ≥ 1`
   purely from `∑_{d | m} Λ(d) = log m` and `Chebyshev.psi_le_const_mul_self`.
2. **Weighted Positive-Excess Mass (`pole_forces_excess`, `cofinalUpper_iff_zeroFree`):**
   Uses `IndependentLandau.landau_window` and `IndependentLandau.zeta_poleData` for the lower bound
   and `DirectRampEquivalence.abs_rampG_le_of_zeroFree` for the upper bound.
3. **Near-Full Exceptional Measure (`near_full_measure_every_window_mathlib`) & Converse
   (`zeroFree_of_subfull_bad_measure`):**
   Combines the infimum over zero-free abscissas `u = sInf {b ≥ 1/2 | ZeroFree b}` with
   `DirectRampEquivalence.abs_rampG_le_of_zeroFree` (when `u < 1`) and `rampG_le_linear` (when
   `u = 1`) to force `volume {x ∈ [Y, Y^(1+d)] | c * x^θ < rampG x} > ENNReal.ofReal (Y^(1+d-ε))`
   on every late window whenever `∃ ρ, θ < ρ.re ∧ riemannZeta ρ = 0`.
-/

open MeasureTheory Complex Set Filter Topology Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace ArchiveFreeBadMeasure

/-! ### 1. Elementary Slope, Linear Upper Bound, and Power Absorption -/

/-- Truncation of `rampS u` to any finite range `0 .. N` with `⌊u⌋₊ ≤ N`. -/
lemma rampS_on_range {u : ℝ} {N : ℕ} (hu : ⌊u⌋₊ ≤ N) :
    IndependentLandau.rampS u = ∑ n ∈ Finset.range (N + 1), IndependentLandau.rampT n u := by
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hu))
  intro n _ hn
  apply IndependentLandau.rampT_eq_zero_of_floor_lt
  simpa [Finset.mem_range] using hn

/-- Floor-divisor identity `∑_{1 ≤ d ≤ N} ⌊N/d⌋ Λ(d) = ∑_{1 ≤ m ≤ N} log m`. -/
private lemma floor_weight (N : ℕ) :
    (∑ d ∈ Finset.Ioc 0 N, (N / d : ℕ) * Λ d) = ∑ m ∈ Finset.Ioc 0 N, Real.log m := by
  classical
  have split (m : ℕ) (hm : m ∈ Finset.Ioc 0 N) :
      Real.log m = ∑ d ∈ Finset.Ioc 0 N, if d ∣ m then Λ d else 0 := by
    have mp := (Finset.mem_Ioc.mp hm).1
    have divs : m.divisors = (Finset.Ioc 0 N).filter (· ∣ m) := by
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨hd, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hd mp, (Nat.le_of_dvd mp hd).trans (Finset.mem_Ioc.mp hm).2⟩, hd⟩
      · rintro ⟨_, hd⟩
        exact ⟨hd, mp.ne'⟩
    rw [← ArithmeticFunction.vonMangoldt_sum, divs, Finset.sum_filter]
  rw [Finset.sum_congr rfl split, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div]

/-- Elementary one-sided Mertens bound `∑_{1 ≤ d ≤ N} Λ(d)/d ≤ log N + log 4 + 4`. -/
theorem reciprocal_mass (N : ℕ) (hN : 0 < N) :
    ∑ d ∈ Finset.Ioc 0 N, Λ d / d ≤ Real.log N + (Real.log 4 + 4) := by
  have npos : 0 < (N : ℝ) := by exact_mod_cast hN
  have summand (d : ℕ) (_ : d ∈ Finset.Ioc 0 N) :
      N * (Λ d / d) ≤ (N / d : ℕ) * Λ d + Λ d := by
    have f := Nat.lt_floor_add_one ((N : ℝ) / d)
    rw [Nat.floor_div_natCast, Nat.floor_natCast] at f
    calc
      (N : ℝ) * (Λ d / d) = ((N : ℝ) / d) * Λ d := by ring
      _ ≤ (((N / d : ℕ) : ℝ) + 1) * Λ d :=
          mul_le_mul_of_nonneg_right f.le ArithmeticFunction.vonMangoldt_nonneg
      _ = (N / d : ℕ) * Λ d + Λ d := by ring
  have h := Finset.sum_le_sum summand
  rw [← Finset.mul_sum, Finset.sum_add_distrib, floor_weight] at h
  have logs : (∑ m ∈ Finset.Ioc 0 N, Real.log m) ≤ N * Real.log N := by
    calc
      _ ≤ ∑ _m ∈ Finset.Ioc 0 N, Real.log N := by
        apply Finset.sum_le_sum
        intro m hm
        exact Real.log_le_log (by exact_mod_cast (Finset.mem_Ioc.mp hm).1)
          (by exact_mod_cast (Finset.mem_Ioc.mp hm).2)
      _ = N * Real.log N := by simp
  have cheb := Chebyshev.psi_le_const_mul_self npos.le
  simp only [Chebyshev.psi, Nat.floor_natCast] at cheb
  apply (mul_le_mul_iff_right₀ npos).mp
  linarith only [h, logs, cheb]

/-- Elementary one-sided Lipschitz rise bound `rampG y - rampG x ≤ 8 * (y - x)` for `1 ≤ x ≤ y`. -/
theorem rampG_rise {x y : ℝ} (one : 1 ≤ x) (xy : x ≤ y) :
    IndependentLandau.rampG y - IndependentLandau.rampG x ≤ 8 * (y - x) := by
  have oneY := one.trans xy
  have xp : 0 < x := zero_lt_one.trans_le one
  have yp := xp.trans_le xy
  let N := ⌊y⌋₊
  have np : 0 < N := Nat.floor_pos.mpr oneY
  have Nle : (N : ℝ) ≤ y := Nat.floor_le yp.le
  have H : IndependentLandau.rampS y - IndependentLandau.rampS x ≤
      (y - x) * (∑ d ∈ Finset.Ioc 0 N, Λ d / d) := by
    rw [rampS_on_range (u := y) le_rfl, rampS_on_range (Nat.floor_mono xy)]
    rw [← Finset.sum_sub_distrib, Nat.range_succ_eq_Icc_zero, ← Finset.Ioc_insert_left (Nat.zero_le N)]
    simp only [Finset.sum_insert (show 0 ∉ Finset.Ioc 0 N by simp),
      IndependentLandau.rampT_zero, sub_self, zero_add]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    have dp : 0 < (d : ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hd).1
    have mx := max_sub_max_le_max (y / d - 1) (0 : ℝ) (x / d - 1) 0
    have val : 0 ≤ (y - x) / d := div_nonneg (sub_nonneg.mpr xy) dp.le
    rw [show y / d - 1 - (x / d - 1) = (y - x) / d by ring, sub_self, max_eq_left val] at mx
    calc
      IndependentLandau.rampT d y - IndependentLandau.rampT d x
          = Λ d * (max (y / d - 1) 0 - max (x / d - 1) 0) := by unfold IndependentLandau.rampT; ring
      _ ≤ Λ d * ((y - x) / d) := mul_le_mul_of_nonneg_left mx ArithmeticFunction.vonMangoldt_nonneg
      _ = (y - x) * (Λ d / d) := by ring
  have recN := reciprocal_mass N np
  have ly := Real.log_le_log (by exact_mod_cast np) Nle
  have M : (∑ d ∈ Finset.Ioc 0 N, Λ d / d) ≤ Real.log y + (Real.log 4 + 4) := by
    linarith only [recN, ly]
  have bound := H.trans (mul_le_mul_of_nonneg_left M (sub_nonneg.mpr xy))
  have logPart := mul_le_mul_of_nonneg_left (Real.log_le_log xp xy) xp.le
  have l4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have c : Real.log 4 + 4 + (1 + Real.eulerMascheroniConstant) ≤ 8 := by
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have pay := mul_le_mul_of_nonneg_right c (sub_nonneg.mpr xy)
  simp only [IndependentLandau.rampG_eq]
  nlinarith only [bound, logPart, pay]

/-- Value bound `rampG 1 ≤ 2` (`rampG 1 = 1 + γ < 5/3 ≤ 2`). -/
lemma rampG_one_le_two : IndependentLandau.rampG 1 ≤ 2 := by
  have hfl : ⌊(1 : ℝ)⌋₊ = 1 := by norm_num
  have hS : IndependentLandau.rampS 1 = 0 := by
    simp [IndependentLandau.rampS, hfl, Finset.sum_range_succ, IndependentLandau.rampT]
  rw [IndependentLandau.rampG_eq, hS, Real.log_one]
  linarith [Real.eulerMascheroniConstant_lt_two_thirds]

/-- Elementary linear upper bound `rampG x ≤ 8 * x + 2` for all `x ≥ 1`. -/
theorem rampG_le_linear {x : ℝ} (hx : 1 ≤ x) :
    IndependentLandau.rampG x ≤ 8 * x + 2 := by
  have hrise := rampG_rise le_rfl hx
  have h1 := rampG_one_le_two
  linarith

/-- Homogeneous `x^1` upper bound `rampG x ≤ 10 * x^(1 : ℝ)` for all `x ≥ 1`. -/
lemma rampG_le_ten_rpow_one {x : ℝ} (hx : 1 ≤ x) :
    IndependentLandau.rampG x ≤ 10 * x ^ (1 : ℝ) := by
  rw [Real.rpow_one]
  linarith [rampG_le_linear hx]

/-- Power-growth absorption: if `a < b`, then `C * x^a ≤ x^b` for all sufficiently large `x ≥ 1`. -/
theorem eventual_power_absorption {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∃ W : ℝ, ∀ x ≥ W, 1 ≤ x → C * x ^ a ≤ x ^ b := by
  rcases le_or_gt C 0 with hC | hC
  · refine ⟨1, fun x _ hx1 => ?_⟩
    have hx0 : 0 < x := zero_lt_one.trans_le hx1
    exact (mul_nonpos_of_nonpos_of_nonneg hC (Real.rpow_nonneg hx0.le a)).trans
      (Real.rpow_nonneg hx0.le b)
  · have hgap : 0 < b - a := sub_pos.mpr hab
    refine ⟨max 1 (C ^ (1 / (b - a))), fun x hx hx1 => ?_⟩
    have hx0 : 0 < x := zero_lt_one.trans_le hx1
    have hCx : C ^ (1 / (b - a)) ≤ x := (le_max_right _ _).trans hx
    have hC_le : C ≤ x ^ (b - a) := by
      have hpow := Real.rpow_le_rpow (by positivity) hCx hgap.le
      rwa [← Real.rpow_mul hC.le, one_div_mul_cancel hgap.ne', Real.rpow_one] at hpow
    calc C * x ^ a ≤ x ^ (b - a) * x ^ a :=
          mul_le_mul_of_nonneg_right hC_le (Real.rpow_nonneg hx0.le a)
      _ = x ^ b := by rw [← Real.rpow_add hx0, sub_add_cancel]

/-! ### 2. Weighted Clipped Positive-Excess Mass via `IndependentLandau` -/

/-- Weighted positive part `max 0 (g u) * exp (-θ u)` in logarithmic coordinates. -/
def density (g : ℝ → ℝ) (θ u : ℝ) : ℝ := max 0 (g u) * Real.exp (-θ * u)

/-- Integral of `density g θ` over `[U, B]`. -/
def mass (g : ℝ → ℝ) (θ U B : ℝ) : ℝ := ∫ u in Icc U B, density g θ u

/-- Clipped positive excess `max 0 (g u * exp (-θ u) - c)` in logarithmic coordinates. -/
def excessDensity (g : ℝ → ℝ) (θ c u : ℝ) : ℝ :=
  max 0 (g u * Real.exp (-θ * u) - c)

/-- Integral of `excessDensity g θ c` over `[U, B]`. -/
def excessMass (g : ℝ → ℝ) (θ c U B : ℝ) : ℝ := ∫ u in Icc U B, excessDensity g θ c u

private lemma nonneg_density (g : ℝ → ℝ) (θ u : ℝ) : 0 ≤ density g θ u :=
  mul_nonneg (le_max_left _ _) (Real.exp_pos _).le

private lemma density_int {g : ℝ → ℝ} {F : ℂ → ℂ} {Z : Set ℂ}
    (p : IndependentLandau.PoleData g F Z) (θ : ℝ) {U B : ℝ} (hU : 0 ≤ U) :
    IntegrableOn (density g θ) (Icc U B) := by
  obtain ⟨C, hC⟩ := p.growth
  have env : Continuous (fun u : ℝ => C * Real.exp ((2 - θ) * u)) := by fun_prop
  refine env.continuousOn.integrableOn_Icc.mono' ?_ ?_
  · exact ((measurable_const.max p.meas).mul (by fun_prop)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall (fun u hu => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (nonneg_density g θ u)]
    have grow := hC u (hU.trans hu.1)
    have hi : max 0 (g u) ≤ C * Real.exp (2 * u) :=
      max_le ((abs_nonneg _).trans grow) ((le_abs_self _).trans grow)
    calc density g θ u ≤ C * Real.exp (2 * u) * Real.exp (-θ * u) :=
          mul_le_mul_of_nonneg_right hi (Real.exp_pos _).le
      _ = C * Real.exp ((2 - θ) * u) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

private lemma excess_le_density (g : ℝ → ℝ) (θ : ℝ) {c : ℝ} (hc : 0 ≤ c) (u : ℝ) :
    excessDensity g θ c u ≤ density g θ u := by
  apply max_le (nonneg_density _ _ _)
  have w := mul_le_mul_of_nonneg_right (le_max_right 0 (g u)) (Real.exp_pos (-θ * u)).le
  unfold density
  linarith

theorem excess_integrable_on {g : ℝ → ℝ} {F : ℂ → ℂ} {Z : Set ℂ}
    (p : IndependentLandau.PoleData g F Z) (θ : ℝ) {c U B : ℝ} (hc : 0 ≤ c) (hU : 0 ≤ U) :
    IntegrableOn (excessDensity g θ c) (Icc U B) := by
  refine (density_int p θ hU).mono' ?_ (Eventually.of_forall (fun u => ?_))
  · exact (measurable_const.max ((p.meas.mul (by fun_prop)).sub measurable_const)).aestronglyMeasurable
  · have en : 0 ≤ excessDensity g θ c u := le_max_left _ _
    rw [Real.norm_eq_abs, abs_of_nonneg en]
    exact excess_le_density g θ hc u

private lemma edge_compare {g : ℝ → ℝ} {F : ℂ → ℂ} {Z : Set ℂ}
    (p : IndependentLandau.PoleData g F Z) {θ q U A B : ℝ} (hθq : θ < q) (u0 : 0 ≤ U) (ua : U ≤ A) :
    mass g q A B ≤ Real.exp (-(q - θ) * A) * mass g θ U B := by
  have ai := density_int (B := B) p θ (u0.trans ua)
  have bi := density_int (B := B) p θ u0
  have qi := density_int (B := B) p q (u0.trans ua)
  have e (u : ℝ) : density g q u = Real.exp (-(q - θ) * u) * density g θ u := by
    unfold density
    rw [mul_left_comm, ← Real.exp_add, show -(q - θ) * u + -θ * u = -q * u by ring]
  have internal : mass g q A B ≤ Real.exp (-(q - θ) * A) * mass g θ A B := by
    unfold mass
    rw [← integral_const_mul]
    refine setIntegral_mono_on qi (ai.const_mul _) measurableSet_Icc (fun u hu => ?_)
    rw [e]
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (by nlinarith [hu.1] : -(q - θ) * u ≤ -(q - θ) * A))
      (nonneg_density g θ u)
  apply internal.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact setIntegral_mono_set bi (Eventually.of_forall (nonneg_density g θ))
    (Icc_subset_Icc_left ua).eventuallyLE

/-- A pole to the right of `θ` forces exponential positive mass on every sufficiently late `[U, (1+d)U]`. -/
theorem pole_forces_mass {g : ℝ → ℝ} {F : ℂ → ℂ} {Z : Set ℂ}
    (p : IndependentLandau.PoleData g F Z) {ρ : ℂ} (mem : ρ ∈ Z) (top : ρ.re ≤ 1) {θ d h : ℝ}
    (θ0 : 0 < θ) (β : θ < ρ.re) (hd : 0 < d) (rate : h < (1 + d) * (ρ.re - θ)) :
    ∃ U₀ : ℝ, ∀ U ≥ U₀, Real.exp (h * U) < mass g θ U ((1 + d) * U) := by
  let r := 1 + d
  have r1 : 1 < r := by dsimp [r]; linarith
  have rp : 0 < r := by linarith
  have hβ : h / r < ρ.re - θ := (div_lt_iff₀ rp).mpr (by simpa only [mul_comm] using rate)
  let l := max θ (θ + h / r)
  have lβ : l < ρ.re := max_lt β (by linarith)
  obtain ⟨q, lq, qβ⟩ := exists_between lβ
  have θq : θ < q := (le_max_left _ _).trans_lt lq
  have hpq : h < (q - θ) * r := (div_lt_iff₀ rp).mp (by linarith [(le_max_right θ (θ + h / r)).trans_lt lq])
  have qp : 0 < q - θ := sub_pos.mpr θq
  have hv : h / (q - θ) < r := (div_lt_iff₀ qp).mpr (by linarith only [hpq, show (q - θ) * r = r * (q - θ) by ring])
  obtain ⟨s, ls, sr⟩ := exists_between (max_lt r1 hv)
  have s1 : 1 < s := (le_max_left _ _).trans_lt ls
  have sp : 0 < s := by linarith
  have gap : h < s * (q - θ) := (div_lt_iff₀ qp).mp ((le_max_right _ _).trans_lt ls)
  let d' := r / s - 1
  have d0 : 0 < d' := sub_pos.mpr ((one_lt_div sp).mpr sr)
  have back (U : ℝ) : (1 + d') * (s * U) = r * U := by dsimp [d']; field_simp; ring
  by_contra! bad
  have win : IndependentLandau.WindowHypU g q d' := by
    intro ε ε0 M
    obtain ⟨U, hu, sm⟩ := bad (max 0 M)
    have u0 := (le_max_left 0 M).trans hu
    have su : U ≤ s * U := le_mul_of_one_le_left u0 s1.le
    refine ⟨s * U, ((le_max_right _ _).trans hu).trans su, fun u => max 0 (g u), ?_, ?_, ?_⟩
    · exact density_int p q (u0.trans su)
    · exact fun u _ => ⟨le_max_left _ _, le_max_right _ _⟩
    · change mass g q (s * U) ((1 + d') * (s * U)) ≤ _
      rw [back]
      have bound := edge_compare p θq u0 su (B := r * U)
      calc
        _ ≤ Real.exp (-(q - θ) * (s * U)) * Real.exp (h * U) :=
          bound.trans (mul_le_mul_of_nonneg_left sm (Real.exp_pos _).le)
        _ ≤ 1 := by
          rw [← Real.exp_add]
          apply Real.exp_le_one_iff.mpr
          nlinarith only [mul_nonneg (sub_nonneg.mpr gap.le) u0]
        _ ≤ Real.exp (ε * (s * U)) := Real.one_le_exp (mul_nonneg ε0.le (u0.trans su))
  exact (not_le_of_gt qβ)
    (IndependentLandau.landau_window p (θ0.trans θq) (qβ.trans_le top) d0 win ρ mem)

private lemma compare_excess {g : ℝ → ℝ} {F : ℂ → ℂ} {Z : Set ℂ}
    (p : IndependentLandau.PoleData g F Z) (θ : ℝ) {c U B : ℝ}
    (hc : 0 ≤ c) (u0 : 0 ≤ U) (ub : U ≤ B) :
    mass g θ U B ≤ excessMass g θ c U B + c * (B - U) := by
  have ce : IntegrableOn (fun _ : ℝ => c) (Icc U B) := continuousOn_const.integrableOn_Icc
  have ee := excess_integrable_on (B := B) p θ hc u0
  have h (u : ℝ) : density g θ u ≤ excessDensity g θ c u + c := by
    rcases le_total (g u) 0 with sm | sm
    · unfold density
      rw [max_eq_left sm, zero_mul]
      exact add_nonneg (le_max_left _ _) hc
    · unfold density excessDensity
      rw [max_eq_right sm]
      linarith only [le_max_right 0 (g u * Real.exp (-θ * u) - c)]
  unfold mass excessMass
  have bd := setIntegral_mono_on (density_int (B := B) p θ u0) (ee.add ce)
    measurableSet_Icc (fun u _ => h u)
  simp only [Pi.add_apply] at bd
  rw [integral_add ee ce, setIntegral_const, Real.volume_real_Icc_of_le ub, smul_eq_mul] at bd
  simpa only [mul_comm] using bd

private lemma absorb_exp_linear {h h' : ℝ} (hh : h < h') (hp : 0 < h') (C : ℝ) :
    ∃ V : ℝ, ∀ U ≥ V, Real.exp (h * U) + C * U ≤ Real.exp (h' * U) := by
  refine ⟨max 0 (max (1 / (h' - h)) (4 * C / h' ^ 2)), fun U hU => ?_⟩
  have u0 := (le_max_left _ _).trans hU
  have top := (le_max_right _ _).trans hU
  have sep := (div_le_iff₀ (sub_pos.mpr hh)).mp ((le_max_left _ _).trans top)
  have lin := (div_le_iff₀ (sq_pos_of_pos hp)).mp ((le_max_right _ _).trans top)
  have ep : 2 ≤ Real.exp ((h' - h) * U) :=
    (by linarith [Real.exp_one_gt_d9] : (2 : ℝ) ≤ Real.exp 1).trans
      (Real.exp_le_exp.mpr (by linarith only [sep, show U * (h' - h) = (h' - h) * U by ring]))
  have sq := Real.quadratic_le_exp_of_nonneg (mul_nonneg hp.le u0)
  have lg := mul_le_mul_of_nonneg_right lin u0
  have e2 := mul_le_mul_of_nonneg_right ep (Real.exp_pos (h * U)).le
  rw [← Real.exp_add, show (h' - h) * U + h * U = h' * U by ring] at e2
  nlinarith only [e2, sq, lg, mul_nonneg hp.le u0]

/-- A pole to the right of `θ` forces exponential clipped excess mass above any cutoff `c ≥ 0`. -/
theorem pole_forces_excess {g : ℝ → ℝ} {F : ℂ → ℂ} {Z : Set ℂ}
    (p : IndependentLandau.PoleData g F Z) {ρ : ℂ} (mem : ρ ∈ Z) (top : ρ.re ≤ 1)
    {θ d h c : ℝ} (θ0 : 0 < θ) (β : θ < ρ.re) (hd : 0 < d) (hc : 0 ≤ c)
    (rate : h < (1 + d) * (ρ.re - θ)) :
    ∃ U₀ : ℝ, ∀ U ≥ U₀, Real.exp (h * U) < excessMass g θ c U ((1 + d) * U) := by
  have cap : 0 < (1 + d) * (ρ.re - θ) := mul_pos (by linarith) (sub_pos.mpr β)
  obtain ⟨h', mh, hh⟩ := exists_between (max_lt rate cap)
  obtain ⟨A, all⟩ := pole_forces_mass p mem top θ0 β hd hh
  obtain ⟨B, pay⟩ := absorb_exp_linear
    ((le_max_left _ _).trans_lt mh) ((le_max_right _ _).trans_lt mh) (c * d)
  refine ⟨max 0 (max A B), fun U hU => ?_⟩
  have pos := (le_max_left _ _).trans hU
  have uab := (le_max_right _ _).trans hU
  have cost := pay U ((le_max_right _ _).trans uab)
  have lower := all U ((le_max_left _ _).trans uab)
  have comp := compare_excess p θ hc pos (B := (1 + d) * U) (by nlinarith)
  linarith only [cost, lower, comp, show c * ((1 + d) * U - U) = (c * d) * U by ring]

/-- Lower bound on logarithmic clipped excess mass of `rampG` on `[log Y, (1+d) log Y]`. -/
theorem ordinary_excess_every_window {ρ : ℂ} {θ d h c : ℝ}
    (hz : riemannZeta ρ = 0) (θ0 : 0 < θ) (β : θ < ρ.re) (hd : 0 < d) (hc : 0 ≤ c)
    (rate : h < (1 + d) * (ρ.re - θ)) :
    ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, Y ^ h <
      excessMass (fun u => IndependentLandau.rampG (Real.exp u))
        θ c (Real.log Y) ((1 + d) * Real.log Y) := by
  have top : ρ.re ≤ 1 := le_of_not_gt (fun hi => riemannZeta_ne_zero_of_one_le_re hi.le hz)
  obtain ⟨F, p⟩ := IndependentLandau.zeta_poleData
  obtain ⟨U₀, all⟩ := pole_forces_excess p
    (show ρ ∈ IndependentLandau.zetaZeros from ⟨θ0.trans β, hz⟩) top θ0 β hd hc rate
  refine ⟨Real.exp U₀, fun Y hY => ?_⟩
  have yp := (Real.exp_pos _).trans_le hY
  have lg := (Real.le_log_iff_exp_le yp).mpr hY
  simpa only [Real.rpow_def_of_pos yp, mul_comm h (Real.log Y)] using all (Real.log Y) lg

/-- Physical `dx / x` positive-excess integral on `[Y, Y^(1+d)]`. -/
def physicalMass (θ c Y d : ℝ) : ℝ :=
  ∫ x in Icc Y (Y ^ (1 + d)), max 0 (IndependentLandau.rampG x / x ^ θ - c) / x

theorem physicalMass_eq {Y d : ℝ} (Y1 : 1 ≤ Y) (hd : 0 ≤ d) (θ c : ℝ) :
    physicalMass θ c Y d =
      excessMass (fun u => IndependentLandau.rampG (Real.exp u))
        θ c (Real.log Y) ((1 + d) * Real.log Y) := by
  let f := fun x : ℝ => max 0 (IndependentLandau.rampG x / x ^ θ - c) / x
  let U := Real.log Y
  let B := (1 + d) * Real.log Y
  have yp : 0 < Y := zero_lt_one.trans_le Y1
  have ub : U ≤ B := by
    have ul : 0 ≤ U := Real.log_nonneg Y1
    dsimp [B, U] at *; nlinarith
  have cv := integral_Icc_deriv_smul_of_deriv_nonneg (f := Real.exp) (f' := Real.exp) (g := f)
    Real.continuous_exp.continuousOn (fun u _ => Real.hasDerivAt_exp u)
    (fun u _ => (Real.exp_pos u).le) ub
  have lo : Real.exp U = Y := Real.exp_log yp
  have hi : Real.exp B = Y ^ (1 + d) := by
    rw [Real.rpow_def_of_pos yp]; congr 1; dsimp [B]; ring
  rw [lo, hi] at cv
  have pt (u : ℝ) : Real.exp u • f (Real.exp u) =
      excessDensity (fun v => IndependentLandau.rampG (Real.exp v)) θ c u := by
    have ep : (Real.exp u) ^ θ = Real.exp (θ * u) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp, mul_comm]
    dsimp [f, excessDensity]
    rw [ep, show -θ * u = -(θ * u) by ring, Real.exp_neg,
      div_eq_mul_inv (IndependentLandau.rampG (Real.exp u))]
    field_simp [(Real.exp_pos u).ne']
  change (∫ x in Icc Y (Y ^ (1 + d)), f x) =
    ∫ u in Icc U B, excessDensity (fun v => IndependentLandau.rampG (Real.exp v)) θ c u
  simpa only [pt] using cv.symm

theorem off_axis_forces_weighted_excess {ρ : ℂ} {θ d h c : ℝ}
    (hz : riemannZeta ρ = 0) (θ0 : 0 < θ) (β : θ < ρ.re) (hd : 0 < d) (hc : 0 ≤ c)
    (rate : h < (1 + d) * (ρ.re - θ)) :
    ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, Y ^ h < physicalMass θ c Y d := by
  obtain ⟨Z, all⟩ := ordinary_excess_every_window hz θ0 β hd hc rate
  refine ⟨max 1 Z, fun Y hY => ?_⟩
  rw [physicalMass_eq ((le_max_left _ _).trans hY) hd.le]
  exact all Y ((le_max_right _ _).trans hY)

/-- Cofinal power bound at rate `(1 + d)(p - θ)` on `physicalMass`. -/
def cofinalUpper (θ c d p : ℝ) : Prop :=
  ∀ ε > 0, ∀ B : ℝ, ∃ Y ≥ max B 1, physicalMass θ c Y d ≤ Y ^ ((1 + d) * (p - θ) + ε)

theorem zeroFree_of_cofinalUpper {θ c d p : ℝ} (θ0 : 0 < θ) (hc : 0 ≤ c)
    (hd : 0 < d) (hp : θ ≤ p) (upper : cofinalUpper θ c d p) :
    ∀ z : ℂ, p < z.re → riemannZeta z ≠ 0 := by
  intro z hpz hz
  have gap : (1 + d) * (p - θ) < (1 + d) * (z.re - θ) :=
    mul_lt_mul_of_pos_left (by linarith) (by linarith)
  obtain ⟨h, pl, hβ⟩ := exists_between gap
  obtain ⟨M, all⟩ := off_axis_forces_weighted_excess hz θ0 (hp.trans_lt hpz) hd hc hβ
  obtain ⟨Y, hY, small⟩ := upper (h - (1 + d) * (p - θ)) (sub_pos.mpr pl) M
  rw [show (1 + d) * (p - θ) + (h - (1 + d) * (p - θ)) = h by ring] at small
  exact (not_le_of_gt (all Y ((le_max_left _ _).trans hY))) small

/-- Archive-free forward upper bound on `physicalMass` from `DirectRampEquivalence.abs_rampG_le_of_zeroFree`. -/
theorem eventually_upper_of_zeroFree {θ c d p : ℝ} (hc : 0 ≤ c) (hd : 0 < d)
    (hp : θ ≤ p) (p0 : 1 / 2 ≤ p) (p1 : p < 1)
    (zfree : ∀ z : ℂ, p < z.re → riemannZeta z ≠ 0) (ε : ℝ) (ε0 : 0 < ε) :
    ∃ M : ℝ, ∀ Y ≥ M, physicalMass θ c Y d ≤ Y ^ ((1 + d) * (p - θ) + ε) := by
  let r := 1 + d
  have rp : 0 < r := by dsimp [r]; linarith
  have cap : p < min 1 (p + ε / r) := lt_min p1 (lt_add_of_pos_right _ (div_pos ε0 rp))
  obtain ⟨q, pq, qc⟩ := exists_between cap
  have q1 : q < 1 := qc.trans_le (min_le_left _ _)
  have qθ := hp.trans_lt pq
  obtain ⟨A, A0_pos, all⟩ := DirectRampEquivalence.abs_rampG_le_of_zeroFree p0 pq q1 zfree
  have A0 : 0 ≤ A := A0_pos.le
  let low := r * (q - θ)
  let high := r * (p - θ) + ε
  have lh : low < high := by
    have fact : q - p < ε / r := by linarith [qc.trans_le (min_le_right 1 (p + ε / r))]
    have v := (lt_div_iff₀ rp).mp fact
    dsimp [low, high]; nlinarith
  let gap := high - low
  have gp : 0 < gap := sub_pos.mpr lh
  let T := max 0 (2 * (A * d) / gap ^ 2)
  refine ⟨Real.exp T, fun Y hY => ?_⟩
  have y1 : 1 ≤ Y := (Real.one_le_exp (le_max_left _ _)).trans hY
  have yp : 0 < Y := zero_lt_one.trans_le y1
  let U := Real.log Y
  have tu : T ≤ U := (Real.le_log_iff_exp_le yp).mpr hY
  have u0 := (le_max_left _ _).trans tu
  have ur : U ≤ r * U := by dsimp [r]; nlinarith
  obtain ⟨_, pD⟩ := IndependentLandau.zeta_poleData
  have int := excess_integrable_on (B := r * U) pD θ hc u0
  have bound (u : ℝ) (mem : u ∈ Icc U (r * U)) :
      excessDensity (fun u => IndependentLandau.rampG (Real.exp u)) θ c u ≤ A * Real.exp (low * U) := by
    have u0' := u0.trans mem.1
    have rise := all (Real.exp u) (Real.one_le_exp u0')
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm u q] at rise
    have pg := mul_le_mul_of_nonneg_right ((le_abs_self _).trans rise) (Real.exp_pos (-θ * u)).le
    have ex : Real.exp (q * u) * Real.exp (-θ * u) = Real.exp ((q - θ) * u) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [mul_assoc, ex] at pg
    have base := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left mem.2 (sub_nonneg.mpr qθ.le))) A0
    have eq : (q - θ) * (r * U) = low * U := by dsimp [low]; ring
    rw [eq] at base
    exact max_le (mul_nonneg A0 (Real.exp_pos _).le) (by linarith only [pg, base, hc])
  have env : IntegrableOn (fun _ : ℝ => A * Real.exp (low * U)) (Icc U (r * U)) :=
    continuousOn_const.integrableOn_Icc
  have upper := setIntegral_mono_on int env measurableSet_Icc bound
  rw [setIntegral_const, Real.volume_real_Icc_of_le ur, smul_eq_mul] at upper
  have scale : A * d * U ≤ Real.exp (gap * U) := by
    have v := (div_le_iff₀ (sq_pos_of_pos gp)).mp ((le_max_right _ _).trans tu)
    have t := mul_le_mul_of_nonneg_right v u0
    have e := Real.quadratic_le_exp_of_nonneg (mul_nonneg gp.le u0)
    nlinarith only [t, e, mul_nonneg gp.le u0]
  rw [physicalMass_eq y1 hd.le, Real.rpow_def_of_pos yp]
  change excessMass (fun u => IndependentLandau.rampG (Real.exp u)) θ c U (r * U) ≤
    Real.exp (U * high)
  calc _ ≤ (r * U - U) * (A * Real.exp (low * U)) := upper
    _ = (A * d * U) * Real.exp (low * U) := by dsimp [r]; ring
    _ ≤ Real.exp (gap * U) * Real.exp (low * U) :=
        mul_le_mul_of_nonneg_right scale (Real.exp_pos _).le
    _ = Real.exp (U * high) := by rw [← Real.exp_add]; congr 1; dsimp [gap]; ring

/-- Archive-free two-way positive-excess mass equivalence (`cofinalUpper θ c d p ↔ ZeroFree p`). -/
theorem cofinalUpper_iff_zeroFree {θ c d p : ℝ} (θ0 : 0 < θ) (hc : 0 ≤ c) (hd : 0 < d)
    (hp : θ ≤ p) (p0 : 1 / 2 ≤ p) (p1 : p < 1) :
    cofinalUpper θ c d p ↔ ∀ z : ℂ, p < z.re → riemannZeta z ≠ 0 := by
  refine ⟨zeroFree_of_cofinalUpper θ0 hc hd hp, ?_⟩
  intro zf ε ε0 B
  obtain ⟨M, all⟩ := eventually_upper_of_zeroFree hc hd hp p0 p1 zf ε ε0
  exact ⟨max (max B 1) M, le_max_left _ _, all _ (le_max_right _ _)⟩

/-! ### 3. Archive-Free Exceptional-Measure Lower Bound & Subfull-Measure Converse -/

/-- Exceptional set of real points `x ∈ [Y, Y^(1+d)]` exceeding `c * x^θ`. -/
def badSet (θ c Y d : ℝ) : Set ℝ :=
  {x ∈ Set.Icc Y (Y ^ (1 + d)) | c * x ^ θ < IndependentLandau.rampG x}

/-- Real Lebesgue measure of `badSet θ c Y d`. -/
def badSize (θ c Y d : ℝ) : ℝ := MeasureTheory.volume.real (badSet θ c Y d)

private lemma badSet_eq_inter (θ c Y d : ℝ) :
    badSet θ c Y d = Set.Icc Y (Y ^ (1 + d)) ∩ {x | c * x ^ θ < IndependentLandau.rampG x} := by
  ext x; rfl

private lemma above_measurable (θ c : ℝ) :
    MeasurableSet {x : ℝ | c * x ^ θ < IndependentLandau.rampG x} :=
  measurableSet_lt (by fun_prop) IndependentLandau.measurable_rampG

private lemma badSet_measurable (θ c Y d : ℝ) : MeasurableSet (badSet θ c Y d) := by
  rw [badSet_eq_inter]
  exact measurableSet_Icc.inter (above_measurable θ c)

private lemma badSet_volume_ne_top (θ c Y d : ℝ) :
    MeasureTheory.volume (badSet θ c Y d) ≠ ⊤ := by
  rw [badSet_eq_inter]
  exact ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono inter_subset_left)

private lemma mass_le_badSize {θ c Y d q A : ℝ} (y1 : 1 ≤ Y) (hc : 0 ≤ c)
    (hq : θ ≤ q) (A0 : 0 ≤ A) (hA : ∀ x : ℝ, 1 ≤ x → IndependentLandau.rampG x ≤ A * x ^ q) :
    physicalMass θ c Y d ≤ A * Y ^ ((1 + d) * (q - θ) - 1) * badSize θ c Y d := by
  let E := {x : ℝ | c * x ^ θ < IndependentLandau.rampG x}
  let f := fun x : ℝ => max 0 (IndependentLandau.rampG x / x ^ θ - c) / x
  have yp : 0 < Y := zero_lt_one.trans_le y1
  have em : MeasurableSet E := above_measurable θ c
  have bm : MeasurableSet (badSet θ c Y d) := badSet_measurable θ c Y d
  have fmeas : Measurable f := by
    dsimp [f]
    exact (measurable_const.max
      ((IndependentLandau.measurable_rampG.div (by fun_prop)).sub measurable_const)).div measurable_id
  have id_int : physicalMass θ c Y d = ∫ x in badSet θ c Y d, f x := by
    rw [badSet_eq_inter]
    change (∫ x in Icc Y (Y ^ (1 + d)), f x) = ∫ x in Icc Y (Y ^ (1 + d)) ∩ E, f x
    rw [← setIntegral_indicator em]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    by_cases active : x ∈ E
    · simp [Set.indicator_of_mem active]
    · rw [Set.indicator_of_notMem active]
      have xp : 0 < x := yp.trans_le hx.1
      have not_gt : IndependentLandau.rampG x ≤ c * x ^ θ := le_of_not_gt active
      have ratio := (div_le_iff₀ (Real.rpow_pos_of_pos xp θ)).mpr not_gt
      simp [f, max_eq_left (sub_nonpos.mpr ratio)]
  let D := A * Y ^ ((1 + d) * (q - θ) - 1)
  have bnd (x : ℝ) (hx : x ∈ badSet θ c Y d) : 0 ≤ f x ∧ f x ≤ D := by
    have xp := yp.trans_le hx.1.1
    have x1 := y1.trans hx.1.1
    have xθ := Real.rpow_pos_of_pos xp θ
    have rat : IndependentLandau.rampG x / x ^ θ ≤ A * x ^ (q - θ) := by
      apply (div_le_iff₀ xθ).mpr
      rw [mul_assoc, ← Real.rpow_add xp, sub_add_cancel]
      exact hA x x1
    have r0 : 0 ≤ A * x ^ (q - θ) := mul_nonneg A0 (Real.rpow_nonneg xp.le _)
    have rect : max 0 (IndependentLandau.rampG x / x ^ θ - c) ≤ A * x ^ (q - θ) :=
      max_le r0 (by linarith only [rat, hc])
    have xy := Real.rpow_le_rpow xp.le hx.1.2 (sub_nonneg.mpr hq)
    rw [← Real.rpow_mul yp.le] at xy
    have divY : (A * Y ^ ((1 + d) * (q - θ))) / Y = D := by
      unfold D
      rw [Real.rpow_sub yp, Real.rpow_one]
      ring
    refine ⟨div_nonneg (le_max_left _ _) xp.le, ?_⟩
    calc f x ≤ A * x ^ (q - θ) / x := div_le_div_of_nonneg_right rect xp.le
      _ ≤ A * Y ^ ((1 + d) * (q - θ)) / x :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left xy A0) xp.le
      _ ≤ A * Y ^ ((1 + d) * (q - θ)) / Y :=
          div_le_div_of_nonneg_left (mul_nonneg A0 (Real.rpow_nonneg yp.le _)) yp hx.1.1
      _ = D := divY
  have env_full : IntegrableOn (fun _ : ℝ => D) (Icc Y (Y ^ (1 + d))) :=
    continuousOn_const.integrableOn_Icc
  have env : IntegrableOn (fun _ : ℝ => D) (badSet θ c Y d) :=
    env_full.mono_set fun _ hx => hx.1
  have fi : IntegrableOn f (badSet θ c Y d) := by
    refine env.mono' fmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' bm).mpr (Eventually.of_forall (fun x hx => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (bnd x hx).1]
    exact (bnd x hx).2
  have cmp := setIntegral_mono_on fi env bm (fun x hx => (bnd x hx).2)
  rw [setIntegral_const, smul_eq_mul] at cmp
  rw [id_int]
  change (∫ x in badSet θ c Y d, f x) ≤ D * MeasureTheory.volume.real (badSet θ c Y d)
  rwa [mul_comm D]

/-- Quantitative real measure lower bound given a zero `z` and an `A * x^q` upper envelope. -/
theorem measured_from_pole_and_envelope {z : ℂ} {θ c d q A κ : ℝ}
    (hz : riemannZeta z = 0) (θ0 : 0 < θ) (zθ : θ < z.re) (c0 : 0 ≤ c) (d0 : 0 < d)
    (tq : θ ≤ q) (A0 : 0 ≤ A) (bound : ∀ x : ℝ, 1 ≤ x → IndependentLandau.rampG x ≤ A * x ^ q)
    (margin : (1 + d) * (q - z.re) < κ) :
    ∃ M : ℝ, ∀ Y ≥ M, Y ^ (1 - κ) < badSize θ c Y d := by
  let low := (1 + d) * (q - θ) - κ
  let high := (1 + d) * (z.re - θ)
  have lh : low < high := by dsimp [low, high]; nlinarith only [margin]
  obtain ⟨v, lv, vh⟩ := exists_between lh
  obtain ⟨W, pay⟩ := eventual_power_absorption lv A
  obtain ⟨T, large⟩ := off_axis_forces_weighted_excess hz θ0 zθ d0 c0 vh
  refine ⟨max 1 (max W T), fun Y hY => ?_⟩
  have y1 := (le_max_left _ _).trans hY
  have top := (le_max_right _ _).trans hY
  have yp := zero_lt_one.trans_le y1
  have earn := large Y ((le_max_right _ _).trans top)
  have cost := pay Y ((le_max_left _ _).trans top) y1
  have upper := mass_le_badSize y1 c0 tq A0 bound (d := d)
  by_contra! small
  have cmp := mul_le_mul_of_nonneg_left small
    (mul_nonneg A0 (Real.rpow_nonneg yp.le ((1 + d) * (q - θ) - 1)))
  have combine : A * Y ^ ((1 + d) * (q - θ) - 1) * Y ^ (1 - κ) = A * Y ^ low := by
    rw [mul_assoc, ← Real.rpow_add yp, show (1 + d) * (q - θ) - 1 + (1 - κ) = low by dsimp [low]; ring]
  rw [combine] at cmp
  exact (not_le_of_gt earn) (upper.trans (cmp.trans cost))

/-- Unconditional `Y^(1 - κ)` lower bound on `badSize` whenever `riemannZeta` has a zero right of `θ`. -/
theorem measure_from_rightward_zero {ρ : ℂ} {θ c d κ : ℝ}
    (hz : riemannZeta ρ = 0) (half : 1 / 2 ≤ θ) (right : θ < ρ.re)
    (c0 : 0 ≤ c) (d0 : 0 < d) (κ0 : 0 < κ) :
    ∃ M : ℝ, ∀ Y ≥ M, Y ^ (1 - κ) < badSize θ c Y d := by
  let S : Set ℝ := {b : ℝ | 1 / 2 ≤ b ∧ ∀ s : ℂ, b < s.re → riemannZeta s ≠ 0}
  have one_mem : (1 : ℝ) ∈ S := ⟨by norm_num, fun _ hs => riemannZeta_ne_zero_of_one_le_re hs.le⟩
  have ne : S.Nonempty := ⟨1, one_mem⟩
  have bdd : BddBelow S := ⟨1 / 2, fun _ h => h.1⟩
  let u := sInf S
  have u1 : u ≤ 1 := csInf_le bdd one_mem
  have edge : ρ.re ≤ u := le_csInf ne (fun b hb =>
    le_of_not_gt (fun br => hb.2 ρ br hz))
  let r := 1 + d
  have rp : 0 < r := by dsimp [r]; linarith
  let e := κ / (2 * r)
  have ep : 0 < e := div_pos κ0 (by positivity)
  have pay : r * (2 * e) = κ := by dsimp [e]; field_simp
  obtain ⟨v, mv, vu⟩ := exists_between (max_lt (right.trans_le edge) (show u - e < u by linarith))
  have θv : θ < v := (le_max_left _ _).trans_lt mv
  have close : u - e < v := (le_max_right _ _).trans_lt mv
  have nv : ¬ (∀ s : ℂ, v < s.re → riemannZeta s ≠ 0) := fun zh =>
    (not_le_of_gt vu) (csInf_le bdd (show v ∈ S from ⟨half.trans θv.le, zh⟩))
  push Not at nv
  obtain ⟨z, vz, zz⟩ := nv
  have zθ : θ < z.re := θv.trans vz
  have compare {q : ℝ} (qc : q < u + e) : r * (q - z.re) < κ := by
    rw [← pay]
    apply mul_lt_mul_of_pos_left _ rp
    linarith
  by_cases ui : u < 1
  · obtain ⟨q, uq, qm⟩ := exists_between (lt_min ui (show u < u + e by linarith))
    obtain ⟨b, hb, bq⟩ := exists_lt_of_csInf_lt ne uq
    obtain ⟨A, A0_pos, all⟩ := DirectRampEquivalence.abs_rampG_le_of_zeroFree
      hb.1 bq (qm.trans_le (min_le_left _ _)) hb.2
    exact measured_from_pole_and_envelope zz (by linarith : 0 < θ) zθ c0 d0
      ((right.trans_le edge).trans uq).le A0_pos.le
      (fun x x1 => (le_abs_self _).trans (all x x1))
      (compare (qm.trans_le (min_le_right _ _)))
  · have ue : u = 1 := le_antisymm u1 (le_of_not_gt ui)
    exact measured_from_pole_and_envelope zz (by linarith : 0 < θ) zθ c0 d0
      ((right.trans_le edge).trans_le u1).le (by norm_num : (0 : ℝ) ≤ 10)
      (fun _ x1 => rampG_le_ten_rpow_one x1)
      (compare (q := 1) (by linarith))

/-- Real-measure version (`MeasureTheory.volume.real`): any zeta zero right of `θ` forces
`Y^(1 + d - ε) < volume.real {x ∈ Icc Y (Y^(1+d)) | c * x^θ < rampG x}` on every late window. -/
theorem near_full_measureReal_every_window_mathlib {ρ : ℂ} {θ c d ε : ℝ}
    (hz : riemannZeta ρ = 0) (half : 1 / 2 ≤ θ) (right : θ < ρ.re)
    (c0 : 0 ≤ c) (d0 : 0 < d) (ε0 : 0 < ε) :
    ∃ M : ℝ, ∀ Y ≥ M,
      Y ^ (1 + d - ε) <
        MeasureTheory.volume.real {x ∈ Set.Icc Y (Y ^ (1 + d)) | c * x ^ θ < IndependentLandau.rampG x} := by
  let r := 1 + d
  have r1 : 1 < r := by dsimp [r]; linarith
  obtain ⟨s, ls, sr⟩ := exists_between (max_lt r1 (show r - ε < r by linarith))
  have s1 : 1 < s := (le_max_left _ _).trans_lt ls
  have sp : 0 < s := by linarith
  have se : r - ε < s := (le_max_right _ _).trans_lt ls
  let κ := (s - (r - ε)) / (2 * s)
  have kp : 0 < κ := div_pos (sub_pos.mpr se) (by positivity)
  have sc : r - ε ≤ s * (1 - κ) := by dsimp [κ]; field_simp; nlinarith
  let d' := r / s - 1
  have d'0 : 0 < d' := sub_pos.mpr ((one_lt_div sp).mpr sr)
  obtain ⟨V, large⟩ := measure_from_rightward_zero hz half right c0 d'0 kp
  refine ⟨max 1 V, fun Y hY => ?_⟩
  have Y1 := (le_max_left _ _).trans hY
  have yp := zero_lt_one.trans_le Y1
  have YS : Y ≤ Y ^ s := by
    calc Y = Y ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ Y ^ s := Real.rpow_le_rpow_of_exponent_le Y1 s1.le
  have inner := large (Y ^ s) (((le_max_right _ _).trans hY).trans YS)
  have equiv : (Y ^ s) ^ (1 + d') = Y ^ r := by
    rw [← Real.rpow_mul yp.le]
    congr 1
    dsimp [d']; field_simp; ring
  have incl : badSet θ c (Y ^ s) d' ⊆ badSet θ c Y d := by
    intro x hx
    have bounds := hx.1
    rw [equiv] at bounds
    exact ⟨⟨YS.trans bounds.1, bounds.2⟩, hx.2⟩
  calc
    Y ^ (1 + d - ε) ≤ Y ^ (s * (1 - κ)) := Real.rpow_le_rpow_of_exponent_le Y1 sc
    _ = (Y ^ s) ^ (1 - κ) := Real.rpow_mul yp.le _ _
    _ < badSize θ c (Y ^ s) d' := inner
    _ ≤ MeasureTheory.volume.real {x ∈ Set.Icc Y (Y ^ (1 + d)) | c * x ^ θ < IndependentLandau.rampG x} :=
        measureReal_mono incl (badSet_volume_ne_top θ c Y d)

/-- **Near-Full Exceptional Measure (`near_full_measure_every_window_mathlib`):**
If `1 / 2 ≤ θ < 1`, `0 ≤ c`, `0 < d`, and `∃ ρ : ℂ, θ < ρ.re ∧ riemannZeta ρ = 0`, then for
every `ε > 0` and all sufficiently large `Y : ℝ`,
`ENNReal.ofReal (Y ^ (1 + d - ε)) < volume {x ∈ Set.Icc Y (Y ^ (1 + d)) | c * x ^ θ < rampG x}`. -/
theorem near_full_measure_every_window_mathlib {θ c d : ℝ}
    (hθ_lo : 1 / 2 ≤ θ) (_hθ_hi : θ < 1) (hc : 0 ≤ c) (hd : 0 < d)
    (hzero : ∃ ρ : ℂ, θ < ρ.re ∧ riemannZeta ρ = 0) :
    ∀ ε > 0, ∀ᶠ Y : ℝ in atTop,
      ENNReal.ofReal (Y ^ (1 + d - ε)) <
        MeasureTheory.volume {x ∈ Set.Icc Y (Y ^ (1 + d)) | c * x ^ θ < IndependentLandau.rampG x} := by
  obtain ⟨ρ, hρ_re, hρ_zero⟩ := hzero
  intro ε hε
  obtain ⟨M, hM⟩ := near_full_measureReal_every_window_mathlib hρ_zero hθ_lo hρ_re hc hd hε
  filter_upwards [eventually_ge_atTop (max 1 M)] with Y hY
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYM : M ≤ Y := (le_max_right _ _).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hlt := hM Y hYM
  rw [MeasureTheory.measureReal_def] at hlt
  have hpos_toReal : 0 < (MeasureTheory.volume
      {x ∈ Set.Icc Y (Y ^ (1 + d)) | c * x ^ θ < IndependentLandau.rampG x}).toReal :=
    (Real.rpow_nonneg hYp.le _).trans_lt hlt
  have hfin : MeasureTheory.volume
      {x ∈ Set.Icc Y (Y ^ (1 + d)) | c * x ^ θ < IndependentLandau.rampG x} ≠ ⊤ :=
    badSet_volume_ne_top θ c Y d
  calc ENNReal.ofReal (Y ^ (1 + d - ε))
      < ENNReal.ofReal ((MeasureTheory.volume
          {x ∈ Set.Icc Y (Y ^ (1 + d)) | c * x ^ θ < IndependentLandau.rampG x}).toReal) :=
        (ENNReal.ofReal_lt_ofReal_iff hpos_toReal).mpr hlt
    _ = MeasureTheory.volume
          {x ∈ Set.Icc Y (Y ^ (1 + d)) | c * x ^ θ < IndependentLandau.rampG x} :=
        ENNReal.ofReal_toReal hfin

/-- General-`d` subfull-measure converse: a power saving `≤ Y^(1 + d - ε)` in the bad measure on
cofinally many `[Y, Y^(1+d)]` blocks rules out all zeta zeros in `Re s > θ`. -/
theorem zeroFree_of_subfull_bad_measure_general {θ c d ε : ℝ}
    (hθ_lo : 1 / 2 ≤ θ) (hc : 0 ≤ c) (hd : 0 < d) (hε : 0 < ε)
    (hsub : ∀ Y₀ : ℝ, ∃ Y ≥ Y₀,
      MeasureTheory.volume
        {x ∈ Set.Icc Y (Y ^ (1 + d)) | c * x ^ θ < IndependentLandau.rampG x} ≤
          ENNReal.ofReal (Y ^ (1 + d - ε))) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 := by
  intro s hs hz
  have hs1 : s.re ≤ 1 := le_of_not_gt (fun hgt => riemannZeta_ne_zero_of_one_le_re hgt.le hz)
  have hθ_hi : θ < 1 := hs.trans_le hs1
  have hev := near_full_measure_every_window_mathlib hθ_lo hθ_hi hc hd ⟨s, hs, hz⟩ ε hε
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨Y, hY_ge, hle⟩ := hsub Y₀
  exact (not_le_of_gt (hY₀ Y hY_ge)) hle

/-- **Subfull Exceptional-Measure Converse (`zeroFree_of_subfull_bad_measure`):**
If `1 / 2 ≤ θ`, `0 ≤ c`, `0 < ε`, and on cofinally many `[Y, Y^(3/2)]` windows the physical
Lebesgue measure of `{x ∈ Set.Icc Y (Y ^ (3 / 2 : ℝ)) | c * x ^ θ < rampG x}` is at most
`ENNReal.ofReal (Y ^ (3 / 2 - ε))`, then `riemannZeta s ≠ 0` for all `s` with `θ < s.re`. -/
theorem zeroFree_of_subfull_bad_measure {θ c ε : ℝ}
    (hθ_lo : 1 / 2 ≤ θ) (hc : 0 ≤ c) (hε : 0 < ε)
    (hsub : ∀ Y₀ : ℝ, ∃ Y ≥ Y₀,
      MeasureTheory.volume
        {x ∈ Set.Icc Y (Y ^ (3 / 2 : ℝ)) | c * x ^ θ < IndependentLandau.rampG x} ≤
          ENNReal.ofReal (Y ^ (3 / 2 - ε))) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 := by
  refine zeroFree_of_subfull_bad_measure_general hθ_lo hc (by norm_num : (0 : ℝ) < 1 / 2) hε ?_
  intro Y₀
  obtain ⟨Y, hY, hle⟩ := hsub Y₀
  refine ⟨Y, hY, ?_⟩
  have h1 : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
  rwa [h1]

end ArchiveFreeBadMeasure

export ArchiveFreeBadMeasure (
  rampG_rise
  rampG_le_linear
  eventual_power_absorption
  cofinalUpper_iff_zeroFree
  near_full_measureReal_every_window_mathlib
  near_full_measure_every_window_mathlib
  zeroFree_of_subfull_bad_measure_general
  zeroFree_of_subfull_bad_measure
)

#print axioms near_full_measure_every_window_mathlib
#print axioms zeroFree_of_subfull_bad_measure
